use crate::codegen::{ir::*, register::*};
use crate::common::environment::*;
use std::collections::HashMap;

// gets IR with virtual registers as input and fills them in with physical registers
// using linear scan; spilling when no more registers are free
pub struct RegisterAllocation {
    live_intervals: HashMap<usize, (usize, Option<TempRegister>)>,
    registers: ScratchRegisters,
    spill_index: usize,

    // offset from base-pointer; spilled variables stay after local-variable stack-locations
    spill_bp_offset: usize,

    env: Vec<Symbols>,
    counter: usize,
}

impl RegisterAllocation {
    pub fn new(
        env: Vec<Symbols>,
        live_intervals: HashMap<usize, (usize, Option<TempRegister>)>,
    ) -> Self {
        RegisterAllocation {
            live_intervals,
            env,
            counter: 0,
            spill_bp_offset: 0,
            spill_index: 0,
            registers: ScratchRegisters::new(),
        }
    }
    pub fn allocate(mut self, mut ir: Vec<Ir>) -> Vec<Ir> {
        let mut result = Vec::with_capacity(ir.len());

        for (i, mut instr) in ir.drain(..).enumerate() {
            self.expire_old_intervals(i);
            self.counter = i;

            match instr.get_regs() {
                (Some(Register::Temp(left)), Some(Register::Temp(right))) => {
                    self.alloc(left, self.get_reg(right.id), &mut result);
                    self.alloc(right, self.get_reg(left.id), &mut result);
                }
                (Some(Register::Temp(reg)), _) | (_, Some(Register::Temp(reg))) => {
                    self.alloc(reg, None, &mut result);
                }
                _ => (),
            }
            // let (left, right) = instr.get_regs();

            match &instr {
                Ir::Call(..) => {
                    let saved = self.save_regs(&mut result);
                    result.push(instr);
                    self.restore_regs(&mut result, saved);
                }
                Ir::FuncSetup(name) => {
                    self.spill_bp_offset = self
                        .env
                        .get_mut(name.token.get_index())
                        .unwrap()
                        .unwrap_func()
                        .stack_size;
                    result.push(instr);
                }
                _ => result.push(instr),
            }
        }
        result
    }
    #[rustfmt::skip]
    pub fn alloc(&mut self, reg: &mut TempRegister, other: Option<usize>, ir: &mut Vec<Ir>) {
        // only needs to fill in virtual registers whose interval doesn't have a register assigned to it
        let value = match self.live_intervals.get(&reg.id) {
            Some((..,Some(scratch @ TempRegister {reg: Some(TempKind::Scratch(..)),..}))) =>{ reg.reg = scratch.reg.clone(); scratch.clone()},
            Some((..,Some(TempRegister {reg: Some(TempKind::Spilled(..)),..}))) => {
                // if current register is spilled then unspill that regiser
                let scratch = self.unspill(ir, reg.id, other);
                reg.reg = Some(scratch.clone());
                reg.clone()
            }
            Some((.., None)) => {
                // if unknown register allocate new physical register
                let scratch = self.get_scratch(ir, other);
                reg.reg = Some(scratch.clone());
                reg.clone()
            }
            _ => unreachable!(),
        };
        // assign register to interval and instruction
        self.live_intervals.get_mut(&reg.id).unwrap().1 = Some(value);

    }
    fn get_scratch(&mut self, ir: &mut Vec<Ir>, other: Option<usize>) -> TempKind {
        if let Some(scratch) = self.registers.alloc() {
            TempKind::Scratch(self.registers.0.get(scratch).unwrap().clone())
        } else {
            self.spill(ir, other)
        }
    }
    fn spill(&mut self, ir: &mut Vec<Ir>, other: Option<usize>) -> TempKind {
        let spill_reg_idx = self.heuristic(other);
        let spill_interval = self.get_interval_of_reg(spill_reg_idx);
        let Some((_,Some(entry))) = self.live_intervals.get_mut(&spill_interval) else {unreachable!()};

        let prev_reg = entry.clone();
        entry.reg = Some(TempKind::Spilled(StackRegister::new(
            &mut self.spill_bp_offset,
            entry.type_decl.clone(),
        )));

        ir.push(Ir::Mov(
            Register::Temp(prev_reg.clone()),
            Register::Temp(entry.clone()),
        ));
        prev_reg.reg.unwrap()
    }
    fn get_interval_of_reg(&self, reg: usize) -> usize {
        let active_intervals = self
            .live_intervals
            .iter()
            .filter(|(_, (end, s))| end > &&self.counter && s.is_some());

        for (key, (.., r)) in active_intervals {
            if let Some(TempRegister {
                reg: Some(TempKind::Scratch(scratch)),
                ..
            }) = r.clone()
            {
                if self.registers.0.get(reg).unwrap() == &scratch {
                    return *key;
                }
            }
        }
        unreachable!()
    }

    fn unspill(&mut self, ir: &mut Vec<Ir>, id: usize, other: Option<usize>) -> TempKind {
        let Some((.., Some(entry))) = self.live_intervals.get_mut(&id) else {unreachable!()};

        let mut entry = entry.clone(); // for borrow checker
        let prev_reg = entry.clone();
        let new = self.get_scratch(ir, other);

        entry.reg = Some(new.clone());
        ir.push(Ir::Mov(Register::Temp(prev_reg), Register::Temp(entry)));
        new
    }
    // gets the corresponding scratch-register given the interval-id to a tempregister
    fn get_reg(&self, reg_id: usize) -> Option<usize> {
        if let Some((
            ..,
            Some(TempRegister {
                reg: Some(TempKind::Scratch(r)),
                ..
            }),
        )) = self.live_intervals.get(&reg_id)
        {
            return self.registers.0.iter().position(|scratch| scratch == r);
        }
        None
    }
    // chooses which register to spill besides other
    fn heuristic(&mut self, other: Option<usize>) -> usize {
        if let Some(other) = other {
            if other == self.spill_index {
                self.spill_index = (self.spill_index + 1) % self.registers.0.len();
                return self.spill_index;
            }
        }
        let prev = self.spill_index;
        self.spill_index = (self.spill_index + 1) % self.registers.0.len();
        prev
    }
    fn expire_old_intervals(&mut self, instr_idx: usize) {
        // marks freed interval-registers as available again
        for (.., reg) in self
            .live_intervals
            .values()
            .filter(|(end, _)| *end == instr_idx)
        {
            if let Some(TempRegister {
                reg: Some(TempKind::Scratch(reg)),
                ..
            }) = reg
            {
                if let Some(scratch) = self.registers.0.iter_mut().find(|scratch| scratch == &reg) {
                    scratch.in_use = false;
                }
            }
        }
    }
    // TODO: would be nice if arguments registers would also be saved in this pass to avoid duplicate
    fn save_regs(&self, ir: &mut Vec<Ir>) -> Vec<Register> {
        let mut result = Vec::new();
        for scratch in self.registers.0.iter().filter(|r| r.in_use) {
            let reg = Register::Temp(TempRegister::default(scratch.clone()));

            ir.push(Ir::Push(reg.clone()));
            result.push(reg);
        }
        // align stack
        if !result.is_empty() && result.len() % 2 != 0 {
            ir.push(Ir::SubSp(8));
        }
        result
    }

    fn restore_regs(&self, ir: &mut Vec<Ir>, regs: Vec<Register>) {
        if !regs.is_empty() && regs.len() % 2 != 0 {
            ir.push(Ir::AddSp(8));
        }
        for reg in regs {
            ir.push(Ir::Pop(reg));
        }
    }
}
struct ScratchRegisters([ScratchRegister; 4]);
impl ScratchRegisters {
    fn alloc(&mut self) -> Option<usize> {
        for (i, r) in self.0.iter_mut().enumerate() {
            if !r.in_use {
                r.in_use = true;
                return Some(i);
            }
        }
        None
    }
    fn new() -> Self {
        ScratchRegisters([
            ScratchRegister {
                in_use: false,
                base_name: "%r8",
            },
            ScratchRegister {
                in_use: false,
                base_name: "%r9",
            },
            ScratchRegister {
                in_use: false,
                base_name: "%r10",
            },
            ScratchRegister {
                in_use: false,
                base_name: "%r11",
            },
        ])
    }
}
