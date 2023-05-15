use crate::codegen::{ir::*, register::*};
use std::collections::HashMap;

// gets IR with virtual registers as input and fills them in with physical registers
// using linear scan; spilling when no more registers are free
pub struct RegisterAllocation {
    live_intervals: HashMap<usize, (usize, Option<TempKind>)>,
    registers: ScratchRegisters,
}

impl RegisterAllocation {
    pub fn new(live_intervals: HashMap<usize, (usize, Option<TempKind>)>) -> Self {
        RegisterAllocation {
            live_intervals,
            registers: ScratchRegisters::new(),
        }
    }
    pub fn allocate(mut self, mut ir: Vec<Ir>) -> Vec<Ir> {
        let mut result = Vec::with_capacity(ir.len());

        for (i, mut instr) in ir.drain(..).enumerate() {
            self.expire_old_intervals(i);

            let (left, right) = instr.get_regs();
            self.alloc(left);
            self.alloc(right);

            if let Ir::Call(..) = instr {
                let saved = self.save_regs(&mut result);
                result.push(instr);
                self.restore_regs(&mut result, saved);
            } else {
                result.push(instr);
            }
        }
        result
    }
    pub fn alloc(&mut self, reg: Option<&mut Register>) {
        // only needs to fill in virtual registers whose interval doesn't have a register assigned to it
        if let Some(Register::Temp(reg)) = reg {
            match self.live_intervals.get_mut(&reg.id) {
                Some((.., Some(entry))) => reg.reg = Some(entry.clone()),
                Some((.., entry @ None)) => {
                    if let Some(scratch) = self.registers.alloc() {
                        // assign interval-register
                        *entry = Some(TempKind::Scratch(
                            self.registers.0.get(scratch).unwrap().clone(),
                        ));
                        // assign instruction register
                        reg.reg = Some(TempKind::Scratch(
                            self.registers.0.get(scratch).unwrap().clone(),
                        ));
                    } else {
                        // spill
                        unimplemented!("spilling")
                    }
                }
                _ => unreachable!(),
            }
        }
    }
    fn expire_old_intervals(&mut self, instr_idx: usize) {
        // marks freed interval-registers as available again
        for (.., reg) in self
            .live_intervals
            .values()
            .filter(|(end, _)| *end == instr_idx)
        {
            if let Some(TempKind::Scratch(reg)) = reg {
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
