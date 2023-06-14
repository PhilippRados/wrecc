use crate::codegen::{ir::*, register::*};
use crate::common::{environment::*, expr::*, types::NEWTypes};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct IntervalEntry {
    start: usize,
    end: usize,
    arg: Option<ArgRegisterKind>,
    type_decl: NEWTypes,
    scratch: Option<TempKind>,
}
impl IntervalEntry {
    pub fn new(
        start: usize,
        end: usize,
        arg: Option<ArgRegisterKind>,
        type_decl: NEWTypes,
    ) -> Self {
        IntervalEntry {
            start,
            end,
            arg,
            type_decl,
            scratch: None,
        }
    }
}

// gets IR with virtual registers as input and fills them in with physical registers
// using linear scan; spilling when no more registers are free
pub struct RegisterAllocation {
    live_intervals: HashMap<usize, IntervalEntry>,

    // physical registers
    registers: ScratchRegisters,

    // index for next register to spill
    spill_index: usize,

    // offset from base-pointer; spilled variables stay after local-variable stack-locations
    spill_bp_offset: usize,

    env: Vec<Symbols>,

    // registers that are saved before function call
    saved_regs: Vec<Vec<(usize, Box<dyn ScratchRegister>, Register)>>,

    // instruction-counter
    counter: usize,
}

impl RegisterAllocation {
    pub fn new(env: Vec<Symbols>, live_intervals: HashMap<usize, IntervalEntry>) -> Self {
        RegisterAllocation {
            live_intervals,
            env,
            saved_regs: Vec::new(),
            counter: 0,
            spill_bp_offset: 0,
            spill_index: 0,
            registers: ScratchRegisters::new(),
        }
    }
    pub fn generate(mut self, mut ir: Vec<Ir>) -> Vec<Ir> {
        let mut result = Vec::with_capacity(ir.len());

        for (i, mut instr) in ir.drain(..).enumerate() {
            self.expire_old_intervals(i, &mut result);
            self.counter = i;

            if self.is_redundant_instr(&mut instr) {
                continue;
            }

            self.alloc_arg(&mut result);

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

            match &mut instr {
                Ir::SaveRegs => {
                    self.save_regs(&mut result);
                }
                Ir::RestoreRegs => {
                    self.restore_regs(&mut result);
                }
                Ir::FuncSetup(name, ..) => {
                    // get current bp-offset so that spilled regs know where to spill
                    self.spill_bp_offset = self
                        .env
                        .get_mut(name.token.get_index())
                        .unwrap()
                        .unwrap_func()
                        .stack_size;

                    result.push(instr);
                }
                Ir::FuncTeardown(stack_size) => {
                    // when function is done update stack-size if registers where spilled to stack
                    if *stack_size != self.spill_bp_offset {
                        *stack_size = self.spill_bp_offset;
                        self.update_func_setup(&mut result);
                    }
                    result.push(instr)
                }
                _ => result.push(instr),
            }
        }
        result
    }
    // when explictily allocating arg-register then when arg-register is occupied the occupant gets pushed
    // exlicit arg-registers always have priority
    fn alloc_arg(&mut self, result: &mut Vec<Ir>) {
        // get the interval if a new arg-register has been declared
        let new_arg_interval = self.live_intervals.iter_mut().find(|(_, v)| {
            self.counter >= v.start
                && self.counter < v.end
                && v.arg.is_some()
                && v.scratch.is_none()
        });

        if let Some((key, IntervalEntry { arg: Some(scratch), .. })) = new_arg_interval {
            let key = *key;
            let scratch = scratch.clone();

            let reg_in_use = self
                .get_active_intervals()
                .into_iter()
                .find(|(_, active_reg)| active_reg.base_name() == scratch.base_name());

            if let Some((occupied_key, used_scratch)) = reg_in_use {
                // if already in use push previous value on stack
                let occupied_reg = Register::Temp(TempRegister::default(used_scratch.clone()));
                result.push(Ir::Push(occupied_reg));

                self.live_intervals.get_mut(&key).unwrap().scratch =
                    Some(TempKind::Scratch(used_scratch.clone()));

                // mark occupant as pushed
                self.live_intervals.get_mut(&occupied_key).unwrap().scratch =
                    Some(TempKind::Pushed(key));
            } else {
                self.registers.activate_reg(Box::new(scratch.clone()));

                self.live_intervals.get_mut(&key).unwrap().scratch =
                    Some(TempKind::Scratch(Box::new(scratch.clone())));
            }
        }
    }

    fn alloc(&mut self, reg: &mut TempRegister, other: Option<usize>, ir: &mut Vec<Ir>) {
        // only needs to fill in virtual registers whose interval doesn't have a register assigned to it
        let value = match self.live_intervals.get(&reg.id) {
            Some(IntervalEntry {
                scratch: Some(scratch @ TempKind::Scratch(..)),
                ..
            }) => {
                reg.reg = Some(scratch.clone());
                scratch.clone()
            }
            Some(IntervalEntry { scratch: Some(TempKind::Spilled(..)), .. }) => {
                // if current register is spilled then unspill it and spill another register
                let scratch = self.unspill(ir, reg, other);
                reg.reg = Some(scratch.clone());
                scratch
            }
            Some(IntervalEntry { scratch: None, .. }) => {
                // if unknown register allocate new physical register
                let scratch = self.get_scratch(ir, reg, other);
                reg.reg = Some(scratch.clone());
                scratch
            }
            Some(IntervalEntry {
                scratch: Some(TempKind::Pushed(link_key)),
                ..
            }) => {
                // TODO: remove this case
                // should only happen when arg-register is used as scratch and scratch still holds value for arg-operation
                // => need to move value out of arg-reg when it gets pushed
                let TempKind::Scratch(scratch_reg) = self
                    .live_intervals
                    .get(link_key)
                    .unwrap()
                    .scratch
                    .clone()
                    .unwrap() else {unreachable!()};
                ir.push(Ir::Pop(Register::Temp(TempRegister::default(
                    scratch_reg.clone(),
                ))));

                let scratch_reg = TempKind::Scratch(scratch_reg);
                self.live_intervals.get_mut(&reg.id).unwrap().scratch = Some(scratch_reg.clone());

                reg.reg = Some(scratch_reg.clone());
                scratch_reg
            }
            _ => unreachable!(),
        };
        // assign register to the interval
        self.live_intervals.get_mut(&reg.id).unwrap().scratch = Some(value);
    }
    fn get_scratch(
        &mut self,
        ir: &mut Vec<Ir>,
        reg: &mut TempRegister,
        other: Option<usize>,
    ) -> TempKind {
        if let Some(scratch) = self.registers.alloc() {
            TempKind::Scratch(self.registers.0.get(scratch).unwrap().clone())
        } else {
            self.spill(ir, reg, other)
        }
    }
    fn spill(
        &mut self,
        ir: &mut Vec<Ir>,
        reg: &mut TempRegister,
        other: Option<usize>,
    ) -> TempKind {
        // find the interval to spill
        let spill_reg_idx = self.heuristic(other);
        let spill_interval = self.get_interval_of_reg(spill_reg_idx);
        let Some(IntervalEntry{ type_decl,scratch:Some(entry),.. }) = self.live_intervals.get_mut(&spill_interval) else {unreachable!()};

        // save the current register
        let mut prev = reg.clone();
        prev.reg = Some(entry.clone());
        prev.type_decl = type_decl.clone();

        // generate the new stack-position to spill to
        let mut new = reg.clone();
        new.type_decl = type_decl.clone();
        new.reg = Some(TempKind::Spilled(StackRegister::new(
            &mut self.spill_bp_offset,
            type_decl.clone(),
        )));

        // change the interval register to the stackregister
        *entry = new.reg.clone().unwrap();

        ir.push(Ir::Mov(Register::Temp(prev.clone()), Register::Temp(new)));

        // return the now free register
        prev.reg.unwrap()
    }

    fn unspill(
        &mut self,
        ir: &mut Vec<Ir>,
        reg: &mut TempRegister,
        other: Option<usize>,
    ) -> TempKind {
        let Some(IntervalEntry{ type_decl, scratch:Some(entry),.. }) = self.live_intervals.get_mut(&reg.id) else {unreachable!()};

        let mut prev_reg = reg.clone();
        prev_reg.type_decl = type_decl.clone();
        prev_reg.reg = Some(entry.clone());

        let mut new = reg.clone();
        new.type_decl = type_decl.clone();
        new.reg = Some(self.get_scratch(ir, reg, other));

        ir.push(Ir::Mov(
            Register::Temp(prev_reg),
            Register::Temp(new.clone()),
        ));
        new.reg.unwrap()
    }
    // gets the corresponding scratch-register given the interval-id to a tempregister
    fn get_reg(&self, reg_id: usize) -> Option<usize> {
        if let Some(IntervalEntry { scratch: Some(TempKind::Scratch(r)), .. }) =
            self.live_intervals.get(&reg_id)
        {
            return self.registers.0.iter().position(|scratch| scratch == r);
        }
        None
    }
    // gets corresponding interval-key given the index of the scratch-reg in the scratchregisters
    fn get_interval_of_reg(&self, reg_idx: usize) -> usize {
        let matching_scratches: Vec<_> = self
            .get_active_intervals()
            .iter()
            .filter_map(|(key, r)| {
                if self.registers.0.get(reg_idx).unwrap() == r {
                    Some(*key)
                } else {
                    None
                }
            })
            .collect();

        assert!(
            matching_scratches.len() == 1,
            "Can only have single matching interval per active scratch-reg, found: {}",
            matching_scratches.len()
        );

        return *matching_scratches.first().unwrap();
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
    // marks freed interval-registers as available again
    fn expire_old_intervals(&mut self, instr_idx: usize, result: &mut Vec<Ir>) {
        // TODO: remove this clone
        for (key, expired_intervals) in self
            .live_intervals
            .clone()
            .iter()
            .filter(|(_, entry)| entry.end == instr_idx)
        {
            match &expired_intervals.scratch {
                Some(TempKind::Scratch(scratch)) => {
                    if let Some((.., other_interval)) =
                        self.live_intervals.iter_mut().find(|(_, entry)| {
                            if let Some(TempKind::Pushed(link_id)) = entry.scratch {
                                self.counter < entry.end && link_id == *key
                            } else {
                                false
                            }
                        })
                    {
                        // if there exists another interval where this reg is pushed, pop that instead of freeing physical
                        result.push(Ir::Pop(Register::Temp(TempRegister::default(
                            scratch.clone(),
                        ))));
                        other_interval.scratch = expired_intervals.scratch.clone();
                    } else {
                        self.registers.free_reg(scratch.clone());
                    }
                }
                Some(TempKind::Pushed(..)) => {
                    unreachable!("all pushed registers should be popped back before they're freed");
                }
                _ => (),
            }
        }
    }
    fn get_active_intervals(&self) -> Vec<(usize, Box<dyn ScratchRegister>)> {
        self.live_intervals
            .iter()
            .filter_map(|(key, entry)| {
                if let Some(TempKind::Scratch(s)) = &entry.scratch {
                    if self.counter >= entry.start && self.counter < entry.end {
                        Some((*key, s.clone()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }
    fn is_redundant_instr(&mut self, instr: &mut Ir) -> bool {
        if let (true, (Some(left), Some(right))) = (matches!(instr, Ir::Mov(..)), instr.get_regs())
        {
            if let (Register::Temp(left), Register::Arg(right)) = (left, right) {
                let scratch_idx = self.get_reg(left.id);
                if let Some(scratch_idx) = scratch_idx {
                    let left_name = self.registers.0.get(scratch_idx).unwrap().base_name();

                    return left_name == right.reg.base_name()
                        && left.value_kind == ValueKind::Rvalue;
                }
            }
        }
        false
    }
    fn save_regs(&mut self, ir: &mut Vec<Ir>) {
        let active_intervals: Vec<_> = self
            .get_active_intervals()
            .iter()
            .map(|(key, reg)| {
                (
                    *key,
                    reg.clone(),
                    Register::Temp(TempRegister::default(reg.clone())),
                )
            })
            .collect();

        for (key, scratch, reg) in active_intervals.iter() {
            ir.push(Ir::Push(reg.clone()));

            // WARN: should be fine passing 0 as interval-key since values are restored anyway before freeing regs
            self.live_intervals.get_mut(key).unwrap().scratch = Some(TempKind::Pushed(0));
            self.registers.free_reg(scratch.clone());
        }

        // align stack
        if !active_intervals.is_empty() && active_intervals.len() % 2 != 0 {
            ir.push(Ir::SubSp(8));
        }

        self.saved_regs.push(active_intervals);
    }

    fn restore_regs(&mut self, ir: &mut Vec<Ir>) {
        let saved = self.saved_regs.pop().expect("restore always after save");

        if !saved.is_empty() && saved.len() % 2 != 0 {
            ir.push(Ir::AddSp(8));
        }
        for (key, scratch, reg) in saved.iter().rev() {
            ir.push(Ir::Pop(reg.clone()));

            // mark popped registers as used again
            self.registers.activate_reg(scratch.clone());
            self.live_intervals.get_mut(key).unwrap().scratch =
                Some(TempKind::Scratch(scratch.clone()));
        }
    }
    // backtrack trough result and update allocated stack-space
    fn update_func_setup(&self, result: &mut Vec<Ir>) {
        let setup_size = result
            .iter_mut()
            .rev()
            .filter_map(|instr| {
                if let Ir::FuncSetup(.., setup_size) = instr {
                    Some(setup_size)
                } else {
                    None
                }
            })
            .nth(0)
            .unwrap();

        *setup_size = self.spill_bp_offset;
    }
}
struct ScratchRegisters([Box<dyn ScratchRegister>; 6]);
impl ScratchRegisters {
    fn alloc(&mut self) -> Option<usize> {
        for (i, r) in self.0.iter_mut().enumerate().filter(|(_, r)| !r.is_used()) {
            r.in_use();
            return Some(i);
        }
        None
    }
    fn activate_reg(&mut self, scratch: Box<dyn ScratchRegister>) {
        if let Some(scratch) = self
            .0
            .iter_mut()
            .find(|s| s.base_name() == scratch.base_name())
        {
            scratch.in_use()
        }
    }

    fn free_reg(&mut self, scratch: Box<dyn ScratchRegister>) {
        if let Some(scratch) = self
            .0
            .iter_mut()
            .find(|s| s.base_name() == scratch.base_name())
        {
            scratch.free()
        }
    }
    fn new() -> Self {
        // sorted in descending order of occurance probability to reduce collisions
        // don't use rdx and rcx as scratch-regs because of collisions with div/shift operations
        // TODO: allow using rdx and rcx
        ScratchRegisters([
            Box::new(RegularRegister::new("%r10")),
            Box::new(RegularRegister::new("%r11")),
            Box::new(ArgRegisterKind::new(5)),
            Box::new(ArgRegisterKind::new(4)),
            Box::new(ArgRegisterKind::new(1)),
            Box::new(ArgRegisterKind::new(0)),
        ])
    }
}
