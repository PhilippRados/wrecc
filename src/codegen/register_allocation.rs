use crate::codegen::{ir::*, register::*};
use crate::common::environment::*;
use crate::common::types::NEWTypes;
use std::collections::HashMap;

// gets IR with virtual registers as input and fills them in with physical registers
// using linear scan; spilling when no more registers are free
pub struct RegisterAllocation {
    live_intervals: HashMap<usize, (usize, NEWTypes, Option<TempKind>)>,

    // physical registers
    registers: ScratchRegisters,

    // index for next register to spill
    spill_index: usize,

    // offset from base-pointer; spilled variables stay after local-variable stack-locations
    spill_bp_offset: usize,

    env: Vec<Symbols>,

    // registers that are saved before function call
    saved_regs: Vec<Vec<(usize, Register)>>,

    // instruction-counter
    counter: usize,
}

impl RegisterAllocation {
    pub fn new(
        env: Vec<Symbols>,
        live_intervals: HashMap<usize, (usize, NEWTypes, Option<TempKind>)>,
    ) -> Self {
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

            // TODO: coaleascing
            // if let (Some(left), Some(right)) = instr.get_regs() {
            //     match (left, right) {
            //         (Register::Temp(left), Register::Arg(right, ..)) => {
            //             let scratch_idx = self.get_reg(left.id);
            //             if let Some(scratch_idx) = scratch_idx {
            //                 let left_name = self.registers.0.get(scratch_idx).unwrap().base_name();
            //                 if left_name == right.base_name() {
            //                     continue;
            //                 }
            //             }
            //         }
            //         _ => (),
            //     }
            // }

            match instr.get_regs() {
                (Some(Register::Arg(reg, _, id)), _) | (_, Some(Register::Arg(reg, _, id))) => {
                    self.alloc_arg(reg, *id, &mut result);
                }
                _ => (),
            }
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
                Ir::Occ(..) => (),
                _ => result.push(instr),
            }
        }
        result
    }
    // when explictily allocating arg-register then when arg-register is occupied the occupant gets pushed
    // exlicit arg-registers always have priority
    fn alloc_arg(&mut self, reg: &mut ArgRegister, id: usize, result: &mut Vec<Ir>) {
        if let Some((scratch_idx, scratch)) = self
            .registers
            .0
            .iter_mut()
            .enumerate()
            .find(|(_, s)| s.base_name() == reg.base_name())
        {
            match (self.live_intervals.get_mut(&id), scratch.is_used()) {
                (Some((.., interval_reg @ None)), false) => {
                    *interval_reg = Some(TempKind::Scratch(scratch.clone()));
                    scratch.in_use()
                }
                (Some((.., None)), true) => {
                    let scratch = scratch.clone();
                    let occupied_reg = Register::Temp(TempRegister::default(scratch.clone()));
                    result.push(Ir::Push(occupied_reg));

                    let key = self.get_interval_of_reg(scratch_idx);

                    // mark occupant as pushed
                    self.live_intervals.get_mut(&key).unwrap().2 = Some(TempKind::Pushed(id));
                    self.live_intervals.get_mut(&id).unwrap().2 = Some(TempKind::Scratch(scratch));
                }
                _ => (),
            }
        }
    }
    fn alloc(&mut self, reg: &mut TempRegister, other: Option<usize>, ir: &mut Vec<Ir>) {
        // only needs to fill in virtual registers whose interval doesn't have a register assigned to it
        let value = match self.live_intervals.get(&reg.id) {
            Some((.., Some(scratch @ TempKind::Scratch(..)))) => {
                reg.reg = Some(scratch.clone());
                scratch.clone()
            }
            Some((.., Some(TempKind::Spilled(..)))) => {
                // if current register is spilled then unspill it and spill another register
                let scratch = self.unspill(ir, reg, other);
                reg.reg = Some(scratch.clone());
                scratch
            }
            Some((.., None)) => {
                // if unknown register allocate new physical register
                let scratch = self.get_scratch(ir, reg, other);
                reg.reg = Some(scratch.clone());
                scratch
            }
            Some((.., Some(TempKind::Pushed(link_key)))) => {
                // TODO: remove this case
                // should only happen when arg-register is used as scratch and scratch still holds value for arg-operation
                // => need to move value out of arg-reg when it gets pushed
                let TempKind::Scratch(scratch_reg) = self
                    .live_intervals
                    .get(&link_key)
                    .unwrap()
                    .2
                    .clone()
                    .unwrap() else {unreachable!()};
                ir.push(Ir::Pop(Register::Temp(TempRegister::default(
                    scratch_reg.clone(),
                ))));

                let scratch_reg = TempKind::Scratch(scratch_reg);
                self.live_intervals.get_mut(&reg.id).unwrap().2 = Some(scratch_reg.clone());

                reg.reg = Some(scratch_reg.clone());
                scratch_reg
            }
            _ => unreachable!(),
        };
        // assign register to the interval
        self.live_intervals.get_mut(&reg.id).unwrap().2 = Some(value);
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
        let Some((_,type_decl,Some(entry))) = self.live_intervals.get_mut(&spill_interval) else {unreachable!()};

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
        let Some((..,type_decl, Some(entry))) = self.live_intervals.get_mut(&reg.id) else {unreachable!()};

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
        if let Some((.., Some(TempKind::Scratch(r)))) = self.live_intervals.get(&reg_id) {
            return self.registers.0.iter().position(|scratch| scratch == r);
        }
        None
    }
    // gets corresponding interval-key given the index of the scratch-reg in the scratchregisters
    fn get_interval_of_reg(&self, reg_idx: usize) -> usize {
        let active_intervals: Vec<_> = self
            .live_intervals
            .iter()
            .filter(|(_, (end, _, s))| end > &&self.counter && s.is_some())
            .collect();

        let matching_scratches: Vec<_> = active_intervals
            .iter()
            .filter_map(|(key, (.., r))| match r {
                Some(TempKind::Scratch(scratch))
                    if self.registers.0.get(reg_idx).unwrap() == scratch =>
                {
                    Some(*key)
                }
                _ => None,
            })
            .collect();

        assert!(
            matching_scratches.len() == 1,
            "Can only have single matching interval per active scratch-reg, found: {}",
            matching_scratches.len()
        );

        return **matching_scratches.first().unwrap();
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
        for (key, (.., reg)) in self
            .live_intervals
            .clone()
            .iter()
            .filter(|(_, (end, ..))| *end == instr_idx)
        {
            match reg {
                Some(TempKind::Scratch(scratch)) => {
                    if let Some((.., (.., other))) =
                        self.live_intervals.iter_mut().find(|(_, (end, _, r))| {
                            if let Some(TempKind::Pushed(link_id)) = r {
                                self.counter < *end && link_id == key
                            } else {
                                false
                            }
                        })
                    {
                        result.push(Ir::Pop(Register::Temp(TempRegister::default(
                            scratch.clone(),
                        ))));
                        *other = reg.clone();
                    } else if self
                        .live_intervals
                        .values()
                        .filter(|(end, _, r)| {
                            if let Some(TempKind::Scratch(s)) = r {
                                self.counter < *end && s.base_name() == scratch.base_name()
                            } else {
                                false
                            }
                        })
                        .collect::<Vec<_>>()
                        .len()
                        > 1
                    {
                        // TODO: remove this check
                        // if there is another scratch register active right now don't free it
                        // only happens when assigning same scratch-reg to arg-register (movl  %esi,%esi)
                        ()
                    } else if let Some(scratch) =
                        self.registers.0.iter_mut().find(|s| s == &scratch)
                    {
                        scratch.free();
                    }
                }
                Some(TempKind::Pushed(..)) => {
                    unreachable!("all pushed registers should be popped back before they're freed");
                }
                _ => (),
            }
        }
    }
    fn save_regs(&mut self, ir: &mut Vec<Ir>) {
        let active_intervals: Vec<_> = self
            .registers
            .0
            .iter()
            .enumerate()
            .filter(|(_, r)| r.is_used())
            .map(|(scratch_idx, scratch)| {
                (
                    self.get_interval_of_reg(scratch_idx),
                    Register::Temp(TempRegister::default(scratch.clone())),
                )
            })
            .collect();

        for (key, reg) in active_intervals.iter() {
            ir.push(Ir::Push(reg.clone()));

            // WARN: should be fine passing 0 as interval-key since values are restored anyway before freeing regs
            self.live_intervals.get_mut(&key).unwrap().2 = Some(TempKind::Pushed(0));

            if let Some(scratch) = self
                .registers
                .0
                .iter_mut()
                .find(|s| s.base_name() == reg.base_name())
            {
                scratch.free();
            }
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
        for (key, reg) in saved.iter().rev() {
            ir.push(Ir::Pop(reg.clone()));

            if let Some(scratch) = self
                .registers
                .0
                .iter_mut()
                .find(|s| s.base_name() == reg.base_name())
            {
                scratch.in_use();
                self.live_intervals.get_mut(&key).unwrap().2 =
                    Some(TempKind::Scratch(scratch.clone()));
            }
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
struct ScratchRegisters([Box<dyn ScratchRegister>; 8]);
impl ScratchRegisters {
    fn alloc(&mut self) -> Option<usize> {
        // don't use rdx and rcx as scratch-regs because of collisions with div/shift operations
        for (i, r) in self
            .0
            .iter_mut()
            .enumerate()
            .filter(|(_, r)| !r.is_used() && !matches!(r.base_name(), "%rdx" | "%rcx"))
        {
            r.in_use();
            return Some(i);
        }
        None
    }
    fn new() -> Self {
        // sorted in descending order of occurance probability to reduce collisions
        ScratchRegisters([
            Box::new(RegularRegister::new("%r10")),
            Box::new(RegularRegister::new("%r11")),
            Box::new(ArgRegister::new(5)),
            Box::new(ArgRegister::new(4)),
            Box::new(ArgRegister::new(3)), // WARN: not used
            Box::new(ArgRegister::new(2)), // WARN: not used
            Box::new(ArgRegister::new(1)),
            Box::new(ArgRegister::new(0)),
        ])
    }
}
