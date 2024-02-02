use crate::compiler::codegen::{lir::*, register::*};
use crate::compiler::common::types::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct IntervalEntry {
    start: usize,
    end: usize,
    arg: Option<ArgRegisterKind>,
    type_decl: Type,
    scratch: Option<TempKind>,
}
impl IntervalEntry {
    pub fn new(start: usize, end: usize, arg: Option<ArgRegisterKind>, type_decl: Type) -> Self {
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

    // registers that are saved before function call
    saved_regs: Vec<Vec<(usize, Box<dyn ScratchRegister>, Register)>>,

    // instruction-counter
    counter: usize,
}

impl RegisterAllocation {
    pub fn new(live_intervals: HashMap<usize, IntervalEntry>) -> Self {
        RegisterAllocation {
            live_intervals,
            saved_regs: Vec::new(),
            counter: 0,
            spill_bp_offset: 0,
            spill_index: 0,
            registers: ScratchRegisters::new(),
        }
    }
    pub fn generate(mut self, mut ir: Vec<Lir>) -> Vec<Lir> {
        let mut result = Vec::with_capacity(ir.len());

        for (i, mut instr) in ir.drain(..).enumerate() {
            self.expire_old_intervals(i, &mut result);
            self.counter = i;

            self.alloc_arg(&mut result);

            match instr.get_regs_mut() {
                (Some(Register::Temp(left)), Some(Register::Temp(right))) => {
                    let left_interferences = self.interfering_intervals(left.id, Some(right.id));
                    self.alloc(left, left_interferences, &mut result);

                    let right_interferences = self.interfering_intervals(right.id, Some(left.id));
                    self.alloc(right, right_interferences, &mut result);
                }
                (Some(Register::Temp(reg)), _) | (_, Some(Register::Temp(reg))) => {
                    let interferences = self.interfering_intervals(reg.id, None);
                    self.alloc(reg, interferences, &mut result);
                }
                _ => (),
            }

            match &mut instr {
                Lir::SaveRegs => {
                    self.save_regs(&mut result);
                }
                Lir::RestoreRegs => {
                    self.restore_regs(&mut result);
                }
                Lir::FuncSetup(_, stack_size) => {
                    self.spill_bp_offset = *stack_size;

                    result.push(instr);
                }
                Lir::FuncTeardown(stack_size) => {
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
    // When explictily allocating arg-register then when arg-register is occupied the occupant gets pushed
    // exlicit arg-registers always have priority. This covers cases when a specific arg-register is needed
    // by an operation but is occpied as an argument.
    fn alloc_arg(&mut self, result: &mut Vec<Lir>) {
        // get the interval if a new arg-register has been declared
        let new_arg_interval = self.live_intervals.iter_mut().find(|(_, v)| {
            self.counter >= v.start && self.counter < v.end && v.arg.is_some() && v.scratch.is_none()
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
                result.push(Lir::Push(occupied_reg));

                self.live_intervals.get_mut(&key).unwrap().scratch =
                    Some(TempKind::Scratch(used_scratch.clone()));

                // mark occupant as pushed
                self.live_intervals.get_mut(&occupied_key).unwrap().scratch =
                    Some(TempKind::Pushed(key));
            } else {
                // if scratch isn't already used mark it as used for the arg-register
                self.registers.activate_reg(Box::new(scratch.clone()));

                self.live_intervals.get_mut(&key).unwrap().scratch =
                    Some(TempKind::Scratch(Box::new(scratch.clone())));
            }
        }
    }

    fn alloc(&mut self, reg: &mut TempRegister, other: Vec<usize>, ir: &mut Vec<Lir>) {
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
            _ => unreachable!(),
        };
        // assign register to the interval
        self.live_intervals.get_mut(&reg.id).unwrap().scratch = Some(value);
    }
    fn get_scratch(&mut self, ir: &mut Vec<Lir>, reg: &mut TempRegister, other: Vec<usize>) -> TempKind {
        if let Some(scratch) = self.registers.alloc(&other) {
            TempKind::Scratch(self.registers.0.get(scratch).unwrap().clone())
        } else {
            self.spill(ir, reg, other)
        }
    }
    fn spill(&mut self, ir: &mut Vec<Lir>, reg: &mut TempRegister, other: Vec<usize>) -> TempKind {
        let spill_reg_idx = self.choose_spill_reg(other);
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

        ir.push(Lir::Mov(Register::Temp(prev.clone()), Register::Temp(new)));

        // return the now free register
        prev.reg.unwrap()
    }

    fn unspill(&mut self, ir: &mut Vec<Lir>, reg: &mut TempRegister, other: Vec<usize>) -> TempKind {
        let Some(IntervalEntry{ type_decl, scratch:Some(entry),.. }) = self.live_intervals.get_mut(&reg.id) else {unreachable!()};

        let mut prev_reg = reg.clone();
        prev_reg.type_decl = type_decl.clone();
        prev_reg.reg = Some(entry.clone());

        let mut new = reg.clone();
        new.type_decl = type_decl.clone();
        new.reg = Some(self.get_scratch(ir, reg, other));

        ir.push(Lir::Mov(Register::Temp(prev_reg), Register::Temp(new.clone())));
        new.reg.unwrap()
    }
    // gets the corresponding scratch-register given the interval-id to a tempregister
    fn get_reg(&self, key: usize) -> Option<usize> {
        if let Some(IntervalEntry { scratch: Some(TempKind::Scratch(r)), .. }) =
            self.live_intervals.get(&key)
        {
            return self
                .registers
                .0
                .iter()
                .position(|scratch| scratch.base_name() == r.base_name());
        }
        None
    }
    // returns scratch-register-indices of intervals that will interfere own interval
    fn interfering_intervals(&self, own_key: usize, other_key: Option<usize>) -> Vec<usize> {
        let own_interval = self.live_intervals.get(&own_key).unwrap();

        let mut interfering_arg_regs: Vec<_> = self
            .live_intervals
            .values()
            .filter(|v| v.start <= own_interval.end && v.arg.is_some())
            .map(|v| {
                let name = v.arg.as_ref().unwrap().base_name();
                self.registers
                    .0
                    .iter()
                    .position(|scratch| scratch.base_name() == name)
            })
            .collect();

        if let Some(other_key) = other_key {
            interfering_arg_regs.push(self.get_reg(other_key));
        }
        interfering_arg_regs.into_iter().flatten().collect()
    }
    // gets corresponding interval-key given the index of the scratch-reg in the scratchregisters
    fn get_interval_of_reg(&self, reg_idx: usize) -> usize {
        let matching_scratches: Vec<_> = self
            .get_active_intervals()
            .iter()
            .filter_map(|(key, r)| {
                if self.registers.0.get(reg_idx).unwrap().base_name() == r.base_name() {
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
    fn choose_spill_reg(&mut self, interfering_regs: Vec<usize>) -> usize {
        while interfering_regs.contains(&self.spill_index) {
            self.spill_index = (self.spill_index + 1) % self.registers.0.len();
        }
        let index = self.spill_index;
        self.spill_index = (self.spill_index + 1) % self.registers.0.len();

        index
    }
    // marks freed interval-registers as available again and removes interval from live_intervals
    fn expire_old_intervals(&mut self, instr_idx: usize, result: &mut Vec<Lir>) {
        let expired_keys: Vec<usize> = self
            .live_intervals
            .iter()
            .filter(|(_, entry)| entry.end == instr_idx)
            .map(|(key, _)| *key)
            .collect();

        for key in expired_keys {
            if let Some(expired_intervals) = self.live_intervals.remove(&key) {
                if let Some(TempKind::Scratch(scratch)) = &expired_intervals.scratch {
                    if let Some(other_interval) = self.find_same_reg_pushed(key) {
                        // if there exists another interval where this reg is pushed, pop that instead of freeing physical
                        result.push(Lir::Pop(Register::Temp(TempRegister::default(scratch.clone()))));
                        other_interval.scratch = expired_intervals.scratch.clone();
                    } else {
                        self.registers.free_reg(scratch.clone());
                    }
                }
            }
        }
    }
    fn find_same_reg_pushed(&mut self, key: usize) -> Option<&mut IntervalEntry> {
        self.live_intervals
            .iter_mut()
            .find(|(_, entry)| {
                if let Some(TempKind::Pushed(link_id)) = entry.scratch {
                    self.counter < entry.end && link_id == key
                } else {
                    false
                }
            })
            .map(|(_, value)| value)
    }

    fn get_active_intervals(&self) -> Vec<(usize, Box<dyn ScratchRegister>)> {
        let mut active_intervals = self
            .live_intervals
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
            .collect::<Vec<_>>();

        // sort registers so that order is always the same and not determined by hashmap order -> compiler should be deterministic
        active_intervals.sort_by(|(_, a), (_, b)| a.base_name().cmp(b.base_name()));
        active_intervals
    }
    fn save_regs(&mut self, ir: &mut Vec<Lir>) {
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
            ir.push(Lir::Push(reg.clone()));

            // WARN: should be fine passing 0 as interval-key since values are restored anyway before freeing regs
            self.live_intervals.get_mut(key).unwrap().scratch = Some(TempKind::Pushed(0));
            self.registers.free_reg(scratch.clone());
        }

        // align stack
        if !active_intervals.is_empty() && active_intervals.len() % 2 != 0 {
            ir.push(Lir::SubSp(8));
        }

        self.saved_regs.push(active_intervals);
    }

    fn restore_regs(&mut self, ir: &mut Vec<Lir>) {
        let saved = self.saved_regs.pop().expect("restore always after save");

        if !saved.is_empty() && saved.len() % 2 != 0 {
            ir.push(Lir::AddSp(8));
        }
        for (key, scratch, reg) in saved.iter().rev() {
            ir.push(Lir::Pop(reg.clone()));

            // mark popped registers as used again
            self.registers.activate_reg(scratch.clone());
            self.live_intervals.get_mut(key).unwrap().scratch = Some(TempKind::Scratch(scratch.clone()));
        }
    }
    // backtrack trough result and update allocated stack-space
    fn update_func_setup(&self, result: &mut [Lir]) {
        let setup_size = result
            .iter_mut()
            .rev()
            .filter_map(|instr| {
                if let Lir::FuncSetup(.., setup_size) = instr {
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
    fn alloc(&mut self, interfering_regs: &[usize]) -> Option<usize> {
        if let Some((i, r)) = self
            .0
            .iter_mut()
            .enumerate()
            .find(|(i, r)| !r.is_used() && !interfering_regs.contains(i))
        {
            r.in_use();
            Some(i)
        } else {
            None
        }
    }
    fn activate_reg(&mut self, scratch: Box<dyn ScratchRegister>) {
        if let Some(scratch) = self.0.iter_mut().find(|s| s.base_name() == scratch.base_name()) {
            scratch.in_use()
        }
    }

    fn free_reg(&mut self, scratch: Box<dyn ScratchRegister>) {
        if let Some(scratch) = self.0.iter_mut().find(|s| s.base_name() == scratch.base_name()) {
            scratch.free()
        }
    }
    fn new() -> Self {
        // sorted in descending order of occurance probability to reduce collisions
        ScratchRegisters([
            Box::new(RegularRegister::new("%r10")),
            Box::new(RegularRegister::new("%r11")),
            Box::new(ArgRegisterKind::new(5)),
            Box::new(ArgRegisterKind::new(4)),
            Box::new(ArgRegisterKind::new(3)),
            Box::new(ArgRegisterKind::new(2)),
            Box::new(ArgRegisterKind::new(1)),
            Box::new(ArgRegisterKind::new(0)),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::typechecker::mir::expr::ValueKind;
    use std::mem;

    fn setup(intervals: HashMap<usize, IntervalEntry>, occupied_regs: Vec<usize>) -> RegisterAllocation {
        let mut reg_alloc = RegisterAllocation::new(intervals);

        for i in occupied_regs {
            reg_alloc.registers.0.get_mut(i).unwrap().in_use();
        }

        reg_alloc
    }
    impl IntervalEntry {
        fn as_reg(&self, id: usize) -> Register {
            match &self.arg {
                Some(reg) => Register::Arg(ArgRegister {
                    id,
                    reg: reg.clone(),
                    start_idx: self.start,
                    type_decl: self.type_decl.clone(),
                }),
                None => Register::Temp(TempRegister {
                    id,
                    reg: None,
                    start_idx: self.start,
                    type_decl: self.type_decl.clone(),
                    value_kind: ValueKind::Rvalue,
                }),
            }
        }
    }
    fn process_intervals(
        temps: Vec<(Option<Box<dyn ScratchRegister>>, IntervalEntry)>,
    ) -> (HashMap<usize, IntervalEntry>, Vec<Register>, Vec<Register>) {
        let intervals: HashMap<usize, IntervalEntry> = temps
            .iter()
            .enumerate()
            .map(|(k, (_, v))| (k, v.clone()))
            .collect();

        let regs: Vec<Register> = temps.iter().enumerate().map(|(k, (_, v))| v.as_reg(k)).collect();

        let filled_regs = regs
            .clone()
            .iter_mut()
            .zip(temps.iter().map(|(scratch, _)| scratch))
            .map(|(mut r, scratch)| {
                if let (Register::Temp(reg), Some(scratch)) = (&mut r, scratch) {
                    reg.reg = Some(TempKind::Scratch(scratch.clone()));
                }
                r.clone()
            })
            .collect();

        (intervals, regs, filled_regs)
    }
    fn assert_regalloc(input: Vec<Lir>, expected: Vec<Lir>, reg_alloc: RegisterAllocation) {
        let actual = reg_alloc.generate(input);

        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.iter().zip(expected) {
            let actual_ir = mem::discriminant(actual) == mem::discriminant(&expected);
            assert!(actual_ir);

            // TODO: also compare ids
            assert!(
                match (actual.get_regs(), expected.get_regs()) {
                    (
                        (Some(actual_left), Some(actual_right)),
                        (Some(expected_left), Some(expected_right)),
                    ) => {
                        actual_left.name() == expected_left.name()
                            && actual_right.name() == expected_right.name()
                    }
                    ((None, Some(actual_right)), (None, Some(expected_right))) => {
                        actual_right.name() == expected_right.name()
                    }
                    ((None, None), (None, None)) => true,
                    _ => false,
                },
                "Mismatched ir-instruction:\nactual: {}\nexpected: {}",
                actual,
                expected
            )
        }
    }
    macro_rules! temp_entry {
        ($reg:expr,$start:expr,$end:expr) => {
            (
                Some(Box::new($reg)),
                IntervalEntry::new($start, $end, None, Type::Primitive(Primitive::Int)),
            )
        };
    }
    macro_rules! arg_entry {
        ($reg:expr,$start:expr,$end:expr) => {
            (
                None,
                IntervalEntry::new($start, $end, Some($reg), Type::Primitive(Primitive::Int)),
            )
        };
    }

    #[test]
    fn arg_op_collision() {
        let occupied_regs = vec![1, 3];
        let (intervals, regs, filled_regs) = process_intervals(vec![
            temp_entry!(RegularRegister::new("%r10"), 0, 4),
            temp_entry!(ArgRegisterKind::new(5), 0, 4),
            temp_entry!(ArgRegisterKind::new(3), 0, 3),
            temp_entry!(RegularRegister::new("%r10"), 5, 7),
            // INFO: Has to be arg1 since arg2 and arg3 are reserved as required arg-regs in shift and div operation
            // during same interval (3-5 collides with: 4-6,1-4)
            temp_entry!(ArgRegisterKind::new(1), 3, 5),
            temp_entry!(ArgRegisterKind::new(5), 6, 7),
            arg_entry!(ArgRegisterKind::new(3), 4, 6),
            arg_entry!(ArgRegisterKind::new(2), 1, 4),
        ]);

        let reg_alloc = setup(intervals, occupied_regs);

        let input = vec![
            Lir::Mov(regs[0].clone(), regs[1].clone()),
            Lir::Add(regs[2].clone(), regs[1].clone()),
            Lir::Idiv(regs[1].clone()),
            Lir::Mov(regs[1].clone(), regs[4].clone()),
            Lir::Mov(regs[4].clone(), regs[6].clone()),
            Lir::Shift("l", regs[6].clone(), regs[3].clone()),
            Lir::Xor(regs[3].clone(), regs[5].clone()),
        ];

        let expected = vec![
            Lir::Mov(filled_regs[0].clone(), filled_regs[1].clone()),
            Lir::Add(filled_regs[2].clone(), filled_regs[1].clone()),
            Lir::Idiv(filled_regs[1].clone()),
            Lir::Mov(filled_regs[1].clone(), filled_regs[4].clone()),
            Lir::Mov(filled_regs[4].clone(), filled_regs[6].clone()),
            Lir::Shift("l", filled_regs[6].clone(), filled_regs[3].clone()),
            Lir::Xor(filled_regs[3].clone(), filled_regs[5].clone()),
        ];

        assert_regalloc(input, expected, reg_alloc);
    }

    #[test]
    fn spilling() {
        let occupied_regs = vec![4, 5, 6, 7];
        let (intervals, regs, filled_regs) = process_intervals(vec![
            temp_entry!(RegularRegister::new("%r10"), 0, 7),
            temp_entry!(RegularRegister::new("%r11"), 0, 4),
            temp_entry!(ArgRegisterKind::new(5), 1, 6),
            temp_entry!(ArgRegisterKind::new(4), 2, 4),
            temp_entry!(RegularRegister::new("%r10"), 3, 5),
            temp_entry!(RegularRegister::new("%r11"), 4, 6),
            temp_entry!(RegularRegister::new("%r10"), 5, 7),
        ]);

        let reg_alloc = setup(intervals, occupied_regs);

        let input = vec![
            Lir::Add(regs[0].clone(), regs[1].clone()),
            Lir::Imul(regs[1].clone(), regs[2].clone()),
            Lir::Mov(regs[3].clone(), regs[1].clone()),
            Lir::Or(regs[1].clone(), regs[4].clone()),
            Lir::Neg(regs[5].clone()),
            Lir::Mov(regs[6].clone(), regs[5].clone()),
            Lir::Mov(regs[0].clone(), regs[6].clone()),
        ];

        // Reg0 is spilled because is Lir::Or there are no regs left.
        let spilled_reg = Register::Stack(StackRegister::new(&mut 0, Type::Primitive(Primitive::Int)));

        // When it is unspilled again because it is needed in instruction 6, %r10 is not available
        // because when Reg4 was freed %r10 was marked as available again and was assigned to Reg6.
        // So now Reg0 is contained in a new register %r11 which is free at the point of unspilling.
        let unspilled_reg_0 = if let Register::Temp(filled) = filled_regs[0].clone() {
            Register::Temp(TempRegister {
                reg: Some(TempKind::Scratch(Box::new(RegularRegister::new("%r11")))),
                ..filled
            })
        } else {
            unreachable!()
        };

        let expected = vec![
            Lir::Add(filled_regs[0].clone(), filled_regs[1].clone()),
            Lir::Imul(filled_regs[1].clone(), filled_regs[2].clone()),
            Lir::Mov(filled_regs[3].clone(), filled_regs[1].clone()),
            Lir::Mov(filled_regs[0].clone(), spilled_reg.clone()),
            Lir::Or(filled_regs[1].clone(), filled_regs[4].clone()),
            Lir::Neg(filled_regs[5].clone()),
            Lir::Mov(filled_regs[6].clone(), filled_regs[5].clone()),
            Lir::Mov(spilled_reg, unspilled_reg_0.clone()),
            Lir::Mov(unspilled_reg_0.clone(), filled_regs[6].clone()),
        ];

        assert_regalloc(input, expected, reg_alloc);
    }

    #[test]
    fn call_with_spilling_arg_regs() {
        let occupied_regs = vec![];
        let (intervals, regs, filled_regs) = process_intervals(vec![
            temp_entry!(RegularRegister::new("%r10"), 1, 4),
            temp_entry!(RegularRegister::new("%r11"), 1, 3),
            temp_entry!(ArgRegisterKind::new(4), 2, 4),
            temp_entry!(RegularRegister::new("%r11"), 3, 4),
            temp_entry!(RegularRegister::new("%r10"), 4, 7),
            temp_entry!(RegularRegister::new("%r11"), 4, 7),
            temp_entry!(ArgRegisterKind::new(2), 5, 7),
            temp_entry!(RegularRegister::new("%r10"), 7, 8),
            temp_entry!(RegularRegister::new("%r10"), 8, 10),
            temp_entry!(RegularRegister::new("%r11"), 8, 10),
            temp_entry!(RegularRegister::new("%r10"), 10, 15),
            temp_entry!(RegularRegister::new("%r11"), 10, 15),
            temp_entry!(RegularRegister::new("%r10"), 12, 15),
            temp_entry!(RegularRegister::new("%r11"), 13, 15),
            temp_entry!(RegularRegister::new("%r10"), 13, 15),
            temp_entry!(RegularRegister::new("%r10"), 15, 16),
            arg_entry!(ArgRegisterKind::new(5), 3, 16),
            arg_entry!(ArgRegisterKind::new(4), 6, 16),
            arg_entry!(ArgRegisterKind::new(3), 7, 16),
            arg_entry!(ArgRegisterKind::new(2), 9, 16),
            arg_entry!(ArgRegisterKind::new(1), 14, 16),
            arg_entry!(ArgRegisterKind::new(0), 15, 16),
            // register that is occupied for div instruction
            arg_entry!(ArgRegisterKind::new(2), 10, 13),
        ]);

        let reg_alloc = setup(intervals, occupied_regs);

        let input = vec![
            Lir::SaveRegs,
            Lir::Add(regs[0].clone(), regs[1].clone()),
            Lir::Imul(regs[1].clone(), regs[2].clone()),
            Lir::Mov(regs[3].clone(), regs[16].clone()),
            Lir::Add(regs[4].clone(), regs[5].clone()),
            Lir::Imul(regs[5].clone(), regs[6].clone()),
            Lir::Mov(regs[6].clone(), regs[17].clone()),
            Lir::Mov(regs[7].clone(), regs[18].clone()),
            Lir::And(regs[8].clone(), regs[9].clone()),
            Lir::Mov(regs[9].clone(), regs[19].clone()),
            Lir::And(regs[10].clone(), regs[11].clone()),
            Lir::Idiv(regs[11].clone()),
            Lir::And(regs[11].clone(), regs[12].clone()),
            Lir::Add(regs[13].clone(), regs[14].clone()),
            Lir::Mov(regs[10].clone(), regs[20].clone()),
            Lir::Mov(regs[15].clone(), regs[21].clone()),
            Lir::Call("foo".to_string()),
            Lir::RestoreRegs,
        ];

        let mut bp = 0;
        let spilled_reg1 = Register::Stack(StackRegister::new(&mut bp, Type::Primitive(Primitive::Int)));
        let spilled_reg2 = Register::Stack(StackRegister::new(&mut bp, Type::Primitive(Primitive::Int)));
        let spilled_reg3 = Register::Stack(StackRegister::new(&mut bp, Type::Primitive(Primitive::Int)));
        let spilled_reg4 = Register::Stack(StackRegister::new(&mut bp, Type::Primitive(Primitive::Int)));

        let unspilled_reg_1 = if let Register::Temp(filled) = filled_regs[10].clone() {
            Register::Temp(TempRegister {
                reg: Some(TempKind::Scratch(Box::new(RegularRegister::new("%r11")))),
                ..filled
            })
        } else {
            unreachable!()
        };
        let expected = vec![
            Lir::Add(filled_regs[0].clone(), filled_regs[1].clone()),
            Lir::Imul(filled_regs[1].clone(), filled_regs[2].clone()),
            Lir::Mov(filled_regs[3].clone(), filled_regs[16].clone()),
            Lir::Add(filled_regs[4].clone(), filled_regs[5].clone()),
            Lir::Imul(filled_regs[5].clone(), filled_regs[6].clone()),
            Lir::Mov(filled_regs[6].clone(), filled_regs[17].clone()),
            Lir::Mov(filled_regs[7].clone(), filled_regs[18].clone()),
            Lir::And(filled_regs[8].clone(), filled_regs[9].clone()),
            Lir::Mov(filled_regs[9].clone(), filled_regs[19].clone()),
            Lir::Push(filled_regs[22].clone()),
            Lir::And(filled_regs[10].clone(), filled_regs[11].clone()),
            Lir::Idiv(filled_regs[11].clone()),
            Lir::Mov(filled_regs[10].clone(), spilled_reg1.clone()), // spill %r10
            Lir::And(filled_regs[11].clone(), filled_regs[12].clone()),
            Lir::Pop(filled_regs[22].clone()),
            Lir::Mov(filled_regs[11].clone(), spilled_reg2), // spill %r11
            Lir::Mov(filled_regs[12].clone(), spilled_reg3), // spill %r10
            Lir::Add(filled_regs[13].clone(), filled_regs[14].clone()),
            Lir::Mov(filled_regs[13].clone(), spilled_reg4), // spill %r11
            Lir::Mov(spilled_reg1, unspilled_reg_1.clone()), // unspill filled_reg[10]
            Lir::Mov(unspilled_reg_1, filled_regs[20].clone()),
            Lir::Mov(filled_regs[15].clone(), filled_regs[21].clone()),
            Lir::Call("foo".to_string()),
        ];

        assert_regalloc(input, expected, reg_alloc);
    }
}
