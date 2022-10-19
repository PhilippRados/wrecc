pub enum Register {
    Scratch(ScratchIndex),
    Stack(StackRegister),
    Arg(usize),
    Void,
}
impl Register {
    pub fn free(&self, scratch_regs: &mut ScratchRegisters) {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_) => (),
            Register::Arg(_) => (),
            Register::Scratch(index) => scratch_regs.get_mut(index).free(),
        }
    }
    pub fn name(&self, scratch_regs: &ScratchRegisters) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Scratch(index) => scratch_regs.get(index).name.to_string(),
            Register::Arg(index) => self.get_arg_reg(*index).to_string(),
        }
    }
    // argument registers from 1st to last
    fn get_arg_reg(&self, index: usize) -> &str {
        match index {
            0 => "%edi",
            1 => "%esi",
            2 => "%edx",
            3 => "%ecx",
            4 => "%r8d",
            5 => "%r9d",
            _ => unreachable!(),
        }
    }
}
#[derive(PartialEq, Clone)]
pub struct StackRegister {
    bp_offset: usize,
}
impl StackRegister {
    pub fn new(bp_offset: usize) -> Self {
        StackRegister { bp_offset }
    }
    pub fn name(&self) -> String {
        format!("-{}(%rbp)", self.bp_offset)
    }
}

#[derive(Clone)]
pub enum ScratchIndex {
    R8,
    R9,
    R10,
    R11,
}
impl ScratchIndex {
    fn index(&self) -> usize {
        match self {
            ScratchIndex::R8 => 0,
            ScratchIndex::R9 => 1,
            ScratchIndex::R10 => 2,
            ScratchIndex::R11 => 3,
        }
    }
}
impl From<usize> for ScratchIndex {
    fn from(index: usize) -> Self {
        match index {
            0 => ScratchIndex::R8,
            1 => ScratchIndex::R9,
            2 => ScratchIndex::R10,
            3 => ScratchIndex::R11,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ScratchRegister {
    pub in_use: bool,
    name: &'static str,
    pub name_64: &'static str,
}
impl ScratchRegister {
    fn free(&mut self) {
        self.in_use = false;
    }
}
pub struct ScratchRegisters {
    pub registers: [ScratchRegister; 4],
}
impl ScratchRegisters {
    pub fn scratch_alloc(&mut self) -> ScratchIndex {
        for (i, r) in self.registers.iter_mut().enumerate() {
            if !r.in_use {
                r.in_use = true;
                return ScratchIndex::from(i);
            }
        }
        panic!("no free regesiter");
    }
    fn get_mut(&mut self, reg: &ScratchIndex) -> &mut ScratchRegister {
        &mut self.registers[reg.index()]
    }
    fn get(&self, reg: &ScratchIndex) -> &ScratchRegister {
        &self.registers[reg.index()]
    }
    pub fn new() -> Self {
        ScratchRegisters {
            registers: [
                ScratchRegister {
                    in_use: false,
                    name: "%r8d",
                    name_64: "%r8",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r9d",
                    name_64: "%r9",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r10d",
                    name_64: "%r10",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r11d",
                    name_64: "%r11",
                },
            ],
        }
    }
}
