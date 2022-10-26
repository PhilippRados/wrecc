use crate::common::types::Types;

#[derive(Clone)]
pub enum Register {
    Scratch(ScratchIndex, Types),
    Stack(StackRegister, Types),
    Arg(usize, Types),
    Void,
}
impl Register {
    pub fn free(&self, scratch_regs: &mut ScratchRegisters) {
        match self {
            Register::Void => (),
            Register::Stack(_, _) => (),
            Register::Arg(_, _) => (),
            Register::Scratch(index, _) => scratch_regs.get_mut(index).free(),
        }
    }
    pub fn name(&self, scratch_regs: &ScratchRegisters) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg, _) => reg.name(),
            Register::Scratch(index, type_decl) => {
                format!("{}{}", scratch_regs.get(index).name, type_decl.reg_suffix())
            }
            Register::Arg(index, type_decl) => {
                self.get_arg_reg(*index, type_decl.clone()).to_string()
            }
        }
    }
    // argument registers from 1st to last
    fn get_arg_reg(&self, index: usize, type_decl: Types) -> &str {
        // char gets promoted to 32bit as argument
        match (type_decl, index) {
            (Types::Int, 0) => "%edi",
            (Types::Int, 1) => "%esi",
            (Types::Int, 2) => "%edx",
            (Types::Int, 3) => "%ecx",
            (Types::Int, 4) => "%r8d",
            (Types::Int, 5) => "%r9d",

            (Types::Char, 0) => "%dil",
            (Types::Char, 1) => "%sil",
            (Types::Char, 2) => "%dl",
            (Types::Char, 3) => "%cl",
            (Types::Char, 4) => "%r8b",
            (Types::Char, 5) => "%r9b",
            _ => unreachable!(),
        }
    }
    pub fn set_type(&mut self, type_decl: Types) {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_, _) => (),
            Register::Scratch(_, old_decl) => *old_decl = type_decl,
            Register::Arg(_, old_decl) => *old_decl = type_decl,
        }
    }
    pub fn get_type(&self) -> Types {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_, type_decl)
            | Register::Scratch(_, type_decl)
            | Register::Arg(_, type_decl) => type_decl.clone(),
        }
    }
}
#[derive(Clone)]
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
    pub name: &'static str,
}
impl ScratchRegister {
    fn free(&mut self) {
        self.in_use = false;
    }
}
#[derive(Debug)]
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
        panic!("no free register");
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
                    name: "%r8",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r9",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r10",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r11",
                },
            ],
        }
    }
}
