use crate::common::expr::ValueKind;
use crate::common::types::*;

#[derive(Clone, Debug)]
pub enum Register {
    Scratch(ScratchIndex, NEWTypes, ValueKind),
    Stack(StackRegister, NEWTypes),
    Arg(usize, NEWTypes),
    Void,
}
impl Register {
    pub fn free(&self, scratch_regs: &mut ScratchRegisters) {
        match self {
            Register::Void => (),
            Register::Stack(_, _) => (),
            Register::Arg(_, _) => (),
            Register::Scratch(index, _, _) => scratch_regs.get_mut(index).free(),
        }
    }
    pub fn name(&self, scratch_regs: &ScratchRegisters) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg, _) => reg.name(),
            Register::Scratch(index, type_decl, valuekind) => match valuekind {
                ValueKind::Rvalue => {
                    format!("{}{}", scratch_regs.get(index).name, type_decl.reg_suffix())
                }
                ValueKind::Lvalue => {
                    format!("({})", scratch_regs.get(index).name)
                }
            },
            Register::Arg(index, type_decl) => type_decl.get_arg_reg(*index).to_string(),
        }
    }
    pub fn set_type(&mut self, type_decl: NEWTypes) {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_, _) => (),
            Register::Scratch(_, old_decl, _) => *old_decl = type_decl,
            Register::Arg(_, old_decl) => *old_decl = type_decl,
        }
    }
    pub fn get_type(&self) -> NEWTypes {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_, type_decl)
            | Register::Scratch(_, type_decl, _)
            | Register::Arg(_, type_decl) => type_decl.clone(),
        }
    }
    pub fn is_lval(&self) -> bool {
        match self {
            Register::Scratch(_, _, value_kind) if *value_kind == ValueKind::Lvalue => true,
            _ => false,
        }
    }
    pub fn set_value_kind(&mut self, new_val_kind: ValueKind) {
        match self {
            Register::Scratch(_, _, value_kind) => *value_kind = new_val_kind,
            _ => (),
        }
    }
}
#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
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
