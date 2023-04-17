use crate::common::expr::ValueKind;
use crate::common::types::*;
use std::cell::RefCell;
use std::rc::Rc;

static ARG_REGISTER_MAP: &[[&str; 6]] = &[
    ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"],
    ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"],
    ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
];

#[derive(Debug, PartialEq, Clone)]
pub enum Register {
    Scratch(Rc<RefCell<ScratchRegister>>, NEWTypes, ValueKind),
    Stack(StackRegister),
    Label(LabelRegister),
    Literal(usize, NEWTypes),
    Arg(usize, NEWTypes),
    Void,
}
impl Register {
    pub fn free(&self) {
        match self {
            Register::Void
            | Register::Stack(_)
            | Register::Arg(..)
            | Register::Label(_)
            | Register::Literal(..) => (),
            Register::Scratch(reg, _, _) => reg.borrow_mut().free(),
        }
    }
    pub fn name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.name(),
            Register::Literal(n, _) => format!("${n}"),
            Register::Scratch(reg, type_decl, valuekind) => match valuekind {
                ValueKind::Rvalue => reg.borrow().name(type_decl),
                ValueKind::Lvalue => self.base_name(),
            },
            Register::Arg(i, type_decl) => match type_decl {
                NEWTypes::Primitive(Types::Char) => ARG_REGISTER_MAP[0][*i].to_string(),
                NEWTypes::Primitive(Types::Int) | NEWTypes::Enum(..) => {
                    ARG_REGISTER_MAP[1][*i].to_string()
                }
                NEWTypes::Primitive(Types::Long)
                | NEWTypes::Pointer(_)
                | NEWTypes::Array { .. } => ARG_REGISTER_MAP[2][*i].to_string(),
                _ => unreachable!("cant pass void argument"),
            },
        }
    }
    // name as 64bit register
    pub fn base_name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.base_name(),
            Register::Literal(index, ..) => format!("{index}"),
            Register::Scratch(reg, _, valuekind) => match valuekind {
                ValueKind::Rvalue => {
                    reg.borrow()
                        .name(&NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                            Types::Void,
                        ))))
                }
                ValueKind::Lvalue => {
                    format!(
                        "({})",
                        reg.borrow()
                            .name(&NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                                Types::Void
                            ))))
                    )
                }
            },
            Register::Arg(i, _) => ARG_REGISTER_MAP[2][*i].to_string(),
        }
    }
    pub fn set_type(&mut self, type_decl: NEWTypes) {
        match self {
            Register::Void => unimplemented!(),
            Register::Label(_) => (),
            Register::Literal(_, old_decl) => *old_decl = type_decl,
            Register::Stack(reg) => reg.type_decl = type_decl,
            Register::Scratch(_, old_decl, _) => *old_decl = type_decl,
            Register::Arg(_, old_decl) => *old_decl = type_decl,
        }
    }
    pub fn get_type(&self) -> NEWTypes {
        match self {
            Register::Void => unimplemented!(),
            Register::Label(reg) => reg.get_type(),
            Register::Literal(_, type_decl) => type_decl.clone(),
            Register::Stack(reg) => reg.type_decl.clone(),
            Register::Scratch(_, type_decl, _) | Register::Arg(_, type_decl) => type_decl.clone(),
        }
    }
    pub fn is_lval(&self) -> bool {
        matches!(self, Register::Scratch(_, _, value_kind) if *value_kind == ValueKind::Lvalue)
    }
    pub fn set_value_kind(&mut self, new_val_kind: ValueKind) {
        if let Register::Scratch(_, _, value_kind) = self {
            *value_kind = new_val_kind
        }
    }
}
#[derive(Debug, PartialEq, Clone)]
pub enum LabelRegister {
    String(usize),
    Var(String, NEWTypes),
}
impl LabelRegister {
    fn get_type(&self) -> NEWTypes {
        match self {
            LabelRegister::String(_) => {
                NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char)))
            }
            LabelRegister::Var(_, type_decl) => type_decl.clone(),
        }
    }
    fn name(&self) -> String {
        format!("{}(%rip)", self.base_name())
    }

    fn base_name(&self) -> String {
        match self {
            LabelRegister::String(index) => format!("LS{index}"),
            LabelRegister::Var(name, _) => format!("_{name}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StackRegister {
    pub bp_offset: usize,
    type_decl: NEWTypes,
}
impl StackRegister {
    pub fn new(bp_offset: usize, type_decl: NEWTypes) -> Self {
        StackRegister {
            bp_offset,
            type_decl,
        }
    }
    pub fn name(&self) -> String {
        format!("-{}(%rbp)", self.bp_offset)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ScratchRegister {
    pub in_use: bool,
    pub base_name: &'static str,
}
impl ScratchRegister {
    fn free(&mut self) {
        self.in_use = false;
    }
    fn name(&self, type_decl: &NEWTypes) -> String {
        format!("{}{}", self.base_name, type_decl.reg_suffix())
    }
}

#[derive(Debug)]
pub struct ScratchRegisters {
    pub registers: [Rc<RefCell<ScratchRegister>>; 4],
}
impl ScratchRegisters {
    pub fn scratch_alloc(&self) -> Rc<RefCell<ScratchRegister>> {
        for (i, r) in self.registers.iter().enumerate() {
            if !r.borrow().in_use {
                r.borrow_mut().in_use = true;
                return Rc::clone(&self.registers[i]);
            }
        }
        panic!("no free register");
    }
    pub fn new() -> Self {
        ScratchRegisters {
            registers: [
                Rc::new(RefCell::new(ScratchRegister {
                    in_use: false,
                    base_name: "%r8",
                })),
                Rc::new(RefCell::new(ScratchRegister {
                    in_use: false,
                    base_name: "%r9",
                })),
                Rc::new(RefCell::new(ScratchRegister {
                    in_use: false,
                    base_name: "%r10",
                })),
                Rc::new(RefCell::new(ScratchRegister {
                    in_use: false,
                    base_name: "%r11",
                })),
            ],
        }
    }
}
