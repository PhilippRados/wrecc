use crate::common::expr::ValueKind;
use crate::common::types::*;
use std::cell::RefCell;
use std::rc::Rc;

pub trait RegName {
    fn name(&self, type_decl: &NEWTypes) -> String;
}

pub enum Register {
    Scratch(Rc<Rc<RefCell<ScratchRegister>>>, NEWTypes, ValueKind),
    Stack(StackRegister),
    Arg(Rc<Rc<RefCell<ArgRegister>>>, NEWTypes),
    Void,
}
impl Register {
    pub fn free(&self) {
        match self {
            Register::Void => (),
            Register::Stack(_) => (),
            Register::Arg(_, _) => (),
            Register::Scratch(reg, _, _) => reg.borrow_mut().free(), //scratch_regs.get_mut(index).free(),
        }
    }
    pub fn name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Scratch(reg, type_decl, valuekind) => match valuekind {
                ValueKind::Rvalue => reg.borrow().name(type_decl).to_string(),
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
            Register::Arg(reg, type_decl) => reg.borrow().name(type_decl).to_string(),
        }
    }
    pub fn set_type(&mut self, type_decl: NEWTypes) {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_) => (),
            Register::Scratch(_, old_decl, _) => *old_decl = type_decl,
            Register::Arg(_, old_decl) => *old_decl = type_decl,
        }
    }
    pub fn get_type(&self) -> NEWTypes {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.type_decl.clone(),
            Register::Scratch(_, type_decl, _) | Register::Arg(_, type_decl) => type_decl.clone(),
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
#[derive(Debug)]
pub struct ArgRegisters {
    pub registers: [Rc<RefCell<ArgRegister>>; 6],
}
impl ArgRegisters {
    pub fn new() -> Self {
        ArgRegisters {
            registers: [
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 0,
                })),
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 1,
                })),
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 2,
                })),
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 3,
                })),
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 4,
                })),
                Rc::new(RefCell::new(ArgRegister {
                    in_use: false,
                    index: 5,
                })),
            ],
        }
    }
}

static ARG_REGISTER_MAP: &[[&'static str; 6]] = &[
    ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"],
    ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"],
    ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
];
#[derive(Clone, Debug)]
pub struct ArgRegister {
    pub in_use: bool,
    index: usize,
}
impl RegName for ArgRegister {
    fn name(&self, type_decl: &NEWTypes) -> String {
        match type_decl {
            NEWTypes::Primitive(Types::Char) => ARG_REGISTER_MAP[0][self.index].to_string(),
            NEWTypes::Primitive(Types::Int) => ARG_REGISTER_MAP[1][self.index].to_string(),
            NEWTypes::Primitive(Types::Long) | NEWTypes::Pointer(_) | NEWTypes::Array { .. } => {
                ARG_REGISTER_MAP[2][self.index].to_string()
            }
            _ => unreachable!("cant pass void argument"),
        }
    }
}
impl ArgRegisters {
    pub fn alloc(&self, index: usize) -> Rc<Rc<RefCell<ArgRegister>>> {
        self.registers[index].borrow_mut().in_use = true;
        Rc::new(Rc::clone(&self.registers[index]))
    }
    pub fn get(&self, index: usize) -> Rc<Rc<RefCell<ArgRegister>>> {
        Rc::new(Rc::clone(&self.registers[index]))
    }
    pub fn free_all(&mut self) {
        for r in self.registers.iter_mut() {
            r.borrow_mut().in_use = false;
        }
    }
}

#[derive(Clone)]
pub struct StackRegister {
    bp_offset: usize,
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

#[derive(Clone, Debug)]
pub struct ScratchRegister {
    pub in_use: bool,
    pub base_name: &'static str,
}
impl ScratchRegister {
    fn free(&mut self) {
        self.in_use = false;
    }
}
impl RegName for ScratchRegister {
    fn name(&self, type_decl: &NEWTypes) -> String {
        format!("{}{}", self.base_name, type_decl.reg_suffix())
    }
}

#[derive(Debug)]
pub struct ScratchRegisters {
    pub registers: [Rc<RefCell<ScratchRegister>>; 4],
}
impl ScratchRegisters {
    pub fn scratch_alloc(&self) -> Rc<Rc<RefCell<ScratchRegister>>> {
        for (i, r) in self.registers.iter().enumerate() {
            if !r.borrow().in_use {
                r.borrow_mut().in_use = true;
                return Rc::new(Rc::clone(&self.registers[i]));
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
