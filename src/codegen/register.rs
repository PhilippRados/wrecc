use crate::common::expr::ValueKind;
use crate::common::types::*;
use std::cell::RefCell;
use std::fmt::Write;
use std::rc::Rc;

static ARG_REGISTER_MAP: &[[&str; 6]] = &[
    ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"],
    ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"],
    ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
];

#[derive(Debug, PartialEq, Clone)]
pub enum Register {
    // scratch/spilled-registers hold temporary expression results
    Temp(TempRegister),
    // variables that live on the local function-stack
    Stack(StackRegister),
    // Labels can be Strings and global variables
    Label(LabelRegister),
    // Special register only used for spilling
    Spare(SpareRegister),
    // numerical constants
    Literal(usize, NEWTypes),
    // registers that are used in function calls for arguments
    Arg(usize, NEWTypes),
    // indicator register for functions returning void
    Void,
}
impl Register {
    pub fn free(&mut self, output: &mut String) {
        match self {
            Register::Void
            | Register::Stack(_)
            | Register::Arg(..)
            | Register::Label(_)
            | Register::Literal(..) => (),
            Register::Spare(reg) => *self = reg.free(output),
            Register::Temp(reg) => reg.free(),
        }
    }
    pub fn name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.name(),
            Register::Literal(n, _) => format!("${n}"),
            Register::Temp(reg) => reg.name(),
            Register::Spare(reg) => reg.name(),
            Register::Arg(i, type_decl) => self.get_arg_reg(*i, type_decl),
        }
    }
    // name as 64bit register
    pub fn base_name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.base_name(),
            Register::Literal(n, ..) => format!("{n}"),
            Register::Temp(reg) => reg.base_name(),
            Register::Spare(reg) => reg.base_name.to_string(),
            Register::Arg(i, _) => ARG_REGISTER_MAP[2][*i].to_string(),
        }
    }
    pub fn get_arg_reg(&self, index: usize, type_decl: &NEWTypes) -> String {
        match type_decl {
            NEWTypes::Primitive(Types::Char) => ARG_REGISTER_MAP[0][index],
            NEWTypes::Primitive(Types::Int) | NEWTypes::Enum(..) => ARG_REGISTER_MAP[1][index],
            NEWTypes::Primitive(Types::Long) | NEWTypes::Pointer(_) | NEWTypes::Array { .. } => {
                ARG_REGISTER_MAP[2][index]
            }
            _ => unimplemented!("aggregate types are not yet implemented as function args"),
        }
        .to_string()
    }
    pub fn set_type(&mut self, type_decl: NEWTypes) {
        match self {
            Register::Void => unimplemented!(),
            Register::Label(reg) => reg.set_type(type_decl),
            Register::Literal(_, old_decl) => *old_decl = type_decl,
            Register::Stack(reg) => reg.type_decl = type_decl,
            Register::Temp(reg) => reg.type_decl = type_decl,
            Register::Spare(reg) => reg.set_type(type_decl),
            Register::Arg(_, old_decl) => *old_decl = type_decl,
        }
    }
    pub fn get_type(&self) -> NEWTypes {
        match self {
            Register::Void => unimplemented!(),
            Register::Label(reg) => reg.get_type(),
            Register::Literal(_, type_decl) => type_decl.clone(),
            Register::Stack(reg) => reg.type_decl.clone(),
            Register::Temp(reg) => reg.type_decl.clone(),
            Register::Spare(reg) => reg.dest.get_type(),
            Register::Arg(_, type_decl) => type_decl.clone(),
        }
    }
    pub fn is_lval(&self) -> bool {
        matches!(self, Register::Temp(reg) if reg.value_kind == ValueKind::Lvalue && !reg.is_spilled())
    }
    pub fn is_scratch(&self) -> bool {
        match self {
            Register::Temp(reg) => !reg.is_spilled(),
            _ => false,
        }
    }
    pub fn is_spilled(&self) -> bool {
        match self {
            Register::Temp(reg) => reg.is_spilled(),
            _ => false,
        }
    }
    pub fn set_value_kind(&mut self, new_val_kind: ValueKind) {
        if let Register::Temp(reg) = self {
            reg.value_kind = new_val_kind
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
    fn set_type(&mut self, new_type: NEWTypes) {
        match self {
            LabelRegister::String(_) => (),
            LabelRegister::Var(_, type_decl) => *type_decl = new_type,
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
    pub fn new(bp_offset: &mut usize, type_decl: NEWTypes) -> Self {
        *bp_offset += type_decl.size();
        *bp_offset = crate::codegen::codegen::align(*bp_offset, &type_decl);

        StackRegister {
            bp_offset: *bp_offset,
            type_decl,
        }
    }
    pub fn name(&self) -> String {
        format!("-{}(%rbp)", self.bp_offset)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SpareRegister {
    dest: Box<Register>,
    base_name: &'static str,
}
impl SpareRegister {
    pub fn new(dest: Register) -> Self {
        SpareRegister {
            dest: Box::new(dest),
            base_name: "r12",
        }
    }
    fn name(&self) -> String {
        format!("%{}{}", self.base_name, self.dest.get_type().reg_suffix())
    }
    fn free(&self, output: &mut String) -> Register {
        writeln!(
            output,
            "\tmov{}   {}, {}",
            self.dest.get_type().suffix(),
            self.name(),
            self.dest.name()
        )
        .unwrap();
        *self.dest.clone()
    }
    fn set_type(&mut self, new_type: NEWTypes) {
        self.dest.set_type(new_type)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TempKind {
    Scratch(Rc<RefCell<ScratchRegister>>),
    Spilled(StackRegister),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TempRegister {
    pub type_decl: NEWTypes,
    pub reg: TempKind,
    // output: Rc<RefCell<String>>,
    pub value_kind: ValueKind,
}
impl TempRegister {
    pub fn new(
        scratches: &mut ScratchRegisters,
        type_decl: NEWTypes,
        spill_bp_offset: &mut usize,
    ) -> Self {
        let reg = scratches.scratch_alloc(type_decl.clone(), spill_bp_offset);

        TempRegister {
            type_decl,
            reg,
            // output: Rc::clone(&output),
            value_kind: ValueKind::Rvalue,
        }
    }
    fn free(&self) {
        match &self.reg {
            TempKind::Scratch(reg) => reg.borrow_mut().free(),
            TempKind::Spilled(..) => (),
        }
    }
    fn name(&self) -> String {
        match (&self.reg, &self.value_kind) {
            (TempKind::Scratch(reg), ValueKind::Rvalue) => reg.borrow().name(&self.type_decl),
            (TempKind::Scratch(..), ValueKind::Lvalue) => self.base_name(),
            (TempKind::Spilled(reg), ..) => reg.name(),
        }
    }
    fn base_name(&self) -> String {
        match (&self.reg, &self.value_kind) {
            // base_name for scratch-register is just it's 64bit name
            (TempKind::Scratch(reg), ValueKind::Rvalue) => {
                reg.borrow()
                    .name(&NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                        Types::Void,
                    ))))
            }
            (TempKind::Scratch(reg), ValueKind::Lvalue) => {
                format!(
                    "({})",
                    reg.borrow()
                        .name(&NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                            Types::Void
                        ))))
                )
            }
            (TempKind::Spilled(reg), ..) => reg.name(),
        }
    }
    pub fn is_spilled(&self) -> bool {
        match &self.reg {
            TempKind::Spilled(..) => true,
            TempKind::Scratch(..) => false,
        }
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
    pub fn scratch_alloc(&mut self, type_decl: NEWTypes, spill_bp_offset: &mut usize) -> TempKind {
        for r in self.registers.iter() {
            if !r.borrow().in_use {
                r.borrow_mut().in_use = true;
                return TempKind::Scratch(Rc::clone(&r));
            }
        }
        // when no more registers free has to spill register to stack
        // whenever it is used and it needs to be in physical register
        // then it's converted
        TempKind::Spilled(StackRegister::new(spill_bp_offset, type_decl))
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
    pub fn is_all_spilled(&self) -> bool {
        !self
            .registers
            .iter()
            .map(|r| r.borrow().in_use)
            .any(|in_use| !in_use)
    }
}
