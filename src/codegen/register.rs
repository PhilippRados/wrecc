use crate::common::expr::ValueKind;
use crate::common::types::*;

static ARG_REGISTER_MAP: &[[&str; 6]] = &[
    ["%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"],
    ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"],
    ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
];

#[derive(Debug, PartialEq, Clone)]
pub enum Register {
    // virtual register that can be infinite in amount; get transformed into pysical registers
    // in register-allocation pass
    Temp(TempRegister),
    // variables that live on the local function-stack
    Stack(StackRegister),
    // Labels can be Strings and global variables
    Label(LabelRegister),
    // register used for return values
    Return(NEWTypes),
    // numerical constants
    Literal(usize, NEWTypes),
    // registers that are used in function calls for arguments
    Arg(usize, NEWTypes),
    // indicator register for functions returning void
    Void,
}
impl Register {
    pub fn name(&self) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.name(),
            Register::Literal(n, _) => format!("${n}"),
            Register::Temp(reg) => reg.name(),
            Register::Return(t) => t.return_reg(),
            Register::Arg(i, type_decl) => self.get_arg_reg(*i, type_decl),
        }
    }
    // name as 64bit register
    pub fn base_name(&self) -> String {
        match self {
            Register::Void | Register::Return(..) => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Label(reg) => reg.base_name(),
            Register::Literal(n, ..) => format!("{n}"),
            Register::Temp(reg) => reg.base_name(),
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
            Register::Void | Register::Return(..) => unimplemented!(),
            Register::Label(reg) => reg.set_type(type_decl),
            Register::Literal(_, old_decl) => *old_decl = type_decl,
            Register::Stack(reg) => reg.type_decl = type_decl,
            Register::Temp(reg) => reg.type_decl = type_decl,
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
            Register::Return(t) => t.clone(),
            Register::Arg(_, type_decl) => type_decl.clone(),
        }
    }
    pub fn is_lval(&self) -> bool {
        matches!(self, Register::Temp(reg) if reg.value_kind == ValueKind::Lvalue)
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

#[derive(Debug, PartialEq, Clone)]
pub enum TempKind {
    Scratch(ScratchRegister),
    Spilled(StackRegister),
}

#[derive(Debug, PartialEq, Clone)]
pub struct TempRegister {
    pub type_decl: NEWTypes,
    pub reg: Option<TempKind>,
    pub value_kind: ValueKind,
    // key into interval hashmap
    pub id: usize,
}
impl TempRegister {
    pub fn new(type_decl: NEWTypes, key_counter: &mut usize) -> Self {
        *key_counter += 1;
        TempRegister {
            id: *key_counter,
            type_decl,
            reg: None,
            value_kind: ValueKind::Rvalue,
        }
    }
    // boilerplate register that is only access it's base-name
    pub fn default(reg: ScratchRegister) -> Self {
        TempRegister {
            type_decl: NEWTypes::default(),
            id: 0,
            reg: Some(TempKind::Scratch(reg)),
            value_kind: ValueKind::Rvalue,
        }
    }
    fn name(&self) -> String {
        match (&self.reg, &self.value_kind) {
            (Some(TempKind::Scratch(reg)), ValueKind::Rvalue) => reg.name(&self.type_decl),
            (Some(TempKind::Scratch(..)), ValueKind::Lvalue) => self.base_name(),
            (Some(TempKind::Spilled(reg)), ..) => reg.name(),
            _ => unreachable!("register should always be filled by allocator"),
        }
    }
    fn base_name(&self) -> String {
        match (&self.reg, &self.value_kind) {
            // base_name for scratch-register is just it's 64bit name
            (Some(TempKind::Scratch(reg)), ValueKind::Rvalue) => reg.name(&NEWTypes::Pointer(
                Box::new(NEWTypes::Primitive(Types::Void)),
            )),
            (Some(TempKind::Scratch(reg)), ValueKind::Lvalue) => {
                format!(
                    "({})",
                    reg.name(&NEWTypes::Pointer(Box::new(NEWTypes::Primitive(
                        Types::Void
                    ))))
                )
            }
            (Some(TempKind::Spilled(reg)), ..) => reg.name(),
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ScratchRegister {
    pub in_use: bool,
    pub base_name: &'static str,
}

impl ScratchRegister {
    fn name(&self, type_decl: &NEWTypes) -> String {
        format!("{}{}", self.base_name, type_decl.reg_suffix())
    }
}
