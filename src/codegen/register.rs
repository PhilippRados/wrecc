use crate::common::expr::ValueKind;
use crate::common::types::*;

pub static ARG_REGS: &[[&str; 3]; 6] = &[
    ["%rdi", "%edi", "%dil"],
    ["%rsi", "%esi", "%sil"],
    ["%rdx", "%edx", "%dl"],
    ["%rcx", "%ecx", "%cl"],
    ["%r8", "%r8d", "%r8b"],
    ["%r9", "%r9d", "%r9b"],
];

#[derive(Debug, Clone)]
pub enum Register {
    // Virtual register that can be infinite in amount; get transformed into pysical registers
    // in register-allocation pass
    Temp(TempRegister),
    // Variables that live on the local function-stack
    Stack(StackRegister),
    // Labels can be Strings and global variables
    Label(LabelRegister),
    // Registers used in function calls for arguments, and in special operations
    Arg(ArgRegister),
    // Register used for return values
    Return(NEWTypes),
    // Numerical constants
    Literal(i64, NEWTypes),
    // Indicator register for functions returning void
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
            Register::Arg(reg) => reg.name(),
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
            Register::Arg(reg) => reg.base_name(),
        }
    }
    pub fn set_type(&mut self, type_decl: NEWTypes) {
        match self {
            Register::Void | Register::Return(..) => unimplemented!(),
            Register::Label(reg) => reg.set_type(type_decl),
            Register::Literal(_, old_type) => *old_type = type_decl,
            Register::Stack(reg) => reg.type_decl = type_decl,
            Register::Temp(reg) => reg.type_decl = type_decl,
            Register::Arg(reg) => reg.type_decl = type_decl,
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
            Register::Arg(reg) => reg.type_decl.clone(),
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
enum StackKind {
    Signed,
    Unsigned,
}
#[derive(Debug, Clone, PartialEq)]
pub struct StackRegister {
    pub bp_offset: usize,
    kind: StackKind,
    type_decl: NEWTypes,
}
impl StackRegister {
    pub fn new(bp_offset: &mut usize, type_decl: NEWTypes) -> Self {
        *bp_offset += type_decl.size();
        *bp_offset = crate::codegen::codegen::align(*bp_offset, &type_decl);

        StackRegister {
            bp_offset: *bp_offset,
            kind: StackKind::Signed,
            type_decl,
        }
    }
    pub fn new_pushed(arg_index: usize) -> Self {
        assert!(arg_index >= 6);
        let arg_stack_index: usize = (arg_index as isize - ARG_REGS.len() as isize) as usize;
        const PUSHED_PARAM_OFFSET: usize = 16;
        let bp_offset =
            PUSHED_PARAM_OFFSET + arg_stack_index * NEWTypes::Primitive(Types::Long).size();

        Self {
            bp_offset,
            kind: StackKind::Unsigned,
            type_decl: NEWTypes::Primitive(Types::Long),
        }
    }
    pub fn name(&self) -> String {
        match self.kind {
            StackKind::Signed => format!("-{}(%rbp)", self.bp_offset),
            StackKind::Unsigned => format!("{}(%rbp)", self.bp_offset),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TempKind {
    Scratch(Box<dyn ScratchRegister>),
    Spilled(StackRegister),
    Pushed(usize),
}

#[derive(Debug, Clone)]
pub struct TempRegister {
    pub type_decl: NEWTypes,
    pub reg: Option<TempKind>,
    pub value_kind: ValueKind,
    pub start_idx: usize,
    // key into interval hashmap
    pub id: usize,
}
impl TempRegister {
    pub fn new(type_decl: NEWTypes, key_counter: &mut usize, instr_counter: usize) -> Self {
        *key_counter += 1;
        TempRegister {
            id: *key_counter,
            type_decl,
            reg: None,
            start_idx: instr_counter,
            value_kind: ValueKind::Rvalue,
        }
    }
    // boilerplate register that is only used to access it's base-name
    pub fn default(reg: Box<dyn ScratchRegister>) -> Self {
        TempRegister {
            type_decl: NEWTypes::default(),
            id: 0,
            reg: Some(TempKind::Scratch(reg)),
            start_idx: 0,
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
            (Some(TempKind::Scratch(reg)), ValueKind::Rvalue) => reg.base_name().to_string(),
            (Some(TempKind::Scratch(reg)), ValueKind::Lvalue) => {
                format!("({})", reg.base_name())
            }
            (Some(TempKind::Spilled(reg)), ..) => reg.name(),
            _ => unreachable!(),
        }
    }
}

pub trait ScratchRegister: ScratchClone {
    fn base_name(&self) -> &'static str;
    fn name(&self, type_decl: &NEWTypes) -> String;
    fn is_used(&self) -> bool;
    fn in_use(&mut self);
    fn free(&mut self);
}

impl std::fmt::Debug for dyn ScratchRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.base_name(), self.is_used())
    }
}

// hacky way to get clone to work on trait object
pub trait ScratchClone {
    fn clone_box(&self) -> Box<dyn ScratchRegister>;
}
impl<T> ScratchClone for T
where
    T: 'static + ScratchRegister + Clone,
{
    fn clone_box(&self) -> Box<dyn ScratchRegister> {
        Box::new(self.clone())
    }
}
impl Clone for Box<dyn ScratchRegister> {
    fn clone(&self) -> Box<dyn ScratchRegister> {
        self.clone_box()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct RegularRegister {
    in_use: bool,
    base_name: &'static str,
}

impl RegularRegister {
    pub fn new(base_name: &'static str) -> Self {
        RegularRegister { in_use: false, base_name }
    }
}

impl ScratchRegister for RegularRegister {
    fn base_name(&self) -> &'static str {
        self.base_name
    }
    fn name(&self, type_decl: &NEWTypes) -> String {
        format!("{}{}", self.base_name, type_decl.reg_suffix())
    }
    fn is_used(&self) -> bool {
        self.in_use
    }
    fn in_use(&mut self) {
        self.in_use = true
    }
    fn free(&mut self) {
        self.in_use = false
    }
}
#[derive(Debug, PartialEq, Clone)]
pub struct ArgRegister {
    pub type_decl: NEWTypes,
    pub start_idx: usize,
    pub id: usize,
    pub reg: ArgRegisterKind,
}
impl ArgRegister {
    pub fn new(
        arg_index: usize,
        type_decl: NEWTypes,
        key_counter: &mut usize,
        instr_counter: usize,
    ) -> Self {
        *key_counter += 1;
        ArgRegister {
            id: *key_counter,
            start_idx: instr_counter,
            type_decl,
            reg: ArgRegisterKind::new(arg_index),
        }
    }
    fn name(&self) -> String {
        self.reg.name(&self.type_decl)
    }
    fn base_name(&self) -> String {
        self.reg.base_name().to_string()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct ArgRegisterKind {
    in_use: bool,
    names: [&'static str; 3],
}
impl ArgRegisterKind {
    pub fn new(index: usize) -> Self {
        ArgRegisterKind { in_use: false, names: ARG_REGS[index] }
    }
}
impl ScratchRegister for ArgRegisterKind {
    fn base_name(&self) -> &'static str {
        self.names[0]
    }
    fn name(&self, type_decl: &NEWTypes) -> String {
        match type_decl {
            NEWTypes::Primitive(Types::Char) => self.names[2],
            NEWTypes::Primitive(Types::Int) | NEWTypes::Enum(..) => self.names[1],
            NEWTypes::Primitive(Types::Long) | NEWTypes::Pointer(_) | NEWTypes::Array { .. } => {
                self.names[0]
            }
            _ => unimplemented!("aggregate types are not yet implemented as function args"),
        }
        .to_string()
    }
    fn is_used(&self) -> bool {
        self.in_use
    }
    fn in_use(&mut self) {
        self.in_use = true
    }
    fn free(&mut self) {
        self.in_use = false
    }
}
