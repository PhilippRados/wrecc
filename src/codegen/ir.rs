use crate::codegen::register::*;
use crate::common::types::*;
use std::fmt::Display;

// Intermediate representation as an assembly instruction abstraction to simplify register allocation.
// Needs owned values so that later register transformations like type-casts don't change previous references
#[derive(Debug)]
pub enum Ir {
    // name
    GlobalDeclaration(String),
    // TODO: check if needs type or if can use reg-type
    // type, value
    GlobalInit(NEWTypes, Register),
    // label index, value
    StringDeclaration(usize, String),
    // label index
    LabelDefinition(usize),
    // label index
    Jmp(usize),
    // jump condition, label index
    JmpCond(&'static str, usize), // maybe encode conditions into enum

    Push(Register),
    Pop(Register),

    Call(String),

    // Function stuff
    FuncSetup(String),
    FuncTeardown,
    AddSp(usize),
    SubSp(usize),

    // binary operations
    Mov(Register, Register),
    Movs(Register, Register),
    Movz(Register, Register),
    Cmp(Register, Register),
    Sub(Register, Register),
    Add(Register, Register),
    Imul(Register, Register),
    Idiv(Register),

    // shift direction, reg, dest
    Shift(&'static str, Register, Register),

    Load(Register, Register),

    Set(&'static str),

    // bit operations
    Xor(Register, Register),
    Or(Register, Register),
    And(Register, Register),
    Not(Register),

    // unary
    Neg(Register),
}
impl Ir {
    pub fn get_regs(&mut self) -> (Option<&mut Register>, Option<&mut Register>) {
        match self {
            Ir::GlobalInit(_, reg) => (None, Some(reg)),
            Ir::Push(reg) => (None, Some(reg)),
            Ir::Pop(reg) => (None, Some(reg)),
            Ir::Mov(left, right)
            | Ir::Movs(left, right)
            | Ir::Movz(left, right)
            | Ir::Cmp(left, right)
            | Ir::Sub(left, right)
            | Ir::Add(left, right)
            | Ir::Imul(left, right)
            | Ir::Xor(left, right)
            | Ir::Or(left, right)
            | Ir::And(left, right)
            | Ir::Load(left, right)
            | Ir::Shift(_, left, right) => (Some(left), Some(right)),
            Ir::Neg(reg) | Ir::Not(reg) | Ir::Idiv(reg) => (None, Some(reg)),
            _ => (None, None),
        }
    }
}

impl Display for Ir {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Ir::GlobalDeclaration(name) => format!("\n\t.data\n_{}:", name),
                Ir::GlobalInit(type_decl, reg) =>
                    format!("\t.{} {}", type_decl.complete_suffix(), reg.base_name()),
                Ir::StringDeclaration(label_index, s) =>
                    format!("LS{}:\n\t.string \"{}\"", label_index, s),
                Ir::LabelDefinition(label_index) => format!("L{}:", label_index),
                Ir::Jmp(label_index) => format!("\tjmp     L{}", label_index),
                Ir::JmpCond(cond, label_index) => format!("\tj{}     L{}", cond, label_index),
                Ir::FuncSetup(name) => format!(
                    "\n\t.text\n\t.globl _{}\n_{}:\n\tpushq   %rbp\n\tmovq    %rsp, %rbp\n",
                    name, name
                ),
                Ir::FuncTeardown => String::from("\tpopq    %rbp\n\tret"),
                Ir::SubSp(value) => format!("\tsubq    ${},%rsp", value),
                Ir::AddSp(value) => format!("\taddq    ${},%rsp", value),
                Ir::Push(reg) => format!("\tpushq   {}", reg.base_name()),
                Ir::Pop(reg) => format!("\tpopq    {}", reg.base_name()),
                Ir::Call(name) => format!("\tcall    _{}", name),
                Ir::Mov(from, to) => format!(
                    "\tmov{}    {}, {}",
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Movs(from, to) => format!(
                    "\tmovs{}{}   {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Movz(from, to) => format!(
                    "\tmovz{}{}   {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Cmp(left, right) => format!(
                    "\tcmp{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Sub(left, right) => format!(
                    "\tsub{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Add(left, right) => format!(
                    "\tadd{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Imul(left, right) => format!(
                    "\timul{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Idiv(reg) => format!(
                    "\t{}\n\tidiv{} {}",
                    match reg.get_type().size() {
                        0..=7 => "cdq",
                        _ => "cqo",
                    },
                    reg.get_type().suffix(),
                    reg.name()
                ),
                Ir::Shift(direction, left, right) => format!(
                    "\tsa{}{}   {}, {}",
                    direction,
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Load(from, to) => format!(
                    "\tlea{}   {}, {}",
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Set(operator) => format!("\t{}   %al", operator),
                Ir::Xor(left, right) => format!(
                    "\txor{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Ir::Or(left, right) => format!(
                    "\tor{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Ir::And(left, right) => format!(
                    "\tand{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Ir::Not(reg) => format!("\tnot{}    {}", reg.get_type().suffix(), reg.name()),
                Ir::Neg(reg) => format!("\tneg{}    {}", reg.get_type().suffix(), reg.name()),
            }
        )
    }
}
