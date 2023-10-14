use crate::common::{token::*, types::*};
use crate::wrecc_codegen::register::*;
use std::fmt::Display;

// Intermediate representation as an assembly instruction abstraction to simplify register allocation.
// Needs owned values so that later register transformations like type-casts don't change previous references
#[derive(Debug)]
pub enum Ir {
    // name
    GlobalDeclaration(String),
    // type, value
    GlobalInit(NEWTypes, StaticRegister),
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
    // usize to allocate/deallocate stack-space
    FuncSetup(Token, usize),
    FuncTeardown(usize),
    SaveRegs,
    RestoreRegs,
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
    pub fn get_regs_mut(&mut self) -> (Option<&mut Register>, Option<&mut Register>) {
        match self {
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
            // global initializer can only have static-registers and no temporaries
            Ir::GlobalInit(..) => (None, None),
            _ => (None, None),
        }
    }
    // only used in unit-tests
    #[allow(unused)]
    pub fn get_regs(&self) -> (Option<&Register>, Option<&Register>) {
        match self {
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
            Ir::GlobalInit(..) => (None, None),
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
                    format!("\t.{} {}", type_decl.complete_suffix(), reg.name()),
                Ir::StringDeclaration(label_index, s) =>
                    format!("LS{}:\n\t.string \"{}\"", label_index, s),
                Ir::LabelDefinition(label_index) => format!("L{}:", label_index),
                Ir::Jmp(label_index) => format!("\tjmp     L{}", label_index),
                Ir::JmpCond(cond, label_index) => format!("\tj{}     L{}", cond, label_index),
                Ir::FuncSetup(name, stack_size) => {
                    let mut result = format!(
                        "\n\t.text\n\t.globl _{}\n_{}:\n\tpushq   %rbp\n\tmovq    %rsp, %rbp\n",
                        name.unwrap_string(),
                        name.unwrap_string()
                    );
                    // have to keep stack 16B aligned
                    if *stack_size > 0 {
                        let size = format!(
                            "\tsubq    ${},%rsp\n",
                            crate::typechecker::align_by(*stack_size, 16)
                        );
                        result.push_str(&size);
                    }
                    result
                }
                Ir::FuncTeardown(stack_size) => {
                    match stack_size {
                        0 => String::from("\tpopq    %rbp\n\tret"),
                        n => format!(
                            "\taddq    ${},%rsp\n\tpopq    %rbp\n\tret",
                            crate::typechecker::align_by(*n, 16)
                        ),
                    }
                }
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
                    "\tmovs{}{}  {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Movz(from, to) => format!(
                    "\tmovz{}{}  {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Ir::Cmp(left, right) => format!(
                    "\tcmp{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Sub(left, right) => format!(
                    "\tsub{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Add(left, right) => format!(
                    "\tadd{}    {}, {}",
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
                    "\t{}\n\tidiv{}   {}",
                    match reg.get_type().size() {
                        0..=7 => "cdq",
                        _ => "cqo",
                    },
                    reg.get_type().suffix(),
                    reg.name()
                ),
                Ir::Shift(direction, left, right) => format!(
                    "\tsa{}{}    {}, {}",
                    direction,
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Ir::Load(from, to) => format!(
                    "\tlea{}    {}, {}",
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
                    "\tor{}     {}, {}",
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
                Ir::SaveRegs | Ir::RestoreRegs =>
                    unreachable!("will be replaced in register-allocation"),
            }
        )
    }
}
