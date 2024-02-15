use crate::compiler::codegen::register::*;
use crate::compiler::common::types::*;
use std::fmt::Display;

// Low-level Intermediate representation as an assembly instruction abstraction to simplify register allocation.
// Needs owned values so that later register transformations like type-casts don't change previous references
#[derive(Debug)]
pub enum Lir {
    // name, if needs alignment
    GlobalDeclaration(String, bool),
    // type, value
    GlobalInit(Type, StaticRegister),
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

    Call(Register),

    // Function stuff
    // usize to allocate/deallocate stack-space
    FuncSetup(String, usize),
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

    // repeatedly store value
    Rep,

    // bit operations
    Xor(Register, Register),
    Or(Register, Register),
    And(Register, Register),
    Not(Register),

    // unary
    Neg(Register),
}
impl Lir {
    pub fn get_regs_mut(&mut self) -> (Option<&mut Register>, Option<&mut Register>) {
        match self {
            Lir::Call(reg) | Lir::Push(reg) | Lir::Pop(reg) => (None, Some(reg)),
            Lir::Mov(left, right)
            | Lir::Movs(left, right)
            | Lir::Movz(left, right)
            | Lir::Cmp(left, right)
            | Lir::Sub(left, right)
            | Lir::Add(left, right)
            | Lir::Imul(left, right)
            | Lir::Xor(left, right)
            | Lir::Or(left, right)
            | Lir::And(left, right)
            | Lir::Load(left, right)
            | Lir::Shift(_, left, right) => (Some(left), Some(right)),
            Lir::Neg(reg) | Lir::Not(reg) | Lir::Idiv(reg) => (None, Some(reg)),
            // global initializer can only have static-registers and no temporaries
            Lir::GlobalInit(..) => (None, None),
            _ => (None, None),
        }
    }
    // only used in unit-tests
    #[allow(unused)]
    pub fn get_regs(&self) -> (Option<&Register>, Option<&Register>) {
        match self {
            Lir::Call(reg) | Lir::Push(reg) | Lir::Pop(reg) => (None, Some(reg)),
            Lir::Mov(left, right)
            | Lir::Movs(left, right)
            | Lir::Movz(left, right)
            | Lir::Cmp(left, right)
            | Lir::Sub(left, right)
            | Lir::Add(left, right)
            | Lir::Imul(left, right)
            | Lir::Xor(left, right)
            | Lir::Or(left, right)
            | Lir::And(left, right)
            | Lir::Load(left, right)
            | Lir::Shift(_, left, right) => (Some(left), Some(right)),
            Lir::Neg(reg) | Lir::Not(reg) | Lir::Idiv(reg) => (None, Some(reg)),
            Lir::GlobalInit(..) => (None, None),
            _ => (None, None),
        }
    }
}

pub fn maybe_prefix_underscore(label: &String) -> String {
    if cfg!(target_os = "macos") {
        format!("_{}", label)
    } else {
        label.to_string()
    }
}

impl Display for Lir {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Lir::GlobalDeclaration(name, is_pointer) => format!(
                    "\n\t.data\n{}{}:",
                    if *is_pointer { "\t.align 4\n" } else { "" },
                    maybe_prefix_underscore(name)
                ),
                Lir::GlobalInit(type_decl, reg) =>
                    format!("\t.{} {}", type_decl.complete_suffix(), reg.name()),
                Lir::StringDeclaration(label_index, s) =>
                    format!("LS{}:\n\t.string \"{}\"", label_index, s),
                Lir::LabelDefinition(label_index) => format!("L{}:", label_index),
                Lir::Jmp(label_index) => format!("\tjmp     L{}", label_index),
                Lir::JmpCond(cond, label_index) => format!("\tj{}     L{}", cond, label_index),
                Lir::FuncSetup(name, stack_size) => {
                    let mut result = format!(
                        "\n\t.text\n\t.globl {}\n{}:\n\tpushq   %rbp\n\tmovq    %rsp, %rbp\n",
                        maybe_prefix_underscore(name),
                        maybe_prefix_underscore(name)
                    );
                    // have to keep stack 16B aligned
                    if *stack_size > 0 {
                        let size = format!(
                            "\tsubq    ${},%rsp\n",
                            crate::compiler::typechecker::align_by(*stack_size, 16)
                        );
                        result.push_str(&size);
                    }
                    result
                }
                Lir::FuncTeardown(stack_size) => {
                    match stack_size {
                        0 => String::from("\tpopq    %rbp\n\tret"),
                        n => format!(
                            "\taddq    ${},%rsp\n\tpopq    %rbp\n\tret",
                            crate::compiler::typechecker::align_by(*n, 16)
                        ),
                    }
                }
                Lir::SubSp(value) => format!("\tsubq    ${},%rsp", value),
                Lir::AddSp(value) => format!("\taddq    ${},%rsp", value),
                Lir::Push(reg) => format!("\tpushq   {}", reg.base_name()),
                Lir::Pop(reg) => format!("\tpopq    {}", reg.base_name()),
                Lir::Call(reg) => format!(
                    "\tcall    {}{}",
                    if !matches!(reg, Register::Label(_)) {
                        "*"
                    } else {
                        ""
                    },
                    reg.base_name()
                ),
                Lir::Mov(from, to) => format!(
                    "\tmov{}    {}, {}",
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Lir::Movs(from, to) => format!(
                    "\tmovs{}{}  {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Lir::Movz(from, to) => format!(
                    "\tmovz{}{}  {}, {}",
                    from.get_type().suffix(),
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Lir::Cmp(left, right) => format!(
                    "\tcmp{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Lir::Sub(left, right) => format!(
                    "\tsub{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Lir::Add(left, right) => format!(
                    "\tadd{}    {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Lir::Imul(left, right) => format!(
                    "\timul{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Lir::Idiv(reg) => format!(
                    "\t{}\n\tidiv{}   {}",
                    match reg.get_type().size() {
                        0..=7 => "cdq",
                        _ => "cqo",
                    },
                    reg.get_type().suffix(),
                    reg.name()
                ),
                Lir::Shift(direction, left, right) => format!(
                    "\tsa{}{}    {}, {}",
                    direction,
                    right.get_type().suffix(),
                    left.name(),
                    right.name()
                ),
                Lir::Load(from, to) => format!(
                    "\tlea{}    {}, {}",
                    to.get_type().suffix(),
                    from.name(),
                    to.name()
                ),
                Lir::Set(operator) => format!("\t{}   %al", operator),
                Lir::Xor(left, right) => format!(
                    "\txor{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Lir::Or(left, right) => format!(
                    "\tor{}     {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Lir::And(left, right) => format!(
                    "\tand{}   {}, {}",
                    right.get_type().suffix(),
                    left.name(),
                    right.name(),
                ),
                Lir::Rep => {
                    "\trep     stosb".to_string()
                }
                Lir::Not(reg) => format!("\tnot{}    {}", reg.get_type().suffix(), reg.name()),
                Lir::Neg(reg) => format!("\tneg{}    {}", reg.get_type().suffix(), reg.name()),
                Lir::SaveRegs | Lir::RestoreRegs =>
                    unreachable!("will be replaced in register-allocation"),
            }
        )
    }
}
