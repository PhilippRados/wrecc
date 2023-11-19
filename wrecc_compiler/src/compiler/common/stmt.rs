use crate::compiler::common::expr::*;
use crate::compiler::common::{token::Token, types::NEWTypes};

use super::expr::PrintIndent;
use std::collections::VecDeque;

#[derive(PartialEq, Clone, Debug)]
pub enum Stmt {
    Expr(Expr),
    Declaration(Vec<DeclarationKind>),
    Block(Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Do(Token, Box<Stmt>, Expr),
    For(
        Token,
        Option<Box<Stmt>>,
        Option<Expr>,
        Option<Expr>,
        Box<Stmt>,
    ),
    Function(Token, Vec<Stmt>),
    Return(Token, Option<Expr>),
    Break(Token),
    Continue(Token),
    Switch(Token, Expr, Box<Stmt>),
    Case(Token, i64, Box<Stmt>),
    Default(Token, Box<Stmt>),
    Goto(Token),
    Label(Token, Box<Stmt>),
}

#[derive(PartialEq, Clone, Debug)]
pub enum DeclarationKind {
    Decl(NEWTypes, Token, bool),
    FuncDecl(Token),
    Initializer(NEWTypes, Token, Init, bool),
}
#[derive(PartialEq, Clone, Debug)]
pub struct Init {
    pub kind: InitKind,
    pub designator: Option<VecDeque<Designator>>,
    pub token: Token,
    pub offset: i64,
}
#[derive(PartialEq, Clone, Debug)]
pub enum InitKind {
    Scalar(Expr),
    Aggr(Vec<Box<Init>>),
}
impl PrintIndent for InitKind {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            InitKind::Scalar(expr) => format!("Scalar:\n{}", indent_fmt(expr, indent_level + 1)),
            InitKind::Aggr(list) => format!(
                "Aggregate:\n{}",
                list.iter()
                    .map(|init| indent_fmt(&init.kind, indent_level + 1))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        }
    }
}
impl std::fmt::Display for InitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}

#[derive(PartialEq, Clone, Debug)]
pub struct Designator {
    pub kind: DesignatorKind,
    pub token: Token,
}

#[derive(PartialEq, Clone, Debug)]
pub enum DesignatorKind {
    Array(i64),
    Member(String),
}

impl PrintIndent for Stmt {
    fn print_indent(&self, indent_level: usize) -> String {
        match self {
            Stmt::Expr(expr) => format!("Expr:\n{}", indent_fmt(expr, indent_level + 1)),
            Stmt::Declaration(decls) => decls
                .iter()
                .map(|d| match d {
                    DeclarationKind::Initializer(_, t, init, _) => {
                        format!(
                            "Init: '{}'\n{}",
                            t.unwrap_string(),
                            indent_fmt(&init.kind, indent_level + 1)
                        )
                    }
                    DeclarationKind::Decl(_, t, _) => {
                        format!("VarDecl: '{}'", t.unwrap_string())
                    }
                    DeclarationKind::FuncDecl(t) => {
                        format!("FuncDecl: '{}'", t.unwrap_string())
                    }
                })
                .collect::<Vec<_>>()
                .join("\n"),
            Stmt::Block(body) => {
                let body = body
                    .iter()
                    .map(|s| indent_fmt(s, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("Block:\n{}", body)
            }
            Stmt::If(_, cond, then, else_branch) => format!(
                "If:\n{}\n{}\n{}",
                indent_fmt(cond, indent_level + 1),
                indent_fmt(then.as_ref(), indent_level + 1),
                display_option(
                    else_branch.as_ref().map(|t| t.as_ref()),
                    indent_level + 1,
                    false
                )
            ),
            Stmt::While(_, cond, body) => format!(
                "While:\n{}\n{}",
                indent_fmt(cond, indent_level + 1),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
            Stmt::Do(_, body, cond) => format!(
                "Do:\n{}\n{}",
                indent_fmt(cond, indent_level + 1),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
            Stmt::For(_, init, cond, inc, body) => format!(
                "For:\n{}{}{}{}",
                display_option(init.as_ref().map(|t| t.as_ref()), indent_level + 1, true),
                display_option(cond.as_ref(), indent_level + 1, true),
                display_option(inc.as_ref(), indent_level + 1, true),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
            Stmt::Function(name, body) => {
                let body = body
                    .iter()
                    .map(|s| indent_fmt(s, indent_level + 1))
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("Func: '{}'\n{}", name.unwrap_string(), body)
            }
            Stmt::Return(_, expr) => {
                let mut expr = display_option(expr.as_ref(), indent_level + 1, false);
                if !expr.is_empty() {
                    expr.insert_str(0, ":\n");
                }
                format!("Return{}", expr)
            }
            Stmt::Break(_) => "Break".to_string(),
            Stmt::Continue(_) => "Continue".to_string(),
            Stmt::Switch(_, cond, body) => format!(
                "Switch:\n{}\n{}",
                indent_fmt(cond, indent_level + 1),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
            Stmt::Case(_, value, body) => format!(
                "Case:\n{}\n{}",
                format_args!("{}Value: {}", "-".repeat(indent_level + 1), value),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
            Stmt::Default(_, body) => {
                format!("Default:\n{}", indent_fmt(body.as_ref(), indent_level + 1))
            }
            Stmt::Goto(t) => format!("Goto: '{}'", t.unwrap_string()),
            Stmt::Label(t, body) => format!(
                "Label: '{}'\n{}",
                t.unwrap_string(),
                indent_fmt(body.as_ref(), indent_level + 1)
            ),
        }
    }
}

impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}

fn display_option<T: PrintIndent>(
    object: Option<&T>,
    indent_level: usize,
    newline: bool,
) -> String {
    if let Some(object) = object {
        indent_fmt(object, indent_level) + if newline { "\n" } else { "" }
    } else {
        "".to_string()
    }
}
