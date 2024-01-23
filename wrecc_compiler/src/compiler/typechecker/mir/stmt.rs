use crate::compiler::common::types::FuncSymbol;
use crate::compiler::typechecker::mir::decl::Declarator;
use crate::compiler::typechecker::mir::expr::*;

pub enum Stmt {
    Declaration(Vec<Declarator>),
    Expr(Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    Do(Box<Stmt>, Expr),
    For(Option<Box<Stmt>>, Option<Expr>, Option<Expr>, Box<Stmt>),
    Return(FuncSymbol, Option<Expr>),
    Break,
    Continue,
    Switch(Expr, Box<Stmt>),
    Case(Box<Stmt>),
    Default(Box<Stmt>),
    Goto(FuncSymbol, String),
    Label(FuncSymbol, String, Box<Stmt>),
}
