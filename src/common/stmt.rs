use crate::common::{expr::Expr, token::Token, types::Types};

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Token, Expr),
    Expr(Expr),
    DeclareVar(Types, Token),
    InitVar(Types, Token, Expr),
    Block(Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Function(Types, Token, Vec<(Types, Token)>, Vec<Stmt>),
    Return(Token, Option<Expr>),
}
