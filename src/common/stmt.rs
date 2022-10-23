use crate::common::{expr::Expr, token::Token, types::Types};
use std::fmt::Display;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Token, Expr),
    Expr(Expr),
    DeclareVar(Types, Token),
    InitVar(Types, Token, Expr),
    Block(Token, Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Function(Types, Token, Vec<(Types, Token)>, Vec<Stmt>),
    FunctionDeclaration(Types, Token, Vec<(Types, Token)>),
    Return(Token, Option<Expr>),
}
impl Stmt {
    pub fn get_token(&self) -> &Token {
        match self {
            Stmt::Print(t, _) => t,
            Stmt::DeclareVar(_, t) => t,
            Stmt::InitVar(_, t, _) => t,
            Stmt::Block(t, _) => t,
            Stmt::If(t, _, _, _) => t,
            Stmt::While(t, _, _) => t,
            Stmt::Function(_, t, _, _) => t,
            Stmt::FunctionDeclaration(_, t, _) => t,
            Stmt::Return(t, _) => t,
            Stmt::Expr(_) => unimplemented!(),
        }
    }
}
impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Stmt::Print(_, _) => "'print-statemnet'",
                Stmt::DeclareVar(_, _) => "'variable-declaration'",
                Stmt::InitVar(_, _, _) => "'variable-initialization'",
                Stmt::Block(_, _) => "'block-statement'",
                Stmt::If(_, _, _, _) => "'if-statement'",
                Stmt::While(_, _, _) => "'loop-statement'",
                Stmt::Function(_, _, _, _) => "'function-definition'",
                Stmt::FunctionDeclaration(_, _, _) => "'function-declaration'",
                Stmt::Return(_, _) => "'return-statement'",
                Stmt::Expr(_) => unimplemented!(),
            }
        )
    }
}
