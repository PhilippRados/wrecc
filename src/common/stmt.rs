use crate::common::{expr::Expr, token::Token, types::NEWTypes};
use std::fmt::Display;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Expr(Expr),
    DeclareVar(NEWTypes, Token),
    InitVar(NEWTypes, Token, Expr),
    Block(Token, Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Function(NEWTypes, Token, Vec<(NEWTypes, Token)>, Vec<Stmt>),
    FunctionDeclaration(NEWTypes, Token, Vec<(NEWTypes, Token)>),
    Return(Token, Option<Expr>),
}
impl Stmt {
    pub fn get_token(&self) -> &Token {
        match self {
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
