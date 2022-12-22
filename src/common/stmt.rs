use crate::common::{expr::Expr, token::Token, types::NEWTypes};
use std::fmt::Display;

#[derive(PartialEq, Clone, Debug)]
pub enum Stmt {
    Expr(Expr),
    // bool is to indicate if global or not
    DeclareVar(NEWTypes, Token, bool),
    InitVar(NEWTypes, Token, Expr, bool),
    InitList(NEWTypes, Token, Vec<Expr>, bool),
    Block(Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Function(NEWTypes, Token, Vec<(NEWTypes, Token)>, Vec<Stmt>),
    FunctionDeclaration(NEWTypes, Token, Vec<(NEWTypes, Token)>),
    Return(Token, Option<Expr>),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Stmt::DeclareVar(..) => "'variable-declaration'",
                Stmt::InitVar(..) => "'variable-initialization'",
                Stmt::Block(..) => "'block-statement'",
                Stmt::If(..) => "'if-statement'",
                Stmt::While(..) => "'loop-statement'",
                Stmt::Function(..) => "'function-definition'",
                Stmt::FunctionDeclaration(..) => "'function-declaration'",
                Stmt::Return(..) => "'return-statement'",
                Stmt::InitList(..) => "'initializer-list'",
                Stmt::Expr(_) => unimplemented!(),
            }
        )
    }
}
