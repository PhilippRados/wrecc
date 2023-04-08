use crate::common::{expr::Expr, token::Token, types::NEWTypes};

#[derive(PartialEq, Clone, Debug)]
pub enum Stmt {
    Expr(Expr),
    DeclareVar(NEWTypes, Token),
    InitVar(NEWTypes, Token, Expr),
    InitList(NEWTypes, Token, Vec<Expr>),
    Block(Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Token, Expr, Box<Stmt>),
    Do(Token, Box<Stmt>, Expr),
    For(
        Token,
        Option<Box<Stmt>>,
        Option<Expr>,
        Option<Expr>,
        Box<Stmt>,
    ),
    Function(NEWTypes, Token, Vec<(NEWTypes, Token)>, Vec<Stmt>),
    FunctionDeclaration(),
    Return(Token, Option<Expr>),
    Break(Token),
    Continue(Token),
}
