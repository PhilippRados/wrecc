use crate::common::{expr::Expr, token::Token, types::NEWTypes};

#[derive(PartialEq, Clone, Debug)]
pub enum Stmt {
    Expr(Expr),
    Declaration(Vec<DeclarationKind>),
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
    Return(Token, Option<Expr>),
    Break(Token),
    Continue(Token),
    Switch(Token, Expr, Box<Stmt>),
    Case(Token, i64, Box<Stmt>),
    Default(Token, Box<Stmt>),
}

#[derive(PartialEq, Clone, Debug)]
pub enum DeclarationKind {
    Decl(NEWTypes, Token),
    FuncDecl(NEWTypes, Token, usize, Vec<(NEWTypes, Token)>),
    Init(NEWTypes, Token, Expr),
    InitList(NEWTypes, Token, Vec<Expr>),
}
