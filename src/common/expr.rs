use crate::common::token::Token;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Binary {
        left: Box<Expr>,
        token: Token,
        right: Box<Expr>,
    },
    Unary {
        token: Token,
        right: Box<Expr>,
    },
    Grouping {
        expr: Box<Expr>,
    },
    Assign {
        name: Token,
        expr: Box<Expr>,
    },
    Logical {
        left: Box<Expr>,
        token: Token,
        right: Box<Expr>,
    },
    Call {
        left_paren: Token,
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Number(i32),
    CharLit(i8),
    Ident(Token),
}
