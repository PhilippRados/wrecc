use crate::common::{token::Token, types::Types};

#[derive(Debug, PartialEq, Clone)]
pub enum ExprKind {
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
    Cast {
        expr: Box<Expr>,
    },
    Number(i32),
    CharLit(i8),
    Ident(Token),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub type_decl: Option<Types>,
}
impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Expr {
            type_decl: None,
            kind,
        }
    }
}
