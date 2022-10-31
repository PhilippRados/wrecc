use crate::common::{token::Token, types::Types};
use std::fmt::Display;

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
        l_expr: Box<Expr>,
        r_expr: Box<Expr>,
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
    CastUp {
        expr: Box<Expr>,
    },
    CastDown {
        expr: Box<Expr>,
    },
    Number(i32),
    CharLit(i8),
    Ident(Token),
}
#[derive(Debug, PartialEq, Clone)]
pub enum ValueKind {
    Lvalue,
    Rvalue,
}
#[derive(Debug, PartialEq, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub type_decl: Option<Types>,
    pub value_kind: ValueKind,
}
impl Expr {
    pub fn new(kind: ExprKind, value_kind: ValueKind) -> Self {
        Expr {
            type_decl: None,
            kind,
            value_kind,
        }
    }
}
impl Display for ExprKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExprKind::Binary {
                    left: _,
                    token,
                    right: _,
                } => format!("'binary-expression': {}", token.token),
                ExprKind::Unary { token, right: _ } =>
                    format!("'unary-expression': {}", token.token),
                ExprKind::Grouping { expr: _ } => "'grouping-expression'".to_string(),
                ExprKind::Assign {
                    l_expr: _,
                    r_expr: _,
                } => "'assign-expression'".to_string(),
                ExprKind::Logical {
                    left: _,
                    token,
                    right: _,
                } => format!("'logical-expression': {}", token.token),
                ExprKind::Call {
                    left_paren: _,
                    callee: _,
                    args: _,
                } => "'call-expression'".to_string(),
                ExprKind::CastUp { expr: _ } | ExprKind::CastDown { expr: _ } =>
                    "'cast-expression'".to_string(),
                ExprKind::Number(_) => "'number-literal'".to_string(),
                ExprKind::CharLit(_) => "'character-literal'".to_string(),
                ExprKind::Ident(_) => "'identifier'".to_string(),
            }
        )
    }
}
