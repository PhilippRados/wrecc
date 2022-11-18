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
        token: Token,
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
    ScaleUp {
        by_amount: usize,
        expr: Box<Expr>,
    },
    ScaleDown {
        by_amount: usize,
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
                ExprKind::Binary { token, .. } => format!("'binary-expression': {}", token.token),
                ExprKind::Unary { token, .. } => format!("'unary-expression': {}", token.token),
                ExprKind::Grouping { .. } => "'grouping-expression'".to_string(),
                ExprKind::Assign { .. } => "'assign-expression'".to_string(),
                ExprKind::Logical { token, .. } => format!("'logical-expression': {}", token.token),
                ExprKind::Call { .. } => "'call-expression'".to_string(),
                ExprKind::CastUp { .. } | ExprKind::CastDown { .. } =>
                    "'cast-expression'".to_string(),
                ExprKind::Number(_) => "'number-literal'".to_string(),
                ExprKind::CharLit(_) => "'character-literal'".to_string(),
                ExprKind::Ident(_) => "'identifier'".to_string(),
                ExprKind::ScaleUp { .. } => "'scaling-up'".to_string(),
                ExprKind::ScaleDown { .. } => "'scaling-down'".to_string(),
            }
        )
    }
}
