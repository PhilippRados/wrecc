use crate::common::{token::Token, types::NEWTypes};
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
        is_global: bool,
    },
    Grouping {
        expr: Box<Expr>,
    },
    Assign {
        l_expr: Box<Expr>,
        token: Token,
        r_expr: Box<Expr>,
    },
    CompoundAssign {
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
        name: Token,
        args: Vec<Expr>,
    },
    Cast {
        token: Token,
        new_type: NEWTypes,
        direction: Option<CastDirection>,
        expr: Box<Expr>,
    },
    ScaleUp {
        by: usize,
        expr: Box<Expr>,
    },
    ScaleDown {
        shift_amount: usize,
        expr: Box<Expr>,
    },
    PostUnary {
        token: Token,
        left: Box<Expr>,
        by_amount: usize,
    },
    MemberAccess {
        token: Token,
        member: Token,
        expr: Box<Expr>,
    },
    Ternary {
        token: Token,
        cond: Box<Expr>,
        true_expr: Box<Expr>,
        false_expr: Box<Expr>,
    },
    Comma {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    SizeofType {
        value: usize,
    },
    // value gets filled in in typechecker
    SizeofExpr {
        expr: Box<Expr>,
        value: Option<usize>,
    },
    String(Token),
    Number(i64),
    CharLit(i8),
    Ident(Token),
    Nop, // works as an indicator for parser
}

#[derive(Debug, PartialEq, Clone)]
pub enum CastDirection {
    Up,
    Down,
    Equal,
}
#[derive(Debug, PartialEq, Clone)]
pub enum ValueKind {
    Lvalue,
    Rvalue,
}
#[derive(Debug, PartialEq, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub type_decl: Option<NEWTypes>,
    pub value_kind: ValueKind,
}
impl Expr {
    pub fn new(kind: ExprKind, value_kind: ValueKind) -> Self {
        Expr { type_decl: None, kind, value_kind }
    }
}
impl Display for ExprKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExprKind::Binary { left, token, right } => format!(
                    "Binary: {}\n\tleft: {}\n\tright {}",
                    token.token, left.kind, right.kind
                ),
                ExprKind::Unary { token, right, .. } =>
                    format!("Unary: {}\n\tright: {}", token.token, right.kind),
                ExprKind::Grouping { expr } => format!("Grouping:\n\t{}", expr.kind),
                ExprKind::Assign { .. } => "'assign-expression'".to_string(),
                ExprKind::Logical { token, .. } => format!("'logical-expression': {}", token.token),
                ExprKind::Call { .. } => "'call-expression'".to_string(),
                ExprKind::Cast { .. } => "'cast-expression'".to_string(),
                ExprKind::Number(_) => "'number-literal'".to_string(),
                ExprKind::CharLit(_) => "'character-literal'".to_string(),
                ExprKind::Ident(_) => "'identifier'".to_string(),
                ExprKind::ScaleUp { .. } => "'scaling-up'".to_string(),
                ExprKind::ScaleDown { .. } => "'scaling-down'".to_string(),
                ExprKind::String(token) => token.unwrap_string(),
                ExprKind::PostUnary { .. } => "'postfix-expression'".to_string(),
                ExprKind::MemberAccess { .. } => "'member-access-expression'".to_string(),
                ExprKind::Nop => "'nop'".to_string(),
                ExprKind::CompoundAssign { token, .. } =>
                    format!("'compound-assignment: {}'", token.token),
                ExprKind::Ternary { .. } => "'ternary-expression'".to_string(),
                ExprKind::Comma { .. } => "'comma-expression'".to_string(),
                ExprKind::SizeofExpr { .. } | ExprKind::SizeofType { .. } =>
                    "'sizeof-expression'".to_string(),
            }
        )
    }
}
