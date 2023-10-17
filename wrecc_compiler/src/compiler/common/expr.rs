use crate::compiler::common::{token::*, types::*};
use std::fmt;

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
    Comparison {
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
    Literal(i64),
    Ident(Token),
    Nop,
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

pub trait PrintIndent {
    fn print_indent(&self, indent_level: usize) -> String;
}
impl PrintIndent for Expr {
    fn print_indent(&self, indent_level: usize) -> String {
        match &self.kind {
            ExprKind::Binary { left, token, right } => format!(
                "Binary: {}\n{}\n{}",
                token.token,
                indent_fmt(left.as_ref(), indent_level + 1),
                indent_fmt(right.as_ref(), indent_level + 1)
            ),
            ExprKind::Unary { token, right, .. } => {
                format!(
                    "Unary: {}\n{}",
                    token.token,
                    indent_fmt(right.as_ref(), indent_level + 1)
                )
            }
            ExprKind::Grouping { expr } => {
                format!("Grouping:\n{}", indent_fmt(expr.as_ref(), indent_level + 1))
            }
            ExprKind::Assign { l_expr, r_expr, .. } => {
                format!(
                    "Assignment:\n{}\n{}",
                    indent_fmt(l_expr.as_ref(), indent_level + 1),
                    indent_fmt(r_expr.as_ref(), indent_level + 1)
                )
            }
            ExprKind::Literal(n) => format!("Literal: {}", n),
            ExprKind::Ident(name) => format!("Ident: '{}'", name.unwrap_string()),
            ExprKind::String(token) => format!("String: '{}'", token.unwrap_string()),
            ExprKind::Logical { token, left, right } => format!(
                "Logical: {}\n{}\n{}",
                token.token,
                indent_fmt(left.as_ref(), indent_level + 1),
                indent_fmt(right.as_ref(), indent_level + 1)
            ),
            ExprKind::Comparison { token, left, right } => format!(
                "Comparison: {}\n{}\n{}",
                token.token,
                indent_fmt(left.as_ref(), indent_level + 1),
                indent_fmt(right.as_ref(), indent_level + 1)
            ),
            ExprKind::Call { name, args, .. } => {
                let mut args: String = args
                    .iter()
                    .map(|arg| indent_fmt(arg, indent_level + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                if !args.is_empty() {
                    args.insert(0, '\n');
                }
                format!("FuncCall: '{}'{}", name.unwrap_string(), args)
            }
            ExprKind::Cast { new_type, expr, .. } => format!(
                "Cast: '{}'\n{}",
                new_type,
                indent_fmt(expr.as_ref(), indent_level + 1)
            ),
            ExprKind::PostUnary { token, left, .. } => format!(
                "PostUnary: {}\n{}",
                token.token,
                indent_fmt(left.as_ref(), indent_level + 1)
            ),
            ExprKind::MemberAccess { member, expr, .. } => format!(
                "MemberAccess: '{}'\n{}",
                member.unwrap_string(),
                indent_fmt(expr.as_ref(), indent_level + 1),
            ),
            ExprKind::CompoundAssign { token, l_expr, r_expr } => {
                format!(
                    "CompoundAssign: {}\n{}\n{}",
                    token.token,
                    indent_fmt(l_expr.as_ref(), indent_level + 1),
                    indent_fmt(r_expr.as_ref(), indent_level + 1)
                )
            }
            ExprKind::Ternary { cond, true_expr, false_expr, .. } => format!(
                "Ternary:\n{}\n{}\n{}",
                indent_fmt(cond.as_ref(), indent_level + 1),
                indent_fmt(true_expr.as_ref(), indent_level + 1),
                indent_fmt(false_expr.as_ref(), indent_level + 1)
            ),
            ExprKind::Comma { left, right } => {
                format!(
                    "Comma:\nleft: {}\nright: {}",
                    indent_fmt(left.as_ref(), indent_level + 1),
                    indent_fmt(right.as_ref(), indent_level + 1)
                )
            }
            ExprKind::SizeofExpr { expr, .. } => {
                format!("Sizeof:\n{}", indent_fmt(expr.as_ref(), indent_level + 1))
            }
            ExprKind::SizeofType { value } => format!("SizeofType: {}", value),
            ExprKind::Nop => "Nop".to_string(),
            ExprKind::ScaleUp { .. } => "'scaling-up'".to_string(),
            ExprKind::ScaleDown { .. } => "'scaling-down'".to_string(),
        }
    }
}

pub fn indent_fmt<T: PrintIndent>(object: &T, indent_level: usize) -> String {
    let indent = "-".repeat(indent_level);

    format!("{}{}", indent, object.print_indent(indent_level))
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}
