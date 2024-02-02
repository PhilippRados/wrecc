use crate::compiler::common::{token::Token, types::Type};
use crate::compiler::parser::hir::decl::*;
use crate::compiler::typechecker::TypeChecker;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub enum ExprKind {
    Binary {
        left: Box<ExprKind>,
        token: Token,
        right: Box<ExprKind>,
    },
    Unary {
        token: Token,
        right: Box<ExprKind>,
    },
    Grouping {
        expr: Box<ExprKind>,
    },
    Assign {
        l_expr: Box<ExprKind>,
        token: Token,
        r_expr: Box<ExprKind>,
    },
    CompoundAssign {
        l_expr: Box<ExprKind>,
        token: Token,
        r_expr: Box<ExprKind>,
    },
    Logical {
        left: Box<ExprKind>,
        token: Token,
        right: Box<ExprKind>,
    },
    Comparison {
        left: Box<ExprKind>,
        token: Token,
        right: Box<ExprKind>,
    },
    Call {
        left_paren: Token,
        name: Token,
        args: Vec<ExprKind>,
    },
    Cast {
        token: Token,
        decl_type: DeclType,
        expr: Box<ExprKind>,
    },
    PostUnary {
        token: Token,
        left: Box<ExprKind>,
    },
    MemberAccess {
        token: Token,
        member: Token,
        expr: Box<ExprKind>,
    },
    Ternary {
        token: Token,
        cond: Box<ExprKind>,
        true_expr: Box<ExprKind>,
        false_expr: Box<ExprKind>,
    },
    Comma {
        left: Box<ExprKind>,
        right: Box<ExprKind>,
    },
    SizeofType {
        decl_type: DeclType,
    },
    SizeofExpr {
        expr: Box<ExprKind>,
    },
    String(Token),
    Literal(i64, Type),
    Ident(Token),
    Nop,
}

pub trait IsZero {
    fn is_zero(&self) -> bool;
}
impl IsZero for ExprKind {
    fn is_zero(&self) -> bool {
        matches!(self, ExprKind::Literal(0, _))
    }
}

pub trait PrintIndent {
    fn print_indent(&self, indent_level: usize) -> String;
}
impl PrintIndent for ExprKind {
    fn print_indent(&self, indent_level: usize) -> String {
        match &self {
            ExprKind::Binary { left, token, right } => format!(
                "Binary: {}\n{}\n{}",
                token.kind,
                indent_fmt(left.as_ref(), indent_level + 1),
                indent_fmt(right.as_ref(), indent_level + 1)
            ),
            ExprKind::Unary { token, right, .. } => {
                format!(
                    "Unary: {}\n{}",
                    token.kind,
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
            ExprKind::Literal(n, _) => format!("Literal: {}", n),
            ExprKind::Ident(name) => format!("Ident: '{}'", name.unwrap_string()),
            ExprKind::String(token) => format!("String: '{}'", token.unwrap_string()),
            ExprKind::Logical { token, left, right } => format!(
                "Logical: {}\n{}\n{}",
                token.kind,
                indent_fmt(left.as_ref(), indent_level + 1),
                indent_fmt(right.as_ref(), indent_level + 1)
            ),
            ExprKind::Comparison { token, left, right } => format!(
                "Comparison: {}\n{}\n{}",
                token.kind,
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
            ExprKind::Cast { decl_type, expr, .. } => {
                let type_string = TypeChecker::new()
                    .parse_type(decl_type.clone())
                    .map(|ty| ty.to_string())
                    .unwrap_or("invalid type".to_string());
                format!(
                    "Cast: '{}'\n{}",
                    type_string,
                    indent_fmt(expr.as_ref(), indent_level + 1)
                )
            }
            ExprKind::PostUnary { token, left, .. } => format!(
                "PostUnary: {}\n{}",
                token.kind,
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
                    token.kind,
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
                format!(
                    "SizeofExpr:\n{}",
                    indent_fmt(expr.as_ref(), indent_level + 1)
                )
            }
            ExprKind::SizeofType { decl_type } => {
                let type_string = TypeChecker::new()
                    .parse_type(decl_type.clone())
                    .map(|ty| ty.to_string())
                    .unwrap_or("invalid type".to_string());

                format!("SizeofType: {}", type_string)
            }
            ExprKind::Nop => "Nop".to_string(),
        }
    }
}

pub fn indent_fmt<T: PrintIndent>(object: &T, indent_level: usize) -> String {
    let indent = "-".repeat(indent_level);

    format!("{}{}", indent, object.print_indent(indent_level))
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", indent_fmt(self, 0))
    }
}
