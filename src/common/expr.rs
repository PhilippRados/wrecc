use crate::common::{token::Token, token::TokenType, types::NEWTypes, types::Types};
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
    Literal(i64),
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
    pub fn new_literal(value: i64, primitive_type: Types) -> Self {
        Expr {
            type_decl: Some(NEWTypes::Primitive(primitive_type)),
            kind: ExprKind::Literal(value),
            value_kind: ValueKind::Rvalue,
        }
    }
    // https://en.cppreference.com/w/c/language/constant_expression
    pub fn integer_const_fold(self) -> Expr {
        let fold_value: Result<i64, ExprKind> = match self.kind {
            ExprKind::Literal(n) => Ok(n),
            ExprKind::Ident(..) => {
                // if let Some(Enum) = self.type_decl {}
                Err(self.kind)
            }
            ExprKind::Binary { left, token, right } => Self::binary_fold(left, token, right),
            ExprKind::Unary { token, right, is_global } => {
                Self::unary_fold(token, right, is_global)
            }
            ExprKind::Grouping { expr } => Err(expr.integer_const_fold().kind),
            ExprKind::Logical { left, token, right } => {
                let left_fold = left.integer_const_fold();
                let right_fold = right.integer_const_fold();

                if let (ExprKind::Literal(left_fold), ExprKind::Literal(right_fold)) =
                    (&left_fold.kind, &right_fold.kind)
                {
                    Ok(match token.token {
                        TokenType::AmpAmp => {
                            if *left_fold != 0 && *right_fold != 0 {
                                1
                            } else {
                                0
                            }
                        }
                        TokenType::PipePipe => {
                            if *left_fold != 0 || *right_fold != 0 {
                                1
                            } else {
                                0
                            }
                        }
                        _ => unreachable!("not logical token"),
                    })
                } else {
                    Err(ExprKind::Logical {
                        left: Box::new(left_fold),
                        right: Box::new(right_fold),
                        token,
                    })
                }
            }
            ExprKind::Ternary { token, cond, true_expr, false_expr } => {
                let (cond_fold, true_fold, false_fold) = (
                    cond.integer_const_fold(),
                    true_expr.integer_const_fold(),
                    false_expr.integer_const_fold(),
                );
                match cond_fold.kind {
                    ExprKind::Literal(0) => Err(false_fold.kind),
                    ExprKind::Literal(_) => Err(true_fold.kind),
                    _ => Err(ExprKind::Ternary {
                        token,
                        cond: Box::new(cond_fold),
                        true_expr: Box::new(true_fold),
                        false_expr: Box::new(false_fold),
                    }),
                }
            }
            ExprKind::Cast { new_type, direction, token, expr } => {
                let right_fold = expr.integer_const_fold();
                Err(ExprKind::Cast {
                    expr: Box::new(right_fold),
                    new_type,
                    direction,
                    token,
                })
            }
            ExprKind::SizeofType { value } => Ok(value as i64),
            ExprKind::Assign { token, l_expr, r_expr } => {
                let right_fold = r_expr.integer_const_fold();
                Err(ExprKind::Assign {
                    r_expr: Box::new(right_fold),
                    l_expr,
                    token,
                })
            }
            ExprKind::CompoundAssign { token, l_expr, r_expr } => {
                let right_fold = r_expr.integer_const_fold();
                Err(ExprKind::CompoundAssign {
                    r_expr: Box::new(right_fold),
                    l_expr,
                    token,
                })
            }
            ExprKind::Comma { left, right } => {
                let left_fold = left.integer_const_fold();
                let right_fold = right.integer_const_fold();

                Err(ExprKind::Comma {
                    left: Box::new(left_fold),
                    right: Box::new(right_fold),
                })
            }
            ExprKind::Call { .. }
            | ExprKind::String(..)
            | ExprKind::MemberAccess { .. }
            | ExprKind::SizeofExpr { .. }
            | ExprKind::PostUnary { .. } => Err(self.kind),

            ExprKind::ScaleUp { .. } | ExprKind::ScaleDown { .. } | ExprKind::Nop { .. } => {
                unreachable!("not found during parsing")
            }
        };
        match fold_value {
            Ok(n) => Expr::new_literal(n, Types::Int),
            Err(kind) => Expr { kind, ..self },
        }
    }
    fn binary_fold(left: Box<Expr>, token: Token, right: Box<Expr>) -> Result<i64, ExprKind> {
        let left_fold = left.integer_const_fold();
        let right_fold = right.integer_const_fold();

        if let (ExprKind::Literal(left_fold), ExprKind::Literal(right_fold)) =
            (&left_fold.kind, &right_fold.kind)
        {
            Ok(match token.token {
                TokenType::Plus => left_fold + right_fold,
                TokenType::Minus => left_fold - right_fold,
                TokenType::Star => left_fold * right_fold,
                TokenType::Slash => left_fold / right_fold,
                TokenType::Mod => left_fold % right_fold,

                TokenType::Pipe => left_fold | right_fold,
                TokenType::Xor => left_fold ^ right_fold,
                TokenType::Amp => left_fold & right_fold,

                TokenType::BangEqual => (left_fold != right_fold).into(),
                TokenType::EqualEqual => (left_fold == right_fold).into(),

                TokenType::Greater => (left_fold > right_fold).into(),
                TokenType::GreaterEqual => (left_fold >= right_fold).into(),
                TokenType::Less => (left_fold < right_fold).into(),
                TokenType::LessEqual => (left_fold <= right_fold).into(),

                TokenType::GreaterGreater => left_fold >> right_fold,
                TokenType::LessLess => left_fold << right_fold,
                _ => unreachable!("not binary token"),
            })
        } else {
            Err(ExprKind::Binary {
                left: Box::new(left_fold),
                right: Box::new(right_fold),
                token,
            })
        }
    }
    fn unary_fold(token: Token, right: Box<Expr>, is_global: bool) -> Result<i64, ExprKind> {
        let right_fold = right.integer_const_fold();

        match (&right_fold.kind, &token.token) {
            (ExprKind::Literal(right_fold), TokenType::Bang) => {
                Ok(if *right_fold == 0 { 1 } else { 0 })
            }
            (ExprKind::Literal(right_fold), TokenType::Tilde) => Ok((!right_fold).into()),
            (ExprKind::Literal(right_fold), TokenType::Minus) => Ok(-right_fold),
            (
                _,
                TokenType::Star
                | TokenType::Amp
                | TokenType::PlusPlus
                | TokenType::MinusMinus
                | TokenType::Bang
                | TokenType::Tilde
                | TokenType::Minus,
            ) => Err(ExprKind::Unary {
                token,
                right: Box::new(right_fold),
                is_global,
            }),
            _ => unreachable!("not unary token {}", token.token),
        }
    }
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn indent_fmt(expr: &ExprKind, indent_level: usize) -> String {
            let indent = "-".repeat(indent_level);

            format!(
                "{}{}",
                indent,
                match expr {
                    ExprKind::Binary { left, token, right } => format!(
                        "Binary: {}\n{}\n{}",
                        token.token,
                        indent_fmt(&left.kind, indent_level + 1),
                        indent_fmt(&right.kind, indent_level + 1)
                    ),
                    ExprKind::Unary { token, right, .. } => {
                        format!(
                            "Unary: {}\n{}",
                            token.token,
                            indent_fmt(&right.kind, indent_level + 1)
                        )
                    }
                    ExprKind::Grouping { expr } =>
                        format!("Grouping:\n{}", indent_fmt(&expr.kind, indent_level + 1)),
                    ExprKind::Assign { l_expr, r_expr, .. } => {
                        format!(
                            "Assignment:\n{}\n{}",
                            indent_fmt(&l_expr.kind, indent_level + 1),
                            indent_fmt(&r_expr.kind, indent_level + 1)
                        )
                    }
                    ExprKind::Literal(n) => format!("Literal: {}", n),
                    ExprKind::Ident(name) => format!("Ident: {}", name.unwrap_string()),
                    ExprKind::String(token) => token.unwrap_string(),
                    ExprKind::Logical { token, left, right } => format!(
                        "Logical: {}\n{}\n{}",
                        token.token,
                        indent_fmt(&left.kind, indent_level + 1),
                        indent_fmt(&right.kind, indent_level + 1)
                    ),
                    ExprKind::Call { name, .. } => format!("FuncCall: {}", name.unwrap_string()),
                    ExprKind::Cast { new_type, expr, .. } => format!(
                        "Cast: '{}'\n{}",
                        new_type,
                        indent_fmt(&expr.kind, indent_level + 1)
                    ),
                    ExprKind::PostUnary { token, left, .. } => format!(
                        "PostUnary: {}\n{}",
                        token.token,
                        indent_fmt(&left.kind, indent_level + 1)
                    ),
                    ExprKind::MemberAccess { member, expr, .. } => format!(
                        "MemberAccess: '{}'\n{}",
                        member.unwrap_string(),
                        indent_fmt(&expr.kind, indent_level + 1),
                    ),
                    ExprKind::CompoundAssign { token, l_expr, r_expr } => {
                        format!(
                            "CompoundAssign: {}\n{}\n{}",
                            token.token,
                            indent_fmt(&l_expr.kind, indent_level + 1),
                            indent_fmt(&r_expr.kind, indent_level + 1)
                        )
                    }
                    ExprKind::Ternary { cond, true_expr, false_expr, .. } => format!(
                        "Ternary:\n{}\n{}\n{}",
                        indent_fmt(&cond.kind, indent_level + 1),
                        indent_fmt(&true_expr.kind, indent_level + 1),
                        indent_fmt(&false_expr.kind, indent_level + 1)
                    ),
                    ExprKind::Comma { left, right } => {
                        format!(
                            "Comma:\nleft: {}\nright: {}",
                            indent_fmt(&left.kind, indent_level + 1),
                            indent_fmt(&right.kind, indent_level + 1)
                        )
                    }
                    ExprKind::SizeofExpr { expr, .. } => {
                        format!("Sizeof:\n{}", indent_fmt(&expr.kind, indent_level + 1))
                    }
                    ExprKind::SizeofType { value } => format!("SizeofType: {}", value),
                    ExprKind::Nop => "Nop".to_string(),
                    ExprKind::ScaleUp { .. } => "'scaling-up'".to_string(),
                    ExprKind::ScaleDown { .. } => "'scaling-down'".to_string(),
                }
            )
        }

        writeln!(f, "{}", indent_fmt(self, 0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::scanner::Scanner;

    fn assert_fold(input: &str, expected: &str) -> NEWTypes {
        let mut scanner = Scanner::new(input);
        let tokens = scanner.scan_token().unwrap();

        let mut parser = Parser::new(tokens);
        let actual_fold = parser.expression().unwrap().integer_const_fold();

        let mut scanner = Scanner::new(expected);
        let tokens = scanner.scan_token().unwrap();

        let mut parser = Parser::new(tokens);
        let expected_fold = parser.expression().unwrap().integer_const_fold();

        assert_eq!(actual_fold, expected_fold);

        return actual_fold.type_decl.unwrap();
    }
    fn assert_fold_type(input: &str, expected: &str, expected_type: Types) {
        let actual_type = assert_fold(input, expected);
        assert_eq!(actual_type, NEWTypes::Primitive(expected_type));
    }
    // TODO: error checking in constant folding
    // fn assert_fold_error(input: &str, err: Error) {}

    #[test]
    fn bit_fold() {
        assert_fold("-8 ^ -8", "0");
        assert_fold("1 ^ -8", "-7");

        assert_fold("-8 & -8", "-8");
        assert_fold("-8 & 1", "0");

        assert_fold("-8 | -8", "-8");
        assert_fold("1 | 1", "1");
    }
    #[test]
    fn advanced_bit_fold() {
        assert_fold("~4 + !'c'", "-5");
        assert_fold("~4 ^ -'c'", "102");
    }
    #[test]
    fn bit_vs_logical() {
        assert_fold("8 & 4", "0");
        assert_fold("8 && 4", "1");

        assert_fold("0 & 3", "0");
        assert_fold("1 && -0", "0");

        assert_fold("8 | 4", "12");
        assert_fold("8 || 4", "1");

        assert_fold("0 | 3", "3");
        assert_fold("1 || -0", "1");
    }

    #[test]
    fn shift_fold() {
        assert_fold("'1' << 5", "1568");
        assert_fold("'1' >> 2", "12");
    }
    #[test]
    fn shift_fold_error() {
        // TODO: this should error because 33 > sizeof(int)
        assert_fold("-16 << 33", "0");
        assert_fold("-5 >> 2", "-1");

        // negative shift count is UB
        assert_fold("16 << -2", "0");
        assert_fold("4 >> -3", "-2147483648");

        assert_fold("-16 << -2", "0");
        assert_fold("-5 >> -1", "-1");
    }

    #[test]
    fn div_fold() {
        assert_fold("5 / 2", "-1");
        assert_fold("32 % 5", "0");

        assert_fold("-5 / 2", "-1");
        assert_fold("-32 % 5", "0");

        assert_fold("5 / -2", "-1");
        assert_fold("32 % -5", "0");

        assert_fold("-5 / -2", "-1");
        assert_fold("-32 % -5", "0");

        assert_fold("(34 / 3) * 3 + 34 % 3", "34");
    }
    #[test]
    fn div_fold_error() {
        // TODO: should error div by 0
        assert_fold("3 / 0", "-1");
        assert_fold("-5 % 0", "0");
    }

    #[test]
    fn char_fold() {
        assert_fold_type("'1' + '1'", "98", Types::Int);
    }
    #[test]
    fn type_conversions() {
        assert_fold_type("4294967296 + 1", "4294967297", Types::Long);
        assert_fold_type("'1' * 2147483648", "105226698752", Types::Long);

        assert_fold_type("'a'", "'a'", Types::Char);
        assert_fold_type("2147483648", "2147483648", Types::Long);
        assert_fold_type("-312127389", "-312127389", Types::Int);
    }

    #[test]
    fn overflow_fold_error() {
        // TODO: should overflow error
        assert_fold_type("2147483647 + 1", "4294967297", Types::Int);
    }

    #[test]
    fn const_cast() {}
}
