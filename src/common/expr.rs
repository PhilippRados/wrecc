use crate::codegen::register::*;
use crate::common::{environment::*, error::*, token::*, types::*};
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
    pub fn new_literal(value: i64, primitive_type: Types) -> Self {
        Expr {
            type_decl: Some(NEWTypes::Primitive(primitive_type)),
            kind: ExprKind::Literal(value),
            value_kind: ValueKind::Rvalue,
        }
    }
    // https://en.cppreference.com/w/c/language/constant_expression
    pub fn integer_const_fold(self, env: &Scope) -> Result<Expr, Error> {
        match self.kind {
            ExprKind::Literal(_) => Ok(self),
            ExprKind::Ident(token) => {
                // if variable is known at compile time then foldable
                // is only enum-constant
                if let Ok((
                    Symbols::Variable(SymbolInfo {
                        reg: Some(Register::Literal(n, _)),
                        type_decl,
                        ..
                    }),
                    _,
                )) = env.get_symbol(&token)
                {
                    Ok(Expr {
                        kind: ExprKind::Literal(n),
                        type_decl: Some(type_decl),
                        value_kind: self.value_kind,
                    })
                } else {
                    Ok(Expr {
                        kind: ExprKind::Ident(token),
                        type_decl: self.type_decl,
                        value_kind: self.value_kind,
                    })
                }
            }
            ExprKind::Binary { left, token, right } => {
                // TODO: fix passing value_kind and type_decl
                Self::binary_fold(left, token, right, env, self.value_kind, self.type_decl)
            }
            ExprKind::Unary { token, right, is_global } => Self::unary_fold(
                token,
                right,
                is_global,
                env,
                self.value_kind,
                self.type_decl,
            ),

            ExprKind::Logical { left, token, right } => {
                Self::logical_fold(token, left, right, env, self.value_kind, self.type_decl)
            }
            ExprKind::Cast { new_type, direction, token, expr } => Self::const_cast(
                token,
                new_type,
                direction,
                expr,
                env,
                self.value_kind,
                self.type_decl,
            ),
            ExprKind::Grouping { expr } => expr.integer_const_fold(env),
            ExprKind::Ternary { token, cond, true_expr, false_expr } => {
                let (cond_fold, true_fold, false_fold) = (
                    cond.integer_const_fold(env)?,
                    true_expr.integer_const_fold(env)?,
                    false_expr.integer_const_fold(env)?,
                );
                Ok(match (&cond_fold.kind, &true_fold.kind, &false_fold.kind) {
                    (ExprKind::Literal(0), _, ExprKind::Literal(_)) => false_fold,
                    (ExprKind::Literal(0), ..) => false_fold,
                    (ExprKind::Literal(_), ExprKind::Literal(_), _) => true_fold,
                    (ExprKind::Literal(_), ..) => true_fold,
                    _ => Expr {
                        kind: ExprKind::Ternary {
                            token,
                            cond: Box::new(cond_fold),
                            true_expr: Box::new(true_fold),
                            false_expr: Box::new(false_fold),
                        },
                        ..self
                    },
                })
            }
            ExprKind::SizeofType { value } => {
                Ok(Expr::new_literal(value as i64, integer_type(value as i64)))
            }
            ExprKind::Assign { token, l_expr, r_expr } => {
                let right_fold = r_expr.integer_const_fold(env)?;
                Ok(Expr {
                    kind: ExprKind::Assign {
                        r_expr: Box::new(right_fold),
                        l_expr,
                        token,
                    },
                    ..self
                })
            }
            ExprKind::CompoundAssign { token, l_expr, r_expr } => {
                let right_fold = r_expr.integer_const_fold(env)?;
                Ok(Expr {
                    kind: ExprKind::CompoundAssign {
                        r_expr: Box::new(right_fold),
                        l_expr,
                        token,
                    },
                    ..self
                })
            }
            ExprKind::Comma { left, right } => {
                let left_fold = left.integer_const_fold(env)?;
                let right_fold = right.integer_const_fold(env)?;

                Ok(Expr {
                    kind: ExprKind::Comma {
                        left: Box::new(left_fold),
                        right: Box::new(right_fold),
                    },
                    ..self
                })
            }
            ExprKind::Call { .. }
            | ExprKind::String(..)
            | ExprKind::MemberAccess { .. }
            | ExprKind::SizeofExpr { .. }
            | ExprKind::PostUnary { .. } => Ok(self),

            ExprKind::ScaleUp { .. } | ExprKind::ScaleDown { .. } | ExprKind::Nop { .. } => {
                unreachable!("not found during parsing")
            }
        }
    }
    fn binary_fold(
        left: Box<Expr>,
        token: Token,
        right: Box<Expr>,
        env: &Scope,
        value_kind: ValueKind,
        type_decl: Option<NEWTypes>,
    ) -> Result<Expr, Error> {
        let (left_fold, right_fold) = (
            left.integer_const_fold(env)?,
            right.integer_const_fold(env)?,
        );

        if let (ExprKind::Literal(left), ExprKind::Literal(right)) =
            (&left_fold.kind, &right_fold.kind)
        {
            let (left_type, right_type) =
                (left_fold.type_decl.unwrap(), right_fold.type_decl.unwrap());

            match token.token {
                TokenType::Plus => Self::literal_type(
                    token,
                    left_type,
                    right_type,
                    i64::overflowing_add(*left, *right),
                ),
                TokenType::Minus => Self::literal_type(
                    token,
                    left_type,
                    right_type,
                    i64::overflowing_sub(*left, *right),
                ),
                TokenType::Star => Self::literal_type(
                    token,
                    left_type,
                    right_type,
                    i64::overflowing_mul(*left, *right),
                ),
                TokenType::Slash | TokenType::Mod => {
                    Self::div_fold(token, left_type, right_type, *left, *right)
                }
                TokenType::GreaterGreater | TokenType::LessLess => {
                    Self::shift_fold(token, left_type, *left, *right)
                }

                TokenType::Pipe => {
                    Self::literal_type(token, left_type, right_type, (left | right, false))
                }
                TokenType::Xor => {
                    Self::literal_type(token, left_type, right_type, (left ^ right, false))
                }
                TokenType::Amp => {
                    Self::literal_type(token, left_type, right_type, (left & right, false))
                }

                TokenType::BangEqual => Ok(Expr::new_literal((left != right).into(), Types::Int)),
                TokenType::EqualEqual => Ok(Expr::new_literal((left == right).into(), Types::Int)),

                TokenType::Greater => Ok(Expr::new_literal((left > right).into(), Types::Int)),
                TokenType::GreaterEqual => {
                    Ok(Expr::new_literal((left >= right).into(), Types::Int))
                }
                TokenType::Less => Ok(Expr::new_literal((left < right).into(), Types::Int)),
                TokenType::LessEqual => Ok(Expr::new_literal((left <= right).into(), Types::Int)),

                _ => unreachable!("not binary token"),
            }
        } else {
            Ok(Expr {
                kind: ExprKind::Binary {
                    left: Box::new(left_fold),
                    right: Box::new(right_fold),
                    token,
                },
                value_kind,
                type_decl,
            })
        }
    }
    fn shift_fold(token: Token, left_type: NEWTypes, left: i64, right: i64) -> Result<Expr, Error> {
        // result type is only dependant on left operand
        let left_type = if left_type.size() < Types::Int.size() {
            NEWTypes::Primitive(Types::Int)
        } else {
            left_type
        };
        if right < 0 {
            return Err(Error::new(&token, ErrorKind::NegativeShift));
        }

        let (value, overflow) = match token.token {
            TokenType::GreaterGreater => i64::overflowing_shr(left, right as u32),
            TokenType::LessLess => i64::overflowing_shl(left, right as u32),
            _ => unreachable!("not shift operation"),
        };

        if overflow || Self::type_overflow(value, &left_type) {
            Err(Error::new(&token, ErrorKind::IntegerOverflow(left_type)))
        } else {
            Ok(Expr {
                kind: ExprKind::Literal(value),
                type_decl: Some(left_type),
                value_kind: ValueKind::Rvalue,
            })
        }
    }
    fn div_fold(
        token: Token,
        left_type: NEWTypes,
        right_type: NEWTypes,
        left: i64,
        right: i64,
    ) -> Result<Expr, Error> {
        if right == 0 {
            return Err(Error::new(&token, ErrorKind::DivideByZero));
        }

        let operation = match token.token {
            TokenType::Slash => i64::overflowing_div(left, right),
            TokenType::Mod => i64::overflowing_rem(left, right),
            _ => unreachable!("not shift operation"),
        };
        Self::literal_type(token, left_type, right_type, operation)
    }
    fn literal_type(
        token: Token,
        left_type: NEWTypes,
        right_type: NEWTypes,
        value: (i64, bool),
    ) -> Result<Expr, Error> {
        let result_type = if left_type.size() > right_type.size() {
            left_type
        } else {
            right_type
        };
        let result_type = if result_type.size() < Types::Int.size() {
            NEWTypes::Primitive(Types::Int)
        } else {
            result_type
        };

        // calculation can overflow or type from literal can overflow
        if value.1 || Self::type_overflow(value.0, &result_type) {
            Err(Error::new(&token, ErrorKind::IntegerOverflow(result_type)))
        } else {
            Ok(Expr {
                kind: ExprKind::Literal(value.0),
                type_decl: Some(result_type),
                value_kind: ValueKind::Rvalue,
            })
        }
    }
    fn type_overflow(value: i64, type_decl: &NEWTypes) -> bool {
        let primitive_type = type_decl.get_primitive().unwrap();
        (value > primitive_type.max()) || ((value) < primitive_type.min())
    }

    fn unary_fold(
        token: Token,
        right: Box<Expr>,
        is_global: bool,
        env: &Scope,
        value_kind: ValueKind,
        type_decl: Option<NEWTypes>,
    ) -> Result<Expr, Error> {
        let right_fold = right.integer_const_fold(env)?;
        let right_type = right_fold.type_decl.clone().unwrap();

        Ok(match (&right_fold.kind, &token.token) {
            (ExprKind::Literal(right_fold), TokenType::Bang) => {
                Expr::new_literal(if *right_fold == 0 { 1 } else { 0 }, Types::Int)
            }
            (ExprKind::Literal(right_fold), TokenType::Tilde) => {
                // TODO: since unary only has one type => fix passing same type twice
                return Self::literal_type(
                    token,
                    right_type.clone(),
                    right_type,
                    (!right_fold, false),
                );
            }
            (ExprKind::Literal(right_fold), TokenType::Minus) => {
                return Self::literal_type(
                    token,
                    right_type.clone(),
                    right_type,
                    right_fold.overflowing_neg(),
                );
            }
            (..) => Expr {
                kind: ExprKind::Unary {
                    token,
                    right: Box::new(right_fold),
                    is_global,
                },
                value_kind,
                type_decl,
            },
        })
    }
    fn logical_fold(
        token: Token,
        left: Box<Expr>,
        right: Box<Expr>,
        env: &Scope,
        value_kind: ValueKind,
        type_decl: Option<NEWTypes>,
    ) -> Result<Expr, Error> {
        let left_fold = left.integer_const_fold(env)?;
        let right_fold = right.integer_const_fold(env)?;

        Ok(match token.token {
            TokenType::AmpAmp => match (&left_fold.kind, &right_fold.kind) {
                (ExprKind::Literal(0), _) | (_, ExprKind::Literal(0)) => {
                    Expr::new_literal(0, Types::Int)
                }
                (ExprKind::Literal(left), ExprKind::Literal(right))
                    if *left != 0 && *right != 0 =>
                {
                    Expr::new_literal(1, Types::Int)
                }
                _ => Expr {
                    kind: ExprKind::Logical {
                        left: Box::new(left_fold),
                        right: Box::new(right_fold),
                        token,
                    },
                    value_kind,
                    type_decl,
                },
            },

            TokenType::PipePipe => match (&left_fold.kind, &right_fold.kind) {
                (ExprKind::Literal(n), _) | (_, ExprKind::Literal(n)) if *n != 0 => {
                    Expr::new_literal(1, Types::Int)
                }
                (ExprKind::Literal(left), ExprKind::Literal(right))
                    if *left == 0 && *right == 0 =>
                {
                    Expr::new_literal(0, Types::Int)
                }
                _ => Expr {
                    kind: ExprKind::Logical {
                        left: Box::new(left_fold),
                        right: Box::new(right_fold),
                        token,
                    },
                    value_kind,
                    type_decl,
                },
            },
            _ => unreachable!("not logical token"),
        })
    }
    fn const_cast(
        token: Token,
        new_type: NEWTypes,
        direction: Option<CastDirection>,
        expr: Box<Expr>,
        env: &Scope,
        value_kind: ValueKind,
        type_decl: Option<NEWTypes>,
    ) -> Result<Expr, Error> {
        let right_fold = expr.integer_const_fold(env)?;

        if let ExprKind::Literal(right) = right_fold.kind {
            let (n, new_type) =
                Self::valid_cast(token, right_fold.type_decl.unwrap(), new_type, right)?;
            Ok(Expr {
                kind: ExprKind::Literal(n),
                type_decl: Some(new_type),
                value_kind,
            })
        } else {
            Ok(Expr {
                kind: ExprKind::Cast {
                    expr: Box::new(right_fold),
                    new_type,
                    direction,
                    token,
                },
                value_kind,
                type_decl,
            })
        }
    }
    fn valid_cast(
        token: Token,
        old_type: NEWTypes,
        new_type: NEWTypes,
        right_fold: i64,
    ) -> Result<(i64, NEWTypes), Error> {
        let result = match (&old_type, &new_type) {
            (old, new) if !old.is_scalar() || !new.is_scalar() => None,
            (_, NEWTypes::Primitive(Types::Char)) => Some(right_fold as i8 as i64),
            (_, NEWTypes::Primitive(Types::Int) | NEWTypes::Enum(..)) => {
                Some(right_fold as i32 as i64)
            }
            (_, NEWTypes::Primitive(Types::Long) | NEWTypes::Pointer(_)) => Some(right_fold),
            _ => None,
        };

        if let Some(result) = result {
            Ok((result, new_type))
        } else {
            Err(Error::new(
                &token,
                ErrorKind::InvalidConstCast(old_type, new_type),
            ))
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
        let actual_fold = parser
            .expression()
            .unwrap()
            .integer_const_fold(&Scope::new());

        let mut scanner = Scanner::new(expected);
        let tokens = scanner.scan_token().unwrap();

        let mut parser = Parser::new(tokens);
        let expected_fold = parser
            .expression()
            .unwrap()
            .integer_const_fold(&Scope::new());

        assert_eq!(actual_fold, expected_fold);

        return actual_fold.unwrap().type_decl.unwrap();
    }
    fn assert_fold_type(input: &str, expected: &str, expected_type: Types) {
        let actual_type = assert_fold(input, expected);
        assert_eq!(actual_type, NEWTypes::Primitive(expected_type));
    }
    macro_rules! assert_fold_error {
        ($input:expr,$expected_err:pat) => {
            let mut scanner = Scanner::new($input);
            let tokens = scanner.scan_token().unwrap();

            let mut parser = Parser::new(tokens);
            let Err(actual_fold) = parser.expression().unwrap().integer_const_fold(&Scope::new()) else {
                                                            panic!("should error on error test");
                                                        };

            assert!(
                matches!(actual_fold.kind, $expected_err),
                "expected: {}, found: {:?}",
                stringify!($expected_err),
                actual_fold
            );
        };
    }

    #[test]
    fn bit_fold() {
        assert_fold("-8 ^ -8", "0");
        assert_fold("1 ^ -8", "-7");

        assert_fold("-8 & -8", "-8");
        assert_fold("-8 & 1", "0");

        assert_fold("-8 | -8", "-8");
        assert_fold("1 | 1", "1");

        assert_fold_type("~0", "-1", Types::Int);
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
    fn comp_fold() {
        assert_fold("1 == 0", "0");
        assert_fold("-2 == -2", "1");

        assert_fold("3 != -2", "1");
        assert_fold("3 != 3", "0");

        assert_fold("3 > -2", "1");
        assert_fold("3 > 3", "0");

        assert_fold("3 >= -2", "1");
        assert_fold("3 >= 3", "1");

        assert_fold("'c' <= -2", "0");
        assert_fold("3 <= -2", "0");
    }

    #[test]
    fn shift_fold() {
        assert_fold("'1' << 5", "1568");
        assert_fold("'1' >> 2", "12");

        assert_fold_type("1 << (long)12", "4096", Types::Int);
        assert_fold_type("(long)1 << (char)12", "(long)4096", Types::Long);
        assert_fold_type("'1' << 12", "200704", Types::Int);

        assert_fold_type("(long)-5 >> 42", "(long)-1", Types::Long);
        assert_fold_type("(long)-5 << 42", "-21990232555520", Types::Long);
    }
    #[test]
    fn shift_fold_error() {
        assert_fold_error!(
            "-16 << 33",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );
        assert_fold_error!(
            "(long)-5 >> 64",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Long))
        );

        // negative shift count is UB
        assert_fold_error!("16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("4 >> -3", ErrorKind::NegativeShift);

        assert_fold_error!("-16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("-5 >> -1", ErrorKind::NegativeShift);

        assert_fold_error!(
            "2147483647 << 2",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );
    }

    #[test]
    fn div_fold() {
        assert_fold("5 / 2", "2");
        assert_fold("32 % 5", "2");

        assert_fold("-5 / 2", "-2");
        assert_fold("-32 % 5", "-2");

        assert_fold("5 / -2", "-2");
        assert_fold("32 % -5", "2");

        assert_fold("-5 / -2", "2");
        assert_fold("-32 % -5", "-2");

        assert_fold("(34 / 3) * 3 + 34 % 3", "34");
    }
    #[test]
    fn div_fold_error() {
        assert_fold_error!("3 / 0", ErrorKind::DivideByZero);
        assert_fold_error!("-5 % 0", ErrorKind::DivideByZero);
    }

    #[test]
    fn char_fold() {
        assert_fold_type("'1' + '1'", "98", Types::Int);
        assert_fold("-'1'", "-49");
        assert_fold("!-'1'", "0");
    }
    #[test]
    fn type_conversions() {
        assert_fold_type("4294967296 + 1", "4294967297", Types::Long);
        assert_fold_type("2147483648 - 10", "(long)2147483638", Types::Long);
        assert_fold_type("'1' * 2147483648", "105226698752", Types::Long);

        assert_fold_type("'a'", "'a'", Types::Char);
        assert_fold_type("-'a'", "-'a'", Types::Int);

        assert_fold_type("2147483648", "2147483648", Types::Long);

        assert_fold_type("-2147483649", "-2147483649", Types::Long);
        assert_fold_type("(int)-2147483648", "(int)-2147483648", Types::Int);
    }

    #[test]
    fn overflow_fold() {
        assert_fold_error!(
            "2147483647 + 1",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );
        assert_fold_error!(
            "9223372036854775807 * 2",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Long))
        );

        assert_fold_error!(
            "(int)-2147483648 - 1",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );
        assert_fold_error!(
            "(int)-2147483648 * -1",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );
        assert_fold_error!(
            "-((int)-2147483648)",
            ErrorKind::IntegerOverflow(NEWTypes::Primitive(Types::Int))
        );

        assert_fold_type("(char)127 + 2", "129", Types::Int);
        assert_fold_type("2147483648 + 1", "2147483649", Types::Long);
    }

    #[test]
    fn const_cast() {
        assert_fold_type("(long)'1' + '1'", "(long)98", Types::Long);
        assert_fold_type("(char)2147483648", "(char)0", Types::Char);
        assert_fold_type("(int)2147483648", "(int)-2147483648", Types::Int);

        assert_fold_type("!((long)'1' + '1')", "0", Types::Int);

        assert_fold_error!(
            "(struct {int age;})2",
            ErrorKind::InvalidConstCast(
                NEWTypes::Primitive(Types::Int),
                NEWTypes::Struct(StructInfo::Anonymous(..)),
            )
        );
    }
}
