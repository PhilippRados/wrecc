//! Implements constant folding to collapse operations involving only literals into single literal

use self::mir::expr::*;
use crate::compiler::codegen::register::*;
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::typechecker::*;

macro_rules! bin_op {
    ($left:expr,$op:tt,$right:expr) => {
        match ($left,$right) {
            (LiteralKind::Signed(left),LiteralKind::Signed(right)) => LiteralKind::Signed((left $op right).into()),
            (LiteralKind::Unsigned(left),LiteralKind::Unsigned(right)) => LiteralKind::Unsigned((left $op right).into()),
             _ => unreachable!("typechecker makes both operands of same literal kind")
        }
    };
}

fn overflow_bin_op(
    left: &LiteralKind,
    right: &LiteralKind,
    overflow_op: fn(i64, i64) -> (i64, bool),
    wrap_op: fn(u64, u64) -> u64,
) -> (LiteralKind, bool) {
    match (left, right) {
        (LiteralKind::Signed(left), LiteralKind::Signed(right)) => {
            let (value, overflow) = overflow_op(*left, *right);
            (LiteralKind::Signed(value), overflow)
        }
        (LiteralKind::Unsigned(left), LiteralKind::Unsigned(right)) => {
            (LiteralKind::Unsigned(wrap_op(*left, *right)), false)
        }
        _ => unreachable!("typechecker makes sure both operands are equal"),
    }
}

impl Expr {
    pub fn int_literal(value: i64) -> Expr {
        Expr {
            kind: ExprKind::Literal(LiteralKind::Signed(value)),
            qtype: QualType::new(Type::Primitive(Primitive::Int(false))),
            value_kind: ValueKind::Rvalue,
        }
    }
    pub fn get_literal_constant(
        &mut self,
        token: &Token,
        msg: &'static str,
    ) -> Result<LiteralKind, Error> {
        self.integer_const_fold()?;

        if let ExprKind::Literal(literal) = &self.kind {
            Ok(literal.clone())
        } else {
            Err(Error::new(token, ErrorKind::NotIntegerConstant(msg)))
        }
    }
    pub fn preprocessor_constant(&mut self, pp: &impl Location) -> Result<LiteralKind, Error> {
        self.integer_const_fold()?;

        if let ExprKind::Literal(literal) = &self.kind {
            Ok(literal.clone())
        } else {
            Err(Error::new(
                pp,
                ErrorKind::Regular("invalid preprocessor constant expression"),
            ))
        }
    }
    // https://en.cppreference.com/w/c/language/constant_expression
    pub fn integer_const_fold(&mut self) -> Result<(), Error> {
        let folded: Option<Expr> = match &mut self.kind {
            ExprKind::Literal(..) => None,
            ExprKind::Ident(symbol) => {
                // if variable is known at compile time then foldable
                // is only enum-constant
                if let Symbol {
                    reg: Some(Register::Literal(literal, _)),
                    qtype,
                    ..
                } = &*symbol.borrow()
                {
                    // INFO: enum constants can only be of type `int`
                    Some(Expr {
                        kind: ExprKind::Literal(literal.clone()),
                        qtype: qtype.clone(),
                        value_kind: ValueKind::Rvalue,
                    })
                } else {
                    None
                }
            }
            ExprKind::Binary { left, token, right } => {
                Self::binary_fold(token.clone(), self.qtype.clone(), left, right)?
            }
            ExprKind::Unary { token, right, .. } => {
                Self::unary_fold(token.clone(), self.qtype.clone(), right)?
            }
            ExprKind::Logical { left, token, right } => Self::logical_fold(token.clone(), left, right)?,
            ExprKind::Comparison { left, token, right } => Self::comp_fold(token.clone(), left, right)?,
            ExprKind::Cast { new_type, expr, .. } => Self::const_cast(new_type.clone(), expr)?,
            ExprKind::Scale { token, by_amount, direction, expr } => {
                expr.integer_const_fold()?;

                if let ExprKind::Literal(literal) = &expr.kind {
                    let by_amount = match literal {
                        LiteralKind::Signed(_) => LiteralKind::Signed(*by_amount as i64),
                        LiteralKind::Unsigned(_) => LiteralKind::Unsigned(*by_amount as u64),
                    };
                    let scaled_literal = match direction {
                        ScaleDirection::Up => Self::literal_type(
                            token,
                            self.qtype.clone(),
                            overflow_bin_op(
                                &literal,
                                &by_amount,
                                i64::overflowing_mul,
                                u64::wrapping_mul,
                            ),
                        ),
                        ScaleDirection::Down => Self::literal_type(
                            token,
                            self.qtype.clone(),
                            overflow_bin_op(
                                &literal,
                                &by_amount,
                                i64::overflowing_div,
                                u64::wrapping_div,
                            ),
                        ),
                    };
                    match scaled_literal {
                        Ok(literal) => Some(literal),
                        Err(err) => {
                            return Err(Error {
                                kind: ErrorKind::ScaleOverflow(self.qtype.clone()),
                                ..err
                            })
                        }
                    }
                } else {
                    None
                }
            }
            ExprKind::Ternary { cond, true_expr, false_expr } => {
                cond.integer_const_fold()?;
                true_expr.integer_const_fold()?;
                false_expr.integer_const_fold()?;

                match &cond.kind {
                    ExprKind::Literal(lit) if lit.is_zero() => Some(false_expr.as_ref().clone()),
                    ExprKind::Literal(_) => Some(true_expr.as_ref().clone()),
                    _ => None,
                }
            }
            ExprKind::Assign { l_expr, r_expr, .. } => {
                l_expr.integer_const_fold()?;
                r_expr.integer_const_fold()?;
                None
            }
            ExprKind::CompoundAssign { expr, .. } => {
                expr.integer_const_fold()?;
                None
            }
            ExprKind::Comma { left, right } => {
                left.integer_const_fold()?;
                right.integer_const_fold()?;
                None
            }
            ExprKind::MemberAccess { expr, .. } => {
                expr.integer_const_fold()?;
                None
            }
            ExprKind::Call { .. } | ExprKind::String(..) | ExprKind::Nop { .. } => None,
        };

        if let Some(folded_expr) = folded {
            *self = folded_expr;
        };

        Ok(())
    }
    fn binary_fold(
        token: Token,
        result_type: QualType,
        left: &mut Box<Expr>,
        right: &mut Box<Expr>,
    ) -> Result<Option<Expr>, Error> {
        left.integer_const_fold()?;
        right.integer_const_fold()?;

        if let (ExprKind::Literal(left_n), ExprKind::Literal(right_n)) = (&left.kind, &right.kind) {
            Ok(Some(match token.kind {
                TokenKind::Plus => Self::literal_type(
                    &token,
                    result_type,
                    overflow_bin_op(&left_n, &right_n, i64::overflowing_add, u64::wrapping_add),
                )?,
                TokenKind::Minus => Self::literal_type(
                    &token,
                    result_type,
                    overflow_bin_op(&left_n, &right_n, i64::overflowing_sub, u64::wrapping_sub),
                )?,
                TokenKind::Star => Self::literal_type(
                    &token,
                    result_type,
                    overflow_bin_op(&left_n, &right_n, i64::overflowing_mul, u64::wrapping_mul),
                )?,
                TokenKind::Slash | TokenKind::Mod => {
                    Self::div_fold(&token, result_type, &left_n, &right_n)?
                }
                TokenKind::GreaterGreater | TokenKind::LessLess => {
                    Self::shift_fold(&token, result_type, &left_n, &right_n)?
                }
                TokenKind::Pipe => {
                    Self::literal_type(&token, result_type, (bin_op!(left_n, |, right_n), false))?
                }
                TokenKind::Xor => {
                    Self::literal_type(&token, result_type, (bin_op!(left_n, ^, right_n), false))?
                }
                TokenKind::Amp => {
                    Self::literal_type(&token, result_type, (bin_op!(left_n, &, right_n), false))?
                }
                _ => unreachable!("not binary token"),
            }))
        } else {
            Ok(None)
        }
    }
    fn shift_fold(
        token: &Token,
        result_type: QualType,
        left: &LiteralKind,
        right: &LiteralKind,
    ) -> Result<Expr, Error> {
        if right.is_negative() {
            return Err(Error::new(token, ErrorKind::NegativeShift));
        }

        fn overflow_shift_op(
            left: &LiteralKind,
            right: &LiteralKind,
            overflow_op: fn(i64, u32) -> (i64, bool),
            wrap_op: fn(u64, u32) -> u64,
        ) -> (LiteralKind, bool) {
            match (left, right) {
                (LiteralKind::Signed(left), LiteralKind::Signed(right)) => {
                    let (value, overflow) = overflow_op(*left, *right as u32);
                    (LiteralKind::Signed(value), overflow)
                }
                (LiteralKind::Unsigned(left), LiteralKind::Unsigned(right)) => {
                    (LiteralKind::Unsigned(wrap_op(*left, *right as u32)), false)
                }
                _ => unreachable!("typechecker makes sure both operands are equal"),
            }
        }

        let operation = match token.kind {
            TokenKind::GreaterGreater => {
                overflow_shift_op(left, right, i64::overflowing_shr, u64::wrapping_shr)
            }
            TokenKind::LessLess => {
                overflow_shift_op(left, right, i64::overflowing_shl, u64::wrapping_shl)
            }
            _ => unreachable!("not shift operation"),
        };

        Self::literal_type(token, result_type, operation)
    }
    fn div_fold(
        token: &Token,
        result_type: QualType,
        left: &LiteralKind,
        right: &LiteralKind,
    ) -> Result<Expr, Error> {
        if right.is_zero() {
            return Err(Error::new(token, ErrorKind::DivideByZero));
        }

        let operation = match token.kind {
            TokenKind::Slash => overflow_bin_op(left, right, i64::overflowing_div, u64::wrapping_div),
            TokenKind::Mod => overflow_bin_op(left, right, i64::overflowing_rem, u64::wrapping_rem),
            _ => unreachable!("not div operation"),
        };

        Self::literal_type(token, result_type, operation)
    }
    fn literal_type(
        token: &Token,
        result_type: QualType,
        (literal, overflow): (LiteralKind, bool),
    ) -> Result<Expr, Error> {
        // unsigned literals get wrapped
        if result_type.ty.is_unsigned() {
            Ok(Expr {
                kind: ExprKind::Literal(literal.wrap(&result_type.ty)),
                qtype: result_type,
                value_kind: ValueKind::Rvalue,
            })
        }
        // signed calculations can overflow, or the literal can overflow its type
        else if overflow || literal.type_overflow(&result_type.ty) {
            Err(Error::new(token, ErrorKind::IntegerOverflow(result_type)))
        } else {
            Ok(Expr {
                kind: ExprKind::Literal(literal),
                qtype: result_type,
                value_kind: ValueKind::Rvalue,
            })
        }
    }

    fn unary_fold(
        token: Token,
        result_type: QualType,
        right: &mut Box<Expr>,
    ) -> Result<Option<Expr>, Error> {
        right.integer_const_fold()?;

        Ok(match (&right.kind, &token.kind) {
            (ExprKind::Literal(literal), TokenKind::Bang) => {
                Some(Expr::int_literal(if literal.is_zero() { 1 } else { 0 }))
            }
            (ExprKind::Literal(literal), TokenKind::Minus | TokenKind::Plus | TokenKind::Tilde) => {
                Some(Self::literal_type(
                    &token,
                    result_type,
                    if token.kind == TokenKind::Plus {
                        (literal.clone(), false)
                    } else if token.kind == TokenKind::Tilde {
                        (
                            match literal {
                                LiteralKind::Signed(n) => LiteralKind::Signed(!*n),
                                LiteralKind::Unsigned(n) => LiteralKind::Unsigned(!*n),
                            },
                            false,
                        )
                    } else {
                        match literal {
                            LiteralKind::Signed(n) => {
                                let (value, overflow) = i64::overflowing_neg(*n);
                                (LiteralKind::Signed(value), overflow)
                            }
                            LiteralKind::Unsigned(n) => {
                                let value = u64::wrapping_neg(*n);
                                (LiteralKind::Unsigned(value), false)
                            }
                        }
                    },
                )?)
            }
            _ => None,
        })
    }
    fn logical_fold(
        token: Token,
        left: &mut Box<Expr>,
        right: &mut Box<Expr>,
    ) -> Result<Option<Expr>, Error> {
        left.integer_const_fold()?;
        right.integer_const_fold()?;

        Ok(match token.kind {
            TokenKind::AmpAmp => match (&left.kind, &right.kind) {
                (ExprKind::Literal(lit), _) if lit.is_zero() => Some(Expr::int_literal(0)),
                (ExprKind::Literal(left_lit), ExprKind::Literal(right_lit))
                    if !left_lit.is_zero() && !right_lit.is_zero() =>
                {
                    Some(Expr::int_literal(1))
                }
                (ExprKind::Literal(..), ExprKind::Literal(..)) => Some(Expr::int_literal(0)),
                _ => None,
            },

            TokenKind::PipePipe => match (&left.kind, &right.kind) {
                (ExprKind::Literal(LiteralKind::Signed(1) | LiteralKind::Unsigned(1)), _) => {
                    Some(Expr::int_literal(1))
                }
                (ExprKind::Literal(left_lit), ExprKind::Literal(right_lit))
                    if left_lit.is_zero() && right_lit.is_zero() =>
                {
                    Some(Expr::int_literal(0))
                }
                (ExprKind::Literal(..), ExprKind::Literal(..)) => Some(Expr::int_literal(1)),
                _ => None,
            },
            _ => unreachable!("not logical token"),
        })
    }
    fn comp_fold(
        token: Token,
        left: &mut Box<Expr>,
        right: &mut Box<Expr>,
    ) -> Result<Option<Expr>, Error> {
        left.integer_const_fold()?;
        right.integer_const_fold()?;

        if let (ExprKind::Literal(left_n), ExprKind::Literal(right_n)) = (&left.kind, &right.kind) {
            let literal = match token.kind {
                TokenKind::BangEqual => bin_op!(left_n, !=, right_n),
                TokenKind::EqualEqual => bin_op!(left_n, ==, right_n),
                TokenKind::Greater => bin_op!(left_n, >, right_n),
                TokenKind::GreaterEqual => bin_op!(left_n, >=, right_n),
                TokenKind::Less => bin_op!(left_n, <, right_n),
                TokenKind::LessEqual => bin_op!(left_n, <= ,right_n),
                _ => unreachable!("not valid comparison token"),
            };
            let n = match literal {
                LiteralKind::Signed(0) | LiteralKind::Unsigned(0) => 0,
                LiteralKind::Signed(1) | LiteralKind::Unsigned(1) => 1,
                _ => unreachable!("comparison operations can only return 0 or 1"),
            };

            Ok(Some(Expr::int_literal(n)))
        } else {
            Ok(None)
        }
    }
    fn const_cast(new_type: Type, expr: &mut Box<Expr>) -> Result<Option<Expr>, Error> {
        expr.integer_const_fold()?;

        if let ExprKind::Literal(literal) = &expr.kind {
            let wrapped = literal.wrap(&new_type);
            let wrapped = match (wrapped, new_type.is_unsigned()) {
                (LiteralKind::Signed(n), true) => LiteralKind::Unsigned(n as u64),
                (LiteralKind::Unsigned(n), false) => LiteralKind::Signed(n as i64),
                (wrapped, _) => wrapped,
            };

            Ok(Some(Expr {
                kind: ExprKind::Literal(wrapped),
                qtype: QualType::new(new_type),
                value_kind: ValueKind::Rvalue,
            }))
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::parser::tests::setup;
    use crate::setup_type;

    fn setup_fold(input: &str) -> Result<Expr, Error> {
        let expr = setup(input).expression()?;
        let mut expr = TypeChecker::new().visit_expr(&mut None, expr)?;
        expr.integer_const_fold()?;

        Ok(expr)
    }
    fn assert_fold(input: &str, expected: &str) {
        let actual = setup_fold(input).unwrap();
        let expected = setup_fold(expected).unwrap();

        assert_eq!(actual, expected);
    }
    fn assert_fold_type(input: &str, expected: &str, expected_type: &str) {
        let actual = setup_fold(input).unwrap();
        let expected = setup_fold(expected).unwrap();

        assert_eq!(actual, expected);
        assert_eq!(actual.qtype, setup_type!(expected_type));
    }
    macro_rules! assert_fold_error {
        ($input:expr,$expected_err:pat) => {
            let actual_fold = setup_fold($input).unwrap_err();

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

        assert_fold_type("~0", "-1", "int");
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

        assert_fold("(long*)4 == (long*)1", "0");
        assert_fold("(long*)4 > (long*)1", "1");
        assert_fold("(long*)4 > 0", "1");

        assert_fold("-56 == (char)200", "1");
        assert_fold("(unsigned)2147483649 == -2147483647", "1");
        assert_fold("(unsigned long)2147483649 == -2147483647", "0");

        assert_fold_error!("(int*)4 <= 1", ErrorKind::InvalidComp(..));
        assert_fold_error!("(long*)4 > (char*)1", ErrorKind::InvalidComp(..));
    }

    #[test]
    fn shift_fold() {
        assert_fold("'1' << 5", "1568");
        assert_fold("'1' >> 2", "12");

        assert_fold_type("1 << (long)12", "4096", "int");
        assert_fold_type("(long)1 << (char)12", "(long)4096", "long");
        assert_fold_type("'1' << 12", "200704", "int");

        assert_fold_type("(long)-5 >> 42", "(long)-1", "long");
        assert_fold_type("(long)-5 << 42", "-21990232555520", "long");

        assert_fold("(enum A {B})4 << 2", "(enum A {B})16");
    }
    #[test]
    fn shift_fold_error() {
        assert_fold_error!(
            "-16 << 33",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
        assert_fold_error!(
            "(long)-5 >> 64",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Long(false)),
                ..
            })
        );

        // negative shift count is UB
        assert_fold_error!("16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("4 >> -3", ErrorKind::NegativeShift);

        assert_fold_error!("-16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("-5 >> -1", ErrorKind::NegativeShift);
        assert_fold_error!("2 << (int)9223372036854775806", ErrorKind::NegativeShift);

        assert_fold_error!(
            "2147483647 << 2",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
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
        assert_fold_type("'1' + '1'", "98", "int");
        assert_fold("-'1'", "-49");
        assert_fold("!-'1'", "0");
    }
    #[test]
    fn ptr_fold() {
        assert_fold_type("(long *)1 + 3", "(long*)25", "long*");
        assert_fold_type("2 + (char *)1 + 3", "(char*)6", "char*");
        assert_fold_type("(int*)100 - (int *)2", "(long)24", "long");
        assert_fold_type("(const short*)2 - (short*)100", "(long)-49", "long");
        assert_fold_type("(char*)5 - (char *)10", "(long)-5", "long");

        assert_fold_error!(
            "6 / (int *)1",
            ErrorKind::InvalidBinary(
                _,
                QualType {
                    ty: Type::Primitive(Primitive::Int(false)),
                    ..
                },
                QualType { ty: Type::Pointer(_), .. }
            )
        );

        assert_fold_error!(
            "-(long *)1",
            ErrorKind::InvalidUnary(_, QualType { ty: Type::Pointer(_), .. }, "integer")
        );
        assert_fold_error!(
            "~(char *)1",
            ErrorKind::InvalidUnary(_, QualType { ty: Type::Pointer(_), .. }, "integer")
        );
    }
    #[test]
    fn ternary_fold() {
        assert_fold("1 == 2 ? 4 : 9", "9");
        assert_fold("(char*)1 ? 4 : 9", "4");
        assert_fold_type("1 > 2 ? (unsigned)1 : (long)8", "(long)8", "long");
        assert_fold_type("1 - 2 ? (void*)4 : (long*)9 - 3", "(void*)4", "void*");
        assert_fold_type("1 - 2 ? (long*)4 : (void*)9 - 3", "(void*)4", "void*");

        assert_fold_error!(
            "1 == 2 ? 4 : (long*)9",
            ErrorKind::TypeMismatch(
                QualType {
                    ty: Type::Primitive(Primitive::Int(false)),
                    ..
                },
                QualType { ty: Type::Pointer(_), .. }
            )
        );

        assert_fold_error!(
            "1 == 2 ? (int*)4 : (long*)9",
            ErrorKind::TypeMismatch(
                QualType { ty: Type::Pointer(_), .. },
                QualType { ty: Type::Pointer(_), .. }
            )
        );
    }
    #[test]
    fn type_conversions() {
        assert_fold_type("4294967296 + 1", "4294967297", "long");
        assert_fold_type("2147483648 - 10", "(long)2147483638", "long");
        assert_fold_type("'1' * 2147483648", "105226698752", "long");
        assert_fold_type("(int*)1 + 2147483648", "(int*)8589934593", "int*");
        assert_fold_type("2147483648 + (int*)1", "(int*)8589934593", "int*");

        assert_fold_type("'a'", "'a'", "char");
        assert_fold_type("'a' + (short)3", "100", "int");
        assert_fold_type("-'a'", "-'a'", "int");
        assert_fold_type("+'a'", "(int)'a'", "int");

        assert_fold_type("2147483648", "2147483648", "long");

        assert_fold_type("-2147483649", "-2147483649", "long");
        assert_fold_type("(int)-2147483648", "(int)-2147483648", "int");
    }

    #[test]
    fn overflow_fold() {
        assert_fold_error!(
            "2147483647 + 1",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
        assert_fold_error!(
            "9223372036854775807 * 2",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Long(false)),
                ..
            })
        );

        assert_fold_error!(
            "(int)-2147483648 - 1",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
        assert_fold_error!(
            "(int)-2147483648 * -1",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
        assert_fold_error!(
            "-((int)-2147483648)",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );

        assert_fold_type("(char)127 + 2", "129", "int");
        assert_fold_type("(short)127 + 2", "129", "int");
        assert_fold_type("2147483648 + 1", "2147483649", "long");

        assert_fold_type(
            "(unsigned)999999 * 9999999 * 999999",
            "(unsigned)420793087",
            "unsigned int",
        );
        assert_fold_error!(
            "999999 * 9999999 * 999999",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
        assert_fold_error!(
            "(unsigned)999999 * (long)9999999 * 999999",
            ErrorKind::IntegerOverflow(QualType {
                ty: Type::Primitive(Primitive::Long(false)),
                ..
            })
        );
    }

    #[test]
    fn sub_fold_expressions() {
        assert_fold("1 + 2, 4 * 2", "3,8");
    }

    #[test]
    fn const_cast() {
        assert_fold_type("(long)'1' + '1'", "(long)98", "long");
        assert_fold_type("(char)2147483648", "(char)0", "char");
        assert_fold_type("(int)2147483648", "(int)-2147483648", "int");

        assert_fold_type("!((long)'1' + '1')", "0", "int");

        assert_fold_error!(
            "(struct {int age;})2",
            ErrorKind::InvalidConstCast(
                QualType {
                    ty: Type::Primitive(Primitive::Int(false)),
                    ..
                },
                QualType {
                    ty: Type::Struct(StructKind::Unnamed(..)),
                    ..
                },
            )
        );
    }
    #[test]
    fn scale_ptr() {
        assert_fold_type(
            "(char *)1 + 9223372036854775805",
            "(char*)9223372036854775806",
            "char*",
        );

        assert_fold_error!(
            "(char **)1 + 9223372036854775805",
            ErrorKind::ScaleOverflow(QualType { ty: Type::Pointer(_), .. })
        );
        assert_fold_error!(
            "(long *)1 + 9223372036854775805",
            ErrorKind::ScaleOverflow(QualType {
                ty: Type::Primitive(Primitive::Long(false)),
                ..
            })
        );
        assert_fold_error!(
            "(int *)1 + 9223372036854775805",
            ErrorKind::ScaleOverflow(QualType {
                ty: Type::Primitive(Primitive::Int(false)),
                ..
            })
        );
    }
}
