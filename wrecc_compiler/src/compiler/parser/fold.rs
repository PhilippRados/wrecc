//! Implements constant folding to collapse operations involving only literals into single literal

use crate::compiler::codegen::register::*;
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::hir::decl::DeclType;
use crate::compiler::parser::hir::expr::*;
use crate::compiler::typechecker::*;

impl ExprKind {
    pub fn new_literal(value: i64, primitive_type: Primitive) -> Self {
        ExprKind::Literal(value, QualType::new(Type::Primitive(primitive_type)))
    }
    pub fn get_literal_constant(
        &mut self,
        typechecker: &mut TypeChecker,
        token: &Token,
        msg: &'static str,
    ) -> Result<i64, Error> {
        self.integer_const_fold(typechecker)?;

        if let ExprKind::Literal(n, _) = self {
            Ok(*n)
        } else {
            Err(Error::new(token, ErrorKind::NotIntegerConstant(msg)))
        }
    }
    pub fn preprocessor_constant(&mut self, pp: &impl Location) -> Result<i64, Error> {
        let mut typechecker = TypeChecker::new();
        self.integer_const_fold(&mut typechecker)?;

        if let ExprKind::Literal(n, _) = self {
            Ok(*n)
        } else {
            Err(Error::new(
                pp,
                ErrorKind::Regular("invalid preprocessor constant expression"),
            ))
        }
    }
    // https://en.cppreference.com/w/c/language/constant_expression
    pub fn integer_const_fold(&mut self, typechecker: &mut TypeChecker) -> Result<(), Error> {
        let folded: Option<ExprKind> = match self {
            ExprKind::Literal(..) => None,
            ExprKind::Ident(name) => {
                // if variable is known at compile time then foldable
                // is only enum-constant
                if let Ok(Symbol {
                    reg: Some(Register::Literal(n, _)),
                    qtype,
                    ..
                }) = typechecker.env.get_symbol(name).map(|s| s.borrow().clone())
                {
                    Some(ExprKind::Literal(n, qtype))
                } else {
                    None
                }
            }
            ExprKind::Binary { left, token, right } => {
                Self::binary_fold(typechecker, left, token.clone(), right)?
            }
            ExprKind::Unary { token, right, .. } => Self::unary_fold(typechecker, token.clone(), right)?,
            ExprKind::Logical { left, token, right } => {
                Self::logical_fold(typechecker, token.clone(), left, right)?
            }
            ExprKind::Comparison { left, token, right } => {
                Self::comp_fold(typechecker, token.clone(), left, right)?
            }
            ExprKind::Cast { decl_type, token, expr, .. } => {
                Self::const_cast(typechecker, token.clone(), decl_type, expr)?
            }
            ExprKind::Ternary { cond, true_expr, false_expr, token } => {
                cond.integer_const_fold(typechecker)?;
                true_expr.integer_const_fold(typechecker)?;
                false_expr.integer_const_fold(typechecker)?;

                if let (ExprKind::Literal(_, true_type), ExprKind::Literal(_, false_type)) =
                    (*true_expr.clone(), *false_expr.clone())
                {
                    if !true_type.type_compatible(&false_type, false_expr.as_ref()) {
                        return Err(Error::new(token, ErrorKind::TypeMismatch(true_type, false_type)));
                    }
                }

                match cond.as_ref() {
                    ExprKind::Literal(0, _) => Some(false_expr.as_ref().clone()),
                    ExprKind::Literal(..) => Some(true_expr.as_ref().clone()),
                    _ => None,
                }
            }
            ExprKind::SizeofType { token, decl_type } => {
                let size = typechecker.parse_type(&token, decl_type.clone())?.ty.size();
                Some(ExprKind::new_literal(size as i64, Primitive::Int))
            }

            ExprKind::Assign { l_expr, r_expr, .. } => {
                l_expr.integer_const_fold(typechecker)?;
                r_expr.integer_const_fold(typechecker)?;
                None
            }
            ExprKind::CompoundAssign { l_expr, r_expr, .. } => {
                l_expr.integer_const_fold(typechecker)?;
                r_expr.integer_const_fold(typechecker)?;
                None
            }
            ExprKind::Comma { left, right } => {
                left.integer_const_fold(typechecker)?;
                right.integer_const_fold(typechecker)?;
                None
            }
            ExprKind::MemberAccess { expr, .. } => {
                expr.integer_const_fold(typechecker)?;
                None
            }
            ExprKind::PostUnary { left, .. } => {
                left.integer_const_fold(typechecker)?;
                None
            }
            ExprKind::Call { .. }
            | ExprKind::String(..)
            | ExprKind::SizeofExpr { .. }
            | ExprKind::Nop { .. } => None,
        };

        if let Some(folded_expr) = folded {
            *self = folded_expr;
        };

        Ok(())
    }
    fn binary_fold(
        typechecker: &mut TypeChecker,
        left: &mut Box<ExprKind>,
        token: Token,
        right: &mut Box<ExprKind>,
    ) -> Result<Option<ExprKind>, Error> {
        left.integer_const_fold(typechecker)?;
        right.integer_const_fold(typechecker)?;

        if let (ExprKind::Literal(mut left_n, left_type), ExprKind::Literal(mut right_n, right_type)) =
            (*left.clone(), *right.clone())
        {
            if !crate::compiler::typechecker::is_valid_bin(
                &token.kind,
                &left_type,
                &right_type,
                right.as_ref(),
            ) {
                return Err(Error::new(
                    &token,
                    ErrorKind::InvalidBinary(token.kind.clone(), left_type, right_type),
                ));
            }

            if let Some((literal, amount)) =
                maybe_scale_index(&left_type, &right_type, &mut left_n, &mut right_n)
            {
                *literal = literal.overflowing_mul(amount as i64).0;
            }

            Ok(Some(match token.kind {
                TokenKind::Plus => Self::literal_type(
                    token,
                    left_type,
                    right_type,
                    i64::overflowing_add(left_n, right_n),
                )?,
                TokenKind::Minus => {
                    let (left_type, right_type, scale_factor) = match (&left_type.ty, &right_type.ty) {
                        (Type::Pointer(inner), Type::Pointer(_)) => {
                            let result_type = QualType::new(Type::Primitive(Primitive::Long));
                            (result_type.clone(), result_type, Some(inner.ty.size()))
                        }
                        _ => (left_type, right_type, None),
                    };

                    let result = Self::literal_type(
                        token.clone(),
                        left_type,
                        right_type,
                        i64::overflowing_sub(left_n, right_n),
                    )?;

                    if let Some(scale_factor) = scale_factor {
                        match result {
                            ExprKind::Literal(n, result_type) => Self::literal_type(
                                token,
                                result_type.clone(),
                                result_type,
                                i64::overflowing_div(n, scale_factor as i64),
                            )?,
                            _ => unreachable!("literal_type always returns literal"),
                        }
                    } else {
                        result
                    }
                }
                TokenKind::Star => Self::literal_type(
                    token,
                    left_type,
                    right_type,
                    i64::overflowing_mul(left_n, right_n),
                )?,
                TokenKind::Slash | TokenKind::Mod => {
                    Self::div_fold(token, left_type, right_type, left_n, right_n)?
                }
                TokenKind::GreaterGreater | TokenKind::LessLess => {
                    Self::shift_fold(token, left_type, left_n, right_n)?
                }

                TokenKind::Pipe => {
                    Self::literal_type(token, left_type, right_type, (left_n | right_n, false))?
                }
                TokenKind::Xor => {
                    Self::literal_type(token, left_type, right_type, (left_n ^ right_n, false))?
                }
                TokenKind::Amp => {
                    Self::literal_type(token, left_type, right_type, (left_n & right_n, false))?
                }

                _ => unreachable!("not binary token"),
            }))
        } else {
            Ok(None)
        }
    }
    fn shift_fold(token: Token, left_type: QualType, left: i64, right: i64) -> Result<ExprKind, Error> {
        // result type is only dependant on left operand
        let left_type = if left_type.ty.size() < Primitive::Int.size() {
            QualType::new(Type::Primitive(Primitive::Int))
        } else {
            left_type
        };
        if right < 0 {
            return Err(Error::new(&token, ErrorKind::NegativeShift));
        }

        let (value, overflow) = match token.kind {
            TokenKind::GreaterGreater => i64::overflowing_shr(left, right as u32),
            TokenKind::LessLess => i64::overflowing_shl(left, right as u32),
            _ => unreachable!("not shift operation"),
        };

        if overflow || Self::type_overflow(value, &left_type.ty) {
            Err(Error::new(&token, ErrorKind::IntegerOverflow(left_type)))
        } else {
            Ok(ExprKind::Literal(value, left_type))
        }
    }
    fn div_fold(
        token: Token,
        left_type: QualType,
        right_type: QualType,
        left: i64,
        right: i64,
    ) -> Result<ExprKind, Error> {
        if right == 0 {
            return Err(Error::new(&token, ErrorKind::DivideByZero));
        }

        let operation = match token.kind {
            TokenKind::Slash => i64::overflowing_div(left, right),
            TokenKind::Mod => i64::overflowing_rem(left, right),
            _ => unreachable!("not shift operation"),
        };
        Self::literal_type(token, left_type, right_type, operation)
    }
    fn literal_type(
        token: Token,
        left_type: QualType,
        right_type: QualType,
        (value, overflow): (i64, bool),
    ) -> Result<ExprKind, Error> {
        let result_type = match (left_type, right_type) {
            (qtype, _) | (_, qtype) if qtype.ty.is_ptr() => qtype,
            (left, right) if left.ty.size() > right.ty.size() => left,
            (_, right) => right,
        };

        let result_type = if result_type.ty.size() < Primitive::Int.size() {
            QualType::new(Type::Primitive(Primitive::Int))
        } else {
            result_type
        };

        // calculation can overflow or type from literal can overflow
        if overflow || Self::type_overflow(value, &result_type.ty) {
            Err(Error::new(&token, ErrorKind::IntegerOverflow(result_type)))
        } else {
            Ok(ExprKind::Literal(value, result_type))
        }
    }
    fn type_overflow(value: i64, ty: &Type) -> bool {
        (value > ty.max()) || ((value) < ty.min())
    }

    fn unary_fold(
        typechecker: &mut TypeChecker,
        token: Token,
        right: &mut Box<ExprKind>,
    ) -> Result<Option<ExprKind>, Error> {
        right.integer_const_fold(typechecker)?;

        Ok(match (right.as_ref(), &token.kind) {
            (ExprKind::Literal(n, _), TokenKind::Bang) => {
                Some(ExprKind::new_literal(if *n == 0 { 1 } else { 0 }, Primitive::Int))
            }
            (
                ExprKind::Literal(n, right_type),
                TokenKind::Minus | TokenKind::Plus | TokenKind::Tilde,
            ) => {
                if !right_type.ty.is_integer() {
                    return Err(Error::new(
                        &token,
                        ErrorKind::InvalidUnary(token.kind.clone(), right_type.clone(), "integer"),
                    ));
                }

                Some(Self::literal_type(
                    token.clone(),
                    right_type.clone(),
                    right_type.clone(),
                    if token.kind == TokenKind::Plus {
                        (*n, false)
                    } else if token.kind == TokenKind::Tilde {
                        (!n, false)
                    } else {
                        n.overflowing_neg()
                    },
                )?)
            }
            (..) => None,
        })
    }
    fn logical_fold(
        typechecker: &mut TypeChecker,
        token: Token,
        left: &mut Box<ExprKind>,
        right: &mut Box<ExprKind>,
    ) -> Result<Option<ExprKind>, Error> {
        left.integer_const_fold(typechecker)?;
        right.integer_const_fold(typechecker)?;

        Ok(match token.kind {
            TokenKind::AmpAmp => match (left.as_ref(), right.as_ref()) {
                (ExprKind::Literal(0, _), _) => Some(ExprKind::new_literal(0, Primitive::Int)),
                (ExprKind::Literal(left_n, _), ExprKind::Literal(right_n, _))
                    if *left_n != 0 && *right_n != 0 =>
                {
                    Some(ExprKind::new_literal(1, Primitive::Int))
                }
                (ExprKind::Literal(..), ExprKind::Literal(..)) => {
                    Some(ExprKind::new_literal(0, Primitive::Int))
                }
                _ => None,
            },

            TokenKind::PipePipe => match (left.as_ref(), right.as_ref()) {
                (ExprKind::Literal(1, _), _) => Some(ExprKind::new_literal(1, Primitive::Int)),
                (ExprKind::Literal(left, _), ExprKind::Literal(right, _))
                    if *left == 0 && *right == 0 =>
                {
                    Some(ExprKind::new_literal(0, Primitive::Int))
                }
                (ExprKind::Literal(..), ExprKind::Literal(..)) => {
                    Some(ExprKind::new_literal(1, Primitive::Int))
                }
                _ => None,
            },
            _ => unreachable!("not logical token"),
        })
    }
    fn comp_fold(
        typechecker: &mut TypeChecker,
        token: Token,
        left: &mut Box<ExprKind>,
        right: &mut Box<ExprKind>,
    ) -> Result<Option<ExprKind>, Error> {
        left.integer_const_fold(typechecker)?;
        right.integer_const_fold(typechecker)?;

        if let (ExprKind::Literal(left_n, left_type), ExprKind::Literal(right_n, right_type)) =
            (left.as_ref(), right.as_ref())
        {
            if !crate::compiler::typechecker::is_valid_comp(
                left_type,
                left.as_ref(),
                right_type,
                right.as_ref(),
            ) {
                return Err(Error::new(
                    &token,
                    ErrorKind::InvalidComp(token.kind.clone(), left_type.clone(), right_type.clone()),
                ));
            }

            Ok(Some(match token.kind {
                TokenKind::BangEqual => {
                    ExprKind::new_literal((left_n != right_n).into(), Primitive::Int)
                }
                TokenKind::EqualEqual => {
                    ExprKind::new_literal((left_n == right_n).into(), Primitive::Int)
                }

                TokenKind::Greater => ExprKind::new_literal((left_n > right_n).into(), Primitive::Int),
                TokenKind::GreaterEqual => {
                    ExprKind::new_literal((left_n >= right_n).into(), Primitive::Int)
                }
                TokenKind::Less => ExprKind::new_literal((left_n < right_n).into(), Primitive::Int),
                TokenKind::LessEqual => {
                    ExprKind::new_literal((left_n <= right_n).into(), Primitive::Int)
                }
                _ => unreachable!("not valid comparison token"),
            }))
        } else {
            Ok(None)
        }
    }
    fn const_cast(
        typechecker: &mut TypeChecker,
        token: Token,
        decl_type: &mut DeclType,
        expr: &mut Box<ExprKind>,
    ) -> Result<Option<ExprKind>, Error> {
        expr.integer_const_fold(typechecker)?;

        if let ExprKind::Literal(right, old_type) = expr.as_ref() {
            let new_type = typechecker.parse_type(&token, decl_type.clone())?;

            let (n, new_type) = Self::valid_cast(token, old_type.clone(), new_type, *right)?;
            Ok(Some(ExprKind::Literal(n, new_type)))
        } else {
            Ok(None)
        }
    }
    fn valid_cast(
        token: Token,
        old_type: QualType,
        new_type: QualType,
        right_fold: i64,
    ) -> Result<(i64, QualType), Error> {
        let result = if old_type.ty.is_scalar() && new_type.ty.is_scalar() {
            new_type.ty.maybe_wrap(right_fold)
        } else {
            None
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::parser::tests::setup;
    use crate::setup_type;

    fn assert_fold(input: &str, expected: &str) {
        let mut actual = setup(input).expression().unwrap();
        actual.integer_const_fold(&mut TypeChecker::new()).unwrap();

        let mut expected = setup(expected).expression().unwrap();
        expected.integer_const_fold(&mut TypeChecker::new()).unwrap();

        assert_eq!(actual, expected);
    }
    fn assert_fold_type(input: &str, expected: &str, expected_type: &str) {
        let mut actual = setup(input).expression().unwrap();
        actual.integer_const_fold(&mut TypeChecker::new()).unwrap();

        let mut expected = setup(expected).expression().unwrap();
        expected.integer_const_fold(&mut TypeChecker::new()).unwrap();

        assert_eq!(actual, expected);

        if let ExprKind::Literal(_, actual_type) = actual {
            assert_eq!(actual_type, setup_type!(expected_type));
        } else {
            unreachable!("only literals have type")
        }
    }
    macro_rules! assert_fold_error {
        ($input:expr,$expected_err:pat) => {
            let actual_fold = setup($input)
                .expression()
                .unwrap()
                .integer_const_fold(&mut TypeChecker::new())
                .unwrap_err();

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
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
        );
        assert_fold_error!(
            "(long)-5 >> 64",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Long), .. })
        );

        // negative shift count is UB
        assert_fold_error!("16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("4 >> -3", ErrorKind::NegativeShift);

        assert_fold_error!("-16 << -2", ErrorKind::NegativeShift);
        assert_fold_error!("-5 >> -1", ErrorKind::NegativeShift);
        assert_fold_error!("2 << (int)9223372036854775806", ErrorKind::NegativeShift);

        assert_fold_error!(
            "2147483647 << 2",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
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
                QualType { ty: Type::Primitive(Primitive::Int), .. },
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

        assert_fold_type("1 - 2 ? (void*)4 : (long*)9 - 3", "(void*)4", "void*");

        assert_fold_error!(
            "1 == 2 ? 4 : (long*)9",
            ErrorKind::TypeMismatch(
                QualType { ty: Type::Primitive(Primitive::Int), .. },
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

        assert_fold_type("(char **)1 + (9223372036854775805 * 1)", "(char**)-23", "char**");
    }

    #[test]
    fn overflow_fold() {
        assert_fold_error!(
            "2147483647 + 1",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
        );
        assert_fold_error!(
            "9223372036854775807 * 2",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Long), .. })
        );

        assert_fold_error!(
            "(int)-2147483648 - 1",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
        );
        assert_fold_error!(
            "(int)-2147483648 * -1",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
        );
        assert_fold_error!(
            "-((int)-2147483648)",
            ErrorKind::IntegerOverflow(QualType { ty: Type::Primitive(Primitive::Int), .. })
        );

        assert_fold_type("(char)127 + 2", "129", "int");
        assert_fold_type("(short)127 + 2", "129", "int");
        assert_fold_type("2147483648 + 1", "2147483649", "long");
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
                QualType { ty: Type::Primitive(Primitive::Int), .. },
                QualType {
                    ty: Type::Struct(StructKind::Unnamed(..)),
                    ..
                },
            )
        );
    }
}
