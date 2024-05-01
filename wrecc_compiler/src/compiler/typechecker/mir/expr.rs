use crate::compiler::common::{environment::SymbolRef, error::*, token::*, types::*};

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Binary { left: Box<Expr>, operator: TokenKind, right: Box<Expr> },
    Unary { operator: TokenKind, right: Box<Expr> },
    Assign { l_expr: Box<Expr>, r_expr: Box<Expr> },
    CompoundAssign { expr: Box<Expr>, tmp_symbol: SymbolRef },
    Logical { left: Box<Expr>, operator: TokenKind, right: Box<Expr> },
    Comparison { left: Box<Expr>, operator: TokenKind, right: Box<Expr> },
    Call { caller: Box<Expr>, args: Vec<Expr> },
    Cast { new_type: Type, direction: CastDirection, expr: Box<Expr> },
    ScaleUp { by: usize, expr: Box<Expr> },
    ScaleDown { shift_amount: usize, expr: Box<Expr> },
    MemberAccess { member: String, expr: Box<Expr> },
    Ternary { cond: Box<Expr>, true_expr: Box<Expr>, false_expr: Box<Expr> },
    Comma { left: Box<Expr>, right: Box<Expr> },
    String(String),
    Literal(i64),
    Ident(SymbolRef),
    Nop,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CastDirection {
    Up,
    Down,
    Equal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ValueKind {
    Lvalue,
    Rvalue,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub qtype: QualType,
    pub value_kind: ValueKind,
}
impl Expr {
    // both arrays and function types decay into:
    // int a[4] => int *a;
    // int f() => int (*f)()
    pub fn decay(self, token: &Token) -> Result<Expr, Error> {
        match &self.qtype.ty {
            Type::Array(of, _) => {
                // is actually undefined behaviour but gcc and clang throw error
                // so let's do that too ;)
                if let ExprKind::Ident(symbol) = &self.kind {
                    if symbol.borrow().is_register() {
                        return Err(Error::new(
                            token,
                            ErrorKind::RegisterAddress(symbol.borrow().token.unwrap_string()),
                        ));
                    }
                }

                Ok(Expr {
                    value_kind: ValueKind::Rvalue,
                    qtype: of.clone().pointer_to(Qualifiers::default()),

                    kind: ExprKind::Unary {
                        operator: TokenKind::Amp,
                        right: Box::new(self),
                    },
                })
            }
            Type::Function(_) => Ok(Expr {
                value_kind: ValueKind::Rvalue,
                qtype: self.qtype.clone().pointer_to(Qualifiers::default()),

                kind: ExprKind::Unary {
                    operator: TokenKind::Amp,
                    right: Box::new(self),
                },
            }),
            _ => Ok(self),
        }
    }
    pub fn to_rval(self) -> Expr {
        Expr {
            // all qualifiers are lost in lvalue-to-rvalue conversion
            qtype: QualType {
                qualifiers: Qualifiers::default(),
                ..self.qtype
            },
            value_kind: ValueKind::Rvalue,
            kind: self.kind,
        }
    }
    pub fn cast_to(self, new_type: QualType, direction: CastDirection) -> Expr {
        Expr {
            qtype: new_type.clone(),
            value_kind: self.value_kind.clone(),
            kind: ExprKind::Cast {
                new_type: new_type.ty,
                direction,
                expr: Box::new(self),
            },
        }
    }
    pub fn maybe_int_promote(self) -> Expr {
        if self.qtype.ty.get_primitive().is_none() || self.qtype.ty.is_void() {
            return self;
        }

        if self.qtype.ty.size() < Type::Primitive(Primitive::Int).size() {
            self.cast_to(QualType::new(Type::Primitive(Primitive::Int)), CastDirection::Up)
        } else {
            self
        }
    }

    // 6.6 Constant Expressions
    // returns true if expression is known at compile-time
    pub fn is_constant(&self) -> bool {
        match &self.kind {
            ExprKind::String(_) | ExprKind::Literal(_) => true,
            ExprKind::Cast { expr, .. } | ExprKind::ScaleUp { expr, .. } => expr.is_constant(),
            _ => self.is_address_constant(true),
        }
    }
    fn is_address_constant(&self, is_outer: bool) -> bool {
        match &self.kind {
            ExprKind::Unary { operator, right } if matches!(operator, TokenKind::Amp) => {
                matches!(right.kind, ExprKind::Ident(_) | ExprKind::String(_))
                    || right.is_address_constant(false)
            }
            ExprKind::Unary { operator, right, .. }
                if matches!(operator, TokenKind::Star) && !is_outer =>
            {
                right.is_address_constant(is_outer)
            }
            ExprKind::MemberAccess { .. } if !is_outer => true,
            ExprKind::Binary { left, operator, right }
                if matches!(operator, TokenKind::Plus | TokenKind::Minus) =>
            {
                match (&left, &right) {
                    (expr, n) | (n, expr) if n.is_const_literal() => expr.is_address_constant(is_outer),
                    _ => false,
                }
            }
            ExprKind::Cast { expr, .. } | ExprKind::ScaleUp { expr, .. } => {
                expr.is_address_constant(is_outer)
            }
            _ => false,
        }
    }
    fn is_const_literal(&self) -> bool {
        match &self.kind {
            ExprKind::Cast { expr, .. } | ExprKind::ScaleUp { expr, .. } => expr.is_const_literal(),
            ExprKind::Literal(_) => true,
            _ => false,
        }
    }
}

impl crate::compiler::parser::hir::expr::IsZero for Expr {
    fn is_zero(&self) -> bool {
        matches!(self.kind, ExprKind::Literal(0))
    }
}
