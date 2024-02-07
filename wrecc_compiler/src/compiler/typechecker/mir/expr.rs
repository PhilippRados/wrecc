use crate::compiler::common::{token::TokenKind, types::*};

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Binary { left: Box<Expr>, operator: TokenKind, right: Box<Expr> },
    Unary { operator: TokenKind, right: Box<Expr> },
    Grouping { expr: Box<Expr> },
    Assign { l_expr: Box<Expr>, r_expr: Box<Expr> },
    CompoundAssign { expr: Box<Expr>, tmp_symbol: VarSymbol },
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
    Ident(VarSymbol),
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
    pub type_decl: Type,
    pub value_kind: ValueKind,
}
impl Expr {
    // both arrays and function types decay into:
    // int a[4] => int *a;
    // int f() => int (*f)()
    pub fn decay(self) -> Expr {
        match self.type_decl.clone() {
            Type::Array { of, .. } => Expr {
                value_kind: self.value_kind.clone(),
                type_decl: of.pointer_to(),

                kind: ExprKind::Unary {
                    operator: TokenKind::Amp,
                    right: Box::new(self),
                },
            },
            ty @ Type::Function(_) => Expr {
                value_kind: self.value_kind.clone(),
                type_decl: ty.pointer_to(),

                kind: ExprKind::Unary {
                    operator: TokenKind::Amp,
                    right: Box::new(self),
                },
            },
            _ => self,
        }
    }
    pub fn to_rval(&mut self) {
        self.value_kind = ValueKind::Rvalue;
    }
    pub fn cast_to(self, new_type: Type, direction: CastDirection) -> Expr {
        Expr {
            type_decl: new_type.clone(),
            value_kind: self.value_kind.clone(),
            kind: ExprKind::Cast {
                new_type,
                direction,
                expr: Box::new(self),
            },
        }
    }
    pub fn maybe_int_promote(self) -> Expr {
        if self.type_decl.get_primitive().is_none() || self.type_decl.is_void() {
            return self;
        }

        if self.type_decl.size() < Type::Primitive(Primitive::Int).size() {
            self.cast_to(Type::Primitive(Primitive::Int), CastDirection::Up)
        } else {
            self
        }
    }

    // 6.6 Constant Expressions
    // returns true if expression is known at compile-time
    pub fn is_constant(&self) -> bool {
        match &self.kind {
            ExprKind::String(_) | ExprKind::Literal(_) => true,
            ExprKind::Cast { expr, .. }
            | ExprKind::ScaleUp { expr, .. }
            | ExprKind::Grouping { expr } => expr.is_constant(),

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
            ExprKind::Cast { expr, .. }
            | ExprKind::ScaleUp { expr, .. }
            | ExprKind::Grouping { expr } => expr.is_address_constant(is_outer),
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
