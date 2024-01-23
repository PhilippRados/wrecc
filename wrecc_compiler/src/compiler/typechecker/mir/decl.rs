use crate::compiler::common::{token::Token, types::*};
use crate::compiler::typechecker::mir::{expr::*, stmt::*};

pub enum ExternalDeclaration {
    Declaration(Vec<Declarator>),
    Function(String, FuncSymbol, Vec<VarSymbol>, Vec<Stmt>),
}

pub struct Declarator {
    pub name: Token,
    pub entry: VarSymbol,
    pub init: Option<Init>,
}

pub enum Init {
    Scalar(Expr),
    Aggr(Vec<(Expr, usize)>),
}
