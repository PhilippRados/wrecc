use crate::compiler::common::{error::*, token::Token, types::*};
use crate::compiler::typechecker::align;
use crate::compiler::typechecker::mir::{expr::*, stmt::*};

use std::collections::HashMap;
use std::collections::VecDeque;

pub enum ExternalDeclaration {
    Declaration(Vec<Declarator>),
    Function(Function, Vec<Stmt>),
}

pub struct Declarator {
    pub name: Token,
    pub entry: VarSymbol,
    pub init: Option<Init>,
}

pub enum Init {
    /// A single element initializer
    Scalar(Expr),

    /// Flat list of expressions in aggregate initializer and their offset from the 0th element
    Aggr(Vec<(Expr, usize)>),
}

pub struct Function {
    pub name: String,

    pub return_type: Type,

    /// Parameters and their references in the symbol table
    pub params: Vec<VarSymbol>,

    /// If function contains var-args
    pub variadic: bool,

    /// How much stack space a function needs to allocate info given in typechecker
    pub stack_size: usize,

    /// All the goto-labels that are unique to that function
    pub labels: HashMap<String, usize>,

    /// Index of epilogue label in function
    pub epilogue_index: usize,

    /// Offset from base-pointer where variable stays
    pub current_bp_offset: usize,

    /// Switch information, about cases and defaults
    pub switches: VecDeque<Vec<CaseKind>>,

    // TODO: should be done via control-flow-graph
    /// Checks if all paths return from a function
    pub returns_all_paths: bool,

    /// All goto-statements in that function, used to generate error for unkown goto-label
    pub gotos: Vec<Token>,

    /// Keeps track of current scope-kind to check that certain statements (eg. continue or case) are
    // only within certain other scopes (loops and switches, respectively)
    pub scope: Vec<ScopeKind>,
}
impl Function {
    pub fn new(name: String, return_type: Type, variadic: bool) -> Self {
        Function {
            name,
            params: Vec::new(),
            return_type,
            variadic,
            stack_size: 0,
            labels: HashMap::new(),
            epilogue_index: 0,
            current_bp_offset: 0,
            switches: VecDeque::new(),
            returns_all_paths: false,
            gotos: Vec::new(),
            scope: Vec::new(),
        }
    }
    pub fn increment_stack_size(&mut self, type_decl: &Type) {
        // pure function-type doesnt require any stack-space
        if !type_decl.is_func() {
            let mut size = self.stack_size + type_decl.size();
            size = align(size, type_decl);

            self.stack_size = size;
        }
    }
    pub fn insert_label(&mut self, name_token: &Token) -> Result<(), Error> {
        let name = name_token.unwrap_string();

        if self.labels.contains_key(&name) {
            return Err(Error::new(name_token, ErrorKind::Redefinition("label", name)));
        }
        let len = self.labels.len();
        self.labels.insert(name, len);

        Ok(())
    }
    pub fn compare_gotos(&mut self) -> Result<(), Error> {
        for g in &self.gotos {
            let label = g.unwrap_string();
            if !self.labels.contains_key(&label) {
                return Err(Error::new(g, ErrorKind::UndeclaredLabel(label)));
            }
        }
        Ok(())
    }
    pub fn main_return(&mut self, token: &Token, body: &mut Vec<Stmt>) -> Result<(), Error> {
        if self.name == "main" {
            if self.return_type != Type::Primitive(Primitive::Int) {
                return Err(Error::new(
                    token,
                    ErrorKind::InvalidMainReturn(self.return_type.clone()),
                ));
            }
            if !self.returns_all_paths {
                self.returns_all_paths = true;

                body.push(Stmt::Return(Some(Expr {
                    kind: ExprKind::Literal(0),
                    type_decl: Type::Primitive(Primitive::Int),
                    value_kind: ValueKind::Rvalue,
                })));
            }
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! find_scope {
    ($scope:expr,$($expected:pat_param)|+) => {{
        let mut result = None;
        for current in $scope.iter_mut().rev() {
            if matches!(current, $($expected)|+) {
                result = Some(current);
                break;
            }
        }
        result
    }};
}

#[derive(Debug, PartialEq)]
pub enum ScopeKind {
    Other,
    Loop,
    Switch(Vec<CaseKind>),
}

#[derive(Debug, PartialEq)]
pub enum CaseKind {
    Case(i64),
    Default,
}
