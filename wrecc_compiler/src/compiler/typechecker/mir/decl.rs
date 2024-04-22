use crate::compiler::common::{environment::SymbolRef, error::*, token::Token, types::*};
use crate::compiler::parser::hir;
use crate::compiler::typechecker::align;
use crate::compiler::typechecker::mir::{expr::*, stmt::*};

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::rc::Rc;

pub enum ExternalDeclaration {
    Declaration(Vec<Declarator>),
    Function(Function, SymbolRef, Vec<Stmt>),
}

pub struct Declarator {
    pub name: Token,
    pub entry: SymbolRef,
    pub init: Option<Init>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StorageClass {
    TypeDef,
    Extern,
    Static,
    Auto,
    Register,
}
impl StorageClass {
    pub fn to_string(&self) -> &'static str {
        match self {
            StorageClass::TypeDef => "typedef",
            StorageClass::Extern => "extern",
            StorageClass::Static => "static",
            StorageClass::Auto => "auto",
            StorageClass::Register => "register",
        }
    }
}
use hir::decl::StorageClassKind;
impl Into<StorageClass> for StorageClassKind {
    fn into(self) -> StorageClass {
        match self {
            StorageClassKind::TypeDef => StorageClass::TypeDef,
            StorageClassKind::Extern => StorageClass::Extern,
            StorageClassKind::Static => StorageClass::Static,
            StorageClassKind::Auto => StorageClass::Auto,
            StorageClassKind::Register => StorageClass::Register,
        }
    }
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

    /// Declarations inside of a function-body are saved and declared after function-definition
    pub static_declarations: Vec<(String, Declarator)>,

    /// Parameters and their references in the symbol table
    pub params: Vec<SymbolRef>,

    /// If function contains var-args
    pub variadic: bool,

    /// If function was declared as `inline`
    pub is_inline: bool,

    /// How much stack space a function needs to allocate
    pub stack_size: usize,

    /// All the goto-labels that are unique to that function
    pub labels: HashMap<String, usize>,

    /// Index of epilogue label in function
    pub epilogue_index: usize,

    /// Offset from base-pointer where variable stays
    pub current_bp_offset: usize,

    /// Switch information, about cases and defaults
    pub switches: VecDeque<Rc<RefCell<Vec<CaseKind>>>>,

    // TODO: should be done via control-flow-graph
    /// Checks if all paths return from a function
    pub returns_all_paths: bool,

    /// All goto-statements in that function, used to generate error for unknown goto-label
    pub gotos: Vec<Token>,

    /// Keeps track of current scope-kind to check that certain statements (eg. continue or case) are
    // only within certain other scopes (loops and switches, respectively)
    pub scope: Vec<ScopeKind>,
}
impl Function {
    pub fn new(name: String, return_type: Type, variadic: bool, is_inline: bool) -> Self {
        Function {
            name,
            params: Vec::new(),
            return_type,
            variadic,
            is_inline,
            stack_size: 0,
            labels: HashMap::new(),
            static_declarations: Vec::new(),
            epilogue_index: 0,
            current_bp_offset: 0,
            switches: VecDeque::new(),
            returns_all_paths: false,
            gotos: Vec::new(),
            scope: Vec::new(),
        }
    }
    pub fn increment_stack_size(&mut self, symbol: &SymbolRef) {
        if !symbol.borrow().is_extern() && !symbol.borrow().is_static() {
            let mut size = self.stack_size + symbol.borrow().type_decl.size();
            size = align(size, &symbol.borrow().type_decl);

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
            if self.is_inline {
                return Err(Error::new(
                    token,
                    ErrorKind::Regular("'main' function cannot be declared 'inline'"),
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
    Switch(Rc<RefCell<Vec<CaseKind>>>),
}

#[derive(Debug, PartialEq)]
pub enum CaseKind {
    Case(i64),
    Default,
}
