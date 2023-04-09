use crate::codegen::register::*;
use crate::common::{error::*, token::*, types::*};
use std::collections::HashMap;

#[derive(Clone, PartialEq, Debug)]
pub enum FunctionKind {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Function {
    params: Vec<(NEWTypes, Token)>,
    return_type: NEWTypes,

    // how much stack space a function needs to allocate
    // info given in typechecker
    stack_space: usize,

    kind: FunctionKind,
}
impl Function {
    pub fn new(return_type: NEWTypes, params: Vec<(NEWTypes, Token)>, kind: FunctionKind) -> Self {
        Function {
            kind,
            stack_space: 0,
            return_type,
            params,
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
    pub fn get_kind(self) -> FunctionKind {
        self.kind
    }
    pub fn get_params(self) -> Vec<(NEWTypes, Token)> {
        self.params
    }
    pub fn get_return_type(self) -> NEWTypes {
        self.return_type
    }
    pub fn set_stack_size(&mut self, size: usize) {
        self.stack_space = size
    }
    pub fn get_stack_size(&mut self) -> usize {
        self.stack_space
    }
    pub fn cmp(&self, token: &Token, other: &Function) -> Result<(), Error> {
        if self.return_type != other.return_type {
            Err(Error::new(
                token,
                &format!(
                    "Conflicting return-types in function-declarations: expected {}, found {}",
                    self.return_type, other.return_type
                ),
            ))
        } else if self.arity() != other.arity() {
            Err(Error::new(
                token,
                &format!(
                "Mismatched number of parameters in function-declarations: expected {}, found {}",
                self.arity(),
                other.arity()
            ),
            ))
        } else {
            for (i, (types, token)) in self.params.iter().enumerate() {
                if *types != other.params[i].0 {
                    return Err(Error::new(token,
                        &format!("Mismatched parameter-types in function-declarations: expected '{}', found '{}'",
                            other.params[i].0,types)));
                }
            }
            Ok(())
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct SymbolInfo {
    // type of identifier given in declaration
    pub type_decl: NEWTypes,

    // optional because info isn't known at moment of insertion
    // stack-register that identifier resides in
    pub reg: Option<Register>,

    // wether or not symbol was declared in global scope
    pub is_global: bool,
}

impl SymbolInfo {
    pub fn new(type_decl: NEWTypes, is_global: bool) -> Self {
        SymbolInfo {
            type_decl,
            is_global,
            reg: None,
        }
    }
    pub fn get_type(&self) -> NEWTypes {
        self.type_decl.clone()
    }
    pub fn get_reg(&self) -> Register {
        self.reg.clone().unwrap()
    }
    pub fn set_reg(&mut self, reg: Register) {
        self.reg = Some(reg)
    }
}
#[derive(Clone, PartialEq, Debug)]
pub enum Symbols {
    // also includes enum-constants
    Variable(SymbolInfo),
    TypeDef(NEWTypes),
    Func(Function),
}
impl Symbols {
    pub fn unwrap_var(self) -> SymbolInfo {
        match self {
            Symbols::Variable(s) => s,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
    pub fn unwrap_func(self) -> Function {
        match self {
            Symbols::Func(f) => f,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
    pub fn is_global(&self) -> bool {
        match self {
            Symbols::Variable(SymbolInfo { is_global, .. }) => *is_global,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tags {
    // struct/union
    Aggregate(StructRef),
    Enum(Vec<(Token, i32)>),
}
impl Tags {
    pub fn get_kind(&self) -> &TokenType {
        match self {
            Tags::Aggregate(s) => s.get_kind(),
            Tags::Enum(_) => &TokenType::Enum,
        }
    }
    pub fn unwrap_aggr(self) -> StructRef {
        match self {
            Tags::Aggregate(s) => s,
            _ => unreachable!(),
        }
    }
    pub fn unwrap_enum(self) -> Vec<(Token, i32)> {
        match self {
            Tags::Enum(s) => s,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Table {
    symbols: HashMap<String, Symbols>,
    tags: HashMap<String, Tags>,
}
impl Table {
    pub fn new() -> Self {
        Table {
            symbols: HashMap::<String, Symbols>::new(),
            tags: HashMap::<String, Tags>::new(),
        }
    }
}
#[derive(Debug)]
pub struct Scope {
    current: usize,
    env: Vec<Environment>,
}
impl Scope {
    pub fn new() -> Self {
        Scope {
            current: 0,
            env: vec![Environment::new(None)],
        }
    }
    pub fn reset_current(&mut self) {
        self.current = 0;
    }
    pub fn is_global(&self) -> bool {
        self.current == 0
    }
    pub fn create(&mut self) {
        let new = Environment::new(Some(self.current));

        self.env.push(new);
        let len = self.env.len() - 1;
        self.env.get_mut(self.current).unwrap().contained.push(len);

        self.current = len;
    }
    pub fn enter(&mut self) {
        // reset contained-index if already went through this scope
        let index = self.env.get(self.current).unwrap().index;
        if index == self.env.get(self.current).unwrap().contained.len() {
            self.env.get_mut(self.current).unwrap().index = 0;
        }

        let prev = self.env.get(self.current).unwrap().index;
        self.env.get_mut(self.current).unwrap().index += 1;

        self.current = self.env.get(self.current).unwrap().contained[prev];
    }
    pub fn exit(&mut self) {
        self.current = self
            .env
            .get(self.current)
            .unwrap()
            .enclosing
            .expect("not global env");
    }
    pub fn declare_symbol(&mut self, var_name: &Token, symbol: Symbols) -> Result<(), Error> {
        let name = var_name.unwrap_string();
        if self
            .env
            .get(self.current)
            .unwrap()
            .current
            .symbols
            .contains_key(&name)
        {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of symbol '{}'", var_name.unwrap_string()),
            ));
        }

        self.env
            .get_mut(self.current)
            .unwrap()
            .current
            .symbols
            .insert(name, symbol);
        Ok(())
    }

    pub fn declare_global_symbol(&mut self, name: String, symbol: Symbols) {
        // don't need to check for redefinitions because function
        self.env
            .get_mut(0)
            .unwrap()
            .current
            .symbols
            .insert(name, symbol);
    }
    pub fn declare_tag(&mut self, var_name: &Token, tag: Tags) -> Result<(), Error> {
        let name = var_name.unwrap_string();
        if self
            .env
            .get(self.current)
            .unwrap()
            .current
            .tags
            .contains_key(&name)
        {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of symbol '{}'", var_name.unwrap_string()),
            ));
        }

        self.env
            .get_mut(self.current)
            .unwrap()
            .current
            .tags
            .insert(name, tag);
        Ok(())
    }

    pub fn set_reg(&mut self, name: &Token, reg: Register) {
        if let Symbols::Variable(ref mut s) = self.get_symbol(name).unwrap() {
            s.set_reg(reg);
            // ugly but updating entry at name
            self.env
                .get_mut(self.current)
                .unwrap()
                .current
                .symbols
                .insert(name.unwrap_string(), Symbols::Variable(s.clone()));
        }
    }
    pub fn set_stack_size(&mut self, name: &Token, size: usize) {
        if let Symbols::Func(ref mut s) = self.get_symbol(name).unwrap() {
            s.set_stack_size(size);
            self.env
                .get_mut(0)
                .unwrap()
                .current
                .symbols
                .insert(name.unwrap_string(), Symbols::Func(s.clone()));
        }
    }

    pub fn get_global_symbol(&self, var_name: &Token) -> Result<Symbols, Error> {
        self.env.get(0).unwrap().get_symbol(var_name, &self.env)
    }
    pub fn get_symbol(&self, var_name: &Token) -> Result<Symbols, Error> {
        self.env
            .get(self.current)
            .unwrap()
            .get_symbol(var_name, &self.env)
    }

    pub fn get_type(&self, var_name: &Token) -> Result<Tags, Error> {
        self.env
            .get(self.current)
            .unwrap()
            .get_type(var_name, &self.env)
    }

    pub fn check_redefinition(&self, name: &Token) -> Result<(), Error> {
        if self
            .env
            .get(self.current)
            .unwrap()
            .current
            .tags
            .contains_key(&name.unwrap_string())
        {
            Err(Error::new(
                name,
                &format!("Redefinition of '{}'", name.unwrap_string()),
            ))
        } else {
            Ok(())
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub struct Environment {
    // index to know which contained env is visited next
    pub index: usize,

    // Environments can hold multiple other environments
    pub contained: Vec<usize>,

    // current environment containing all identifiers
    current: Table,

    // every environment only has single outer environment
    enclosing: Option<usize>,
}
impl Environment {
    pub fn new(enclosing: Option<usize>) -> Self {
        Environment {
            index: 0,
            contained: vec![],
            current: Table::new(),
            enclosing,
        }
    }

    pub fn get_symbol(&self, var_name: &Token, envs: &Vec<Environment>) -> Result<Symbols, Error> {
        let name = var_name.unwrap_string();
        match self.current.symbols.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match self.enclosing {
                Some(env) => envs.get(env).unwrap().get_symbol(var_name, envs),
                None => Err(Error::new(var_name, "Undeclared symbol")),
            },
        }
    }
    pub fn get_type(&self, var_name: &Token, envs: &Vec<Environment>) -> Result<Tags, Error> {
        let name = var_name.unwrap_string();
        match self.current.tags.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match self.enclosing {
                Some(env) => envs.get(env).unwrap().get_type(var_name, envs),
                None => Err(Error::UndeclaredType(var_name.clone())),
            },
        }
    }
}
