use crate::common::{error::*, token::*, types::*};
use std::collections::HashMap;

pub enum FunctionKind {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<(NEWTypes, Token)>,
    pub return_type: NEWTypes,
}
impl Function {
    pub fn new(return_type: NEWTypes, params: Vec<(NEWTypes, Token)>) -> Self {
        Function {
            return_type,
            params,
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

#[derive(Clone, PartialEq)]
pub enum Symbols<T> {
    Var(T),
    FuncDef(Function),
    FuncDecl(Function),
}
impl<T> Symbols<T> {
    pub fn unwrap_var(self) -> T {
        match self {
            Symbols::Var(v) => v,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Table<T> {
    pub symbols: HashMap<String, Symbols<T>>,
    pub customs: HashMap<String, StructRef>,
}

#[derive(Clone, PartialEq)]
pub struct Environment<T> {
    pub current: Table<T>,
    pub enclosing: Option<Box<Environment<T>>>,
}
impl<T: Clone> Environment<T> {
    pub fn new(enclosing: Option<Box<Environment<T>>>) -> Self {
        Environment {
            current: Table {
                symbols: HashMap::<String, Symbols<T>>::new(),
                customs: HashMap::<String, StructRef>::new(),
            },
            enclosing,
        }
    }
    // methods used for typechecker AND codegen
    pub fn declare_var(&mut self, name: String, value: T) {
        self.current.symbols.insert(name, Symbols::Var(value));
    }

    pub fn declare_func(
        &mut self,
        return_type: NEWTypes,
        name: &str,
        params: Vec<(NEWTypes, Token)>,
        kind: FunctionKind,
    ) {
        self.current.symbols.insert(
            name.to_string(),
            match kind {
                FunctionKind::Declaration => Symbols::FuncDecl(Function::new(return_type, params)),
                FunctionKind::Definition => Symbols::FuncDef(Function::new(return_type, params)),
            },
        );
    }

    pub fn get_symbol(&self, var_name: &Token) -> Result<Symbols<T>, Error> {
        let name = var_name.unwrap_string();
        match self.current.symbols.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_symbol(var_name),
                None => Err(Error::new(var_name, "Undeclared symbol")),
            },
        }
    }
    pub fn get_type(&self, var_name: &Token) -> Result<StructRef, Error> {
        let name = var_name.unwrap_string();
        match self.current.customs.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_type(var_name),
                None => Err(Error::new(var_name, "Undeclared type")),
            },
        }
    }
    pub fn init_var(&mut self, name: String, value: T) {
        self.current.symbols.insert(name, Symbols::Var(value));
    }

    pub fn declare_struct(&mut self, name: String) {
        self.current.customs.insert(name.clone(), StructRef::new());
    }
}
