use crate::common::{error::*, token::*, types::*};
use std::collections::HashMap;

pub enum FunctionKind {
    Declaration,
    DefDeclaration,
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
pub struct Table<T> {
    pub vars: HashMap<String, T>,
    // for declaration;
    // can have multiple
    pub func_decl: HashMap<String, Function>,
    // for declaration{}
    // can only have single
    pub func_def_decl: HashMap<String, Function>,
}
impl<T> Table<T> {
    pub fn new() -> Self {
        Table {
            vars: HashMap::<String, T>::new(),
            func_decl: HashMap::<String, Function>::new(),
            func_def_decl: HashMap::<String, Function>::new(),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Environment<T> {
    pub current: Table<T>,
    pub enclosing: Option<Box<Environment<T>>>,
}
impl<T: Clone> Environment<T> {
    pub fn new(enclosing: Option<Box<Environment<T>>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    // methods used for typechecker AND codegen
    pub fn declare_var(&mut self, name: String, value: T) {
        self.current.vars.insert(name, value);
    }

    pub fn get_var(&self, var_name: &Token) -> Result<T, Error> {
        let name = var_name.unwrap_string();
        match self.current.vars.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(var_name),
                None => Err(Error::new(var_name, "undeclared variable")),
            },
        }
    }
    pub fn init_var(&mut self, name: String, value: T) {
        self.current.vars.insert(name, value);
    }

    pub fn declare_func(
        &mut self,
        return_type: NEWTypes,
        name: &str,
        params: Vec<(NEWTypes, Token)>,
        kind: FunctionKind,
    ) {
        let f = Function::new(return_type, params);

        match kind {
            FunctionKind::Declaration => self.current.func_decl.insert(name.to_string(), f),
            FunctionKind::DefDeclaration => self.current.func_def_decl.insert(name.to_string(), f),
        };
    }
    pub fn get_func(&self, name: &str, kind: FunctionKind) -> Option<&Function> {
        // has to be called from global_env because functions can only be declared in global scope
        match kind {
            FunctionKind::Declaration => self.current.func_decl.get(name),
            FunctionKind::DefDeclaration => self.current.func_def_decl.get(name),
        }
    }
}
