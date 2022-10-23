use crate::common::{error::*, token::*, types::*};

use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<(Types, Token)>,
    pub return_type: Types,
}
impl Function {
    pub fn new(return_type: Types, params: Vec<(Types, Token)>) -> Self {
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
    pub funcs: HashMap<String, Function>,
}
impl<T> Table<T> {
    pub fn new() -> Self {
        Table {
            vars: HashMap::<String, T>::new(),
            funcs: HashMap::<String, Function>::new(),
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
    // methods for only typechecker
    pub fn assign_var(&mut self, var_name: &Token, value: T) -> Result<T, Error> {
        let name = var_name.unwrap_string();
        match self.current.vars.contains_key(&name) {
            true => {
                self.current.vars.insert(name, value.clone());
                Ok(value)
            }
            false => match &mut self.enclosing {
                Some(env) => env.assign_var(var_name, value),
                None => Err(Error::new(var_name, "undeclared variable")),
            },
        }
    }
    pub fn init_var(&mut self, name: String, value: T) {
        self.current.vars.insert(name, value);
    }

    pub fn declare_func(&mut self, return_type: Types, name: &str, params: Vec<(Types, Token)>) {
        let f = Function::new(return_type, params);

        self.current.funcs.insert(name.to_string(), f);
    }
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        // has to be called from global_env because functions can only be declared in global scope
        self.current.funcs.get(name)
    }
}
