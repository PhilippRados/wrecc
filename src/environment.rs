use crate::error::Error;
use crate::interpreter::*;
use crate::token::Token;
use crate::types::TypeValues;
use crate::types::Types;
use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<(Types, Token)>,
    pub body: Vec<Stmt>,
    pub return_type: Types,
}
impl Function {
    pub fn new(return_type: Types, params: Vec<(Types, Token)>, body: Vec<Stmt>) -> Self {
        Function {
            return_type,
            params,
            body,
        }
    }
    pub fn call(&self, interpreter: &mut Interpreter, args: Vec<TypeValues>) -> TypeValues {
        let mut env = Environment::new(Some(Box::new(interpreter.env.clone())));
        self.params.iter().enumerate().for_each(|(i, (_, name))| {
            env.init_var(name.unwrap_string(), args[i].clone()).unwrap()
        });

        match interpreter.execute_block(&self.body, env) {
            Ok(_) => TypeValues::Void,
            Err(return_val) => return_val.unwrap_or(TypeValues::Void),
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

#[derive(Clone, PartialEq)]
pub struct Table<VarT> {
    pub vars: HashMap<String, VarT>,
    pub funcs: HashMap<String, Function>,
}
impl<VarT> Table<VarT> {
    pub fn new() -> Self {
        Table {
            vars: HashMap::<String, VarT>::new(),
            funcs: HashMap::<String, Function>::new(),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Environment<VarT> {
    pub current: Table<VarT>,
    pub enclosing: Option<Box<Environment<VarT>>>,
}
impl<VarT: Clone> Environment<VarT> {
    pub fn new(enclosing: Option<Box<Environment<VarT>>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    pub fn declare_var(&mut self, type_decl: VarT, name: String) {
        self.current.vars.insert(name, type_decl);
    }
    pub fn get_var(&self, var_name: &Token) -> Result<VarT, Error> {
        let name = var_name.unwrap_string();
        match self.current.vars.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(var_name),
                None => Err(Error::new(var_name, "undeclared variable")),
            },
        }
    }
    pub fn assign_var(&mut self, var_name: &Token, value: VarT) -> Result<VarT, Error> {
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
    pub fn init_var(&mut self, name: String, value: VarT) -> Result<(), Error> {
        self.current.vars.insert(name, value);
        Ok(())
    }
}
