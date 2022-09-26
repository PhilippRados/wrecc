use crate::error::Error;
use crate::interpreter::*;
use crate::token::Token;
use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<Token>,
    pub body: Vec<Stmt>,
}
impl Function {
    pub fn new(params: Vec<Token>, body: Vec<Stmt>) -> Self {
        Function { params, body }
    }
    pub fn call(&self, interpreter: &mut Interpreter, args: Vec<i32>) -> i32 {
        let mut env = Environment::new(Some(Box::new(interpreter.env.clone())));
        self.params
            .iter()
            .enumerate()
            .for_each(|(i, param)| env.init_var(param, args[i]));

        match interpreter.execute_block(&self.body, env) {
            Ok(_) => 0,
            Err(return_val) => match return_val {
                ReturnValue::Some(v) => v,
                ReturnValue::None => 0,
            },
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

#[derive(Clone, PartialEq)]
pub struct Table {
    vars: HashMap<String, i32>,
    pub funcs: HashMap<String, Function>,
}
impl Table {
    fn new() -> Self {
        Table {
            vars: HashMap::new(),
            funcs: HashMap::new(),
        }
    }
}
#[derive(Clone, PartialEq)]
pub struct Environment {
    pub current: Table,
    pub enclosing: Option<Box<Environment>>,
}
impl Environment {
    pub fn new(enclosing: Option<Box<Environment>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    pub fn declare_var(&mut self, var_name: &Token) {
        let name = var_name.unwrap_string();
        if self.current.vars.contains_key(&name) {
            Error::new(
                var_name,
                &format!("Error: Redefinition of variable '{}'", name),
            )
            .print_exit();
        }
        self.current.vars.insert(name, -1);
    }
    pub fn get_var(&self, var_name: &Token) -> i32 {
        let name = var_name.unwrap_string();
        match self.current.vars.get(&name) {
            Some(v) => *v,
            None => match &self.enclosing {
                Some(env) => (**env).get_var(var_name),
                None => Error::new(var_name, "undeclared variable").print_exit(),
            },
        }
    }
    pub fn assign_var(&mut self, var_name: &Token, value: i32) -> i32 {
        let name = var_name.unwrap_string();
        match self.current.vars.contains_key(&name) {
            true => {
                self.current.vars.insert(name, value);
                return value;
            }
            false => match &mut self.enclosing {
                Some(env) => env.assign_var(var_name, value),
                None => Error::new(var_name, "undeclared variable").print_exit(),
            },
        }
    }
    pub fn init_var(&mut self, var_name: &Token, value: i32) {
        let name = var_name.unwrap_string();
        if self.current.vars.contains_key(&name) {
            Error::new(
                var_name,
                &format!("Error: Redefinition of variable '{}'", name),
            )
            .print_exit();
        }
        self.current.vars.insert(name, value);
    }
}