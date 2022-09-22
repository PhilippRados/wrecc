use crate::interpreter::*;
use crate::parser::Expr;
use std::collections::HashMap;

#[derive(Clone)]
pub struct Function {
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
}
impl Function {
    pub fn new(params: Vec<String>, body: Vec<Stmt>) -> Self {
        Function { params, body }
    }
    pub fn call(&self, interpreter: &mut Interpreter, args: Vec<i32>) {
        let mut env = Environment::new(Some(Box::new(interpreter.global.clone()))); // TODO: remove this indirection with box
        self.params
            .iter()
            .enumerate()
            .for_each(|(i, param)| env.init_var(param, args[i]));

        interpreter.execute_block(&self.body, env);
    }
}

#[derive(Clone)]
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
// FIX: environment shouldnt need clone
#[derive(Clone)]
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
    pub fn declare_var(&mut self, var_name: &str) {
        if self.current.vars.contains_key(var_name) {
            eprintln!("Error: Redefinition of variable '{}'", var_name);
            std::process::exit(-1);
        }
        self.current.vars.insert(var_name.to_string(), -1);
    }
    pub fn get_var(&self, name: &str) -> i32 {
        match self.current.vars.get(name) {
            Some(v) => *v,
            None => match &self.enclosing {
                Some(env) => (**env).get_var(name),
                None => panic!("undeclared var {}", name),
            },
        }
    }
    pub fn assign_var(&mut self, name: &str, value: i32) -> i32 {
        match self.current.vars.contains_key(name) {
            true => {
                self.current.vars.insert(name.to_string(), value);
                return value;
            }
            false => match &mut self.enclosing {
                Some(env) => (*env).assign_var(name, value),
                None => panic!("undeclared var {}", name),
            },
        }
    }
    pub fn init_var(&mut self, var_name: &str, value: i32) {
        if self.current.vars.contains_key(var_name) {
            eprintln!("Error: Redefinition of variable '{}'", var_name);
            std::process::exit(-1);
        }
        self.current.vars.insert(var_name.to_string(), value);
    }
}
