use crate::error::Error;
use crate::interpreter::*;
use crate::token::Token;
use crate::token::TokenType;
use crate::types::Types;
use std::collections::HashMap;

#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<(Token, Token)>,
    pub body: Vec<Stmt>,
}
impl Function {
    pub fn new(params: Vec<(Token, Token)>, body: Vec<Stmt>) -> Self {
        Function { params, body }
    }
    pub fn call(&self, interpreter: &mut Interpreter, args: Vec<Types>) -> Types {
        let mut env = Environment::new(Some(Box::new(interpreter.env.clone())));
        self.params
            .iter()
            .enumerate()
            .for_each(|(i, param)| env.init_var(&param.0, &param.1, args[i].clone()));

        match interpreter.execute_block(&self.body, env) {
            Ok(_) => Types::Void,
            Err(return_val) => return_val.unwrap_or(Types::Void),
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

#[derive(Clone, PartialEq)]
pub struct Table {
    vars: HashMap<String, Types>,
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
        self.current.vars.insert(name, Types::Int(-1));
    }
    pub fn get_var(&self, var_name: &Token) -> Types {
        let name = var_name.unwrap_string();
        match self.current.vars.get(&name) {
            Some(v) => v.clone(),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(var_name),
                None => Error::new(var_name, "undeclared variable").print_exit(),
            },
        }
    }
    pub fn assign_var(&mut self, var_name: &Token, value: Types) -> Types {
        let name = var_name.unwrap_string();
        match self.current.vars.contains_key(&name) {
            true => {
                self.current.vars.insert(name, value.clone());
                value
            }
            false => match &mut self.enclosing {
                Some(env) => env.assign_var(var_name, value),
                None => Error::new(var_name, "undeclared variable").print_exit(),
            },
        }
    }
    pub fn init_var(&mut self, type_decl: &Token, var_name: &Token, value: Types) {
        let name = var_name.unwrap_string();
        if self.current.vars.contains_key(&name) {
            Error::new(
                var_name,
                &format!("Error: Redefinition of variable '{}'", name),
            )
            .print_exit();
        }
        self.current.vars.insert(
            name,
            match type_decl.token {
                TokenType::Int => Types::Int(value.unwrap_num()),
                TokenType::Char => Types::Char(value.unwrap_num() as i8),
                _ => unreachable!("Type-checker should catch this"),
            },
        );
    }
}
