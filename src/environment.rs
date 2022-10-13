use crate::codegen::StackRegister;
use crate::error::Error;
use crate::interpreter::*;
use crate::token::Token;
use crate::token::TokenType;
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
    pub fn declare_var(&mut self, type_decl: T, name: String) {
        self.current.vars.insert(name, type_decl);
    }

    pub fn declare_func(&mut self, type_decl: Types, name: String) {
        let f = Function::new(type_decl, vec![], vec![]);

        self.current.funcs.insert(name, f);
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
}

#[derive(Clone, PartialEq)]
pub struct CgEnv {
    pub env: Environment<StackRegister>,
    current_bp_offset: usize,
}
impl CgEnv {
    pub fn new() -> Self {
        CgEnv {
            env: Environment::new(None),
            current_bp_offset: 0,
        }
    }
    pub fn reset_bp_offset(&mut self) {
        self.current_bp_offset = 0;
    }
    pub fn declare_var(&mut self, type_decl: &Types, name: String) {
        self.current_bp_offset += type_decl.size();
        self.env
            .current
            .vars
            .insert(name, StackRegister::new(self.current_bp_offset));
    }

    pub fn get_func(&self, name: String, global_env: &Environment<StackRegister>) -> Types {
        global_env.current.funcs.get(&name).unwrap().return_type
    }

    pub fn get_var(&self, name: String) -> StackRegister {
        let t = Token::new(TokenType::Ident(name), -1, -1, "".to_string());
        self.env.get_var(&t).unwrap()
    }
}
