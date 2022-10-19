use crate::common::{error::*, symbol_table::*, token::*, types::*};

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
pub struct Environment {
    pub current: Table<Types, Function>,
    pub enclosing: Option<Box<Environment>>,
}
impl Environment {
    pub fn new(enclosing: Option<Box<Environment>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    pub fn declare_var(&mut self, name: String, type_decl: Types) {
        self.current.vars.insert(name, type_decl);
    }

    pub fn declare_func(&mut self, return_type: Types, name: &str, params: Vec<(Types, Token)>) {
        let f = Function::new(return_type, params);

        self.current.funcs.insert(name.to_string(), f);
    }

    pub fn get_var(&self, var_name: &Token) -> Result<Types, Error> {
        let name = var_name.unwrap_string();
        match self.current.vars.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(var_name),
                None => Err(Error::new(var_name, "undeclared variable")),
            },
        }
    }
    pub fn assign_var(&mut self, var_name: &Token, value: Types) -> Result<Types, Error> {
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
    pub fn init_var(&mut self, name: String, value: Types) {
        self.current.vars.insert(name, value);
    }
}
