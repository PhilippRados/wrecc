use crate::codegen::register::StackRegister;
use crate::common::{symbol_table::*, types::*};

#[derive(Clone, PartialEq)]
pub struct Variable {
    pub register: StackRegister,
    pub type_decl: Types,
}

#[derive(Clone, PartialEq)]
pub struct Environment {
    pub current: Table<Variable, Types>, // <register on stack for variable, function return type>
    pub enclosing: Option<Box<Environment>>,
}
impl Environment {
    pub fn new(enclosing: Option<Box<Environment>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    pub fn declare_var(&mut self, name: String, current_bp_offset: usize, type_decl: Types) {
        self.current.vars.insert(
            name,
            Variable {
                register: StackRegister::new(current_bp_offset),
                type_decl,
            },
        );
    }

    pub fn get_var(&self, name: String) -> Variable {
        match self.current.vars.get(&name) {
            Some(v) => v.clone(),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(name),
                None => unreachable!("typechecker catches"),
            },
        }
    }

    pub fn declare_func(&mut self, name: String, return_type: Types) {
        self.current.funcs.insert(name.to_string(), return_type);
    }

    pub fn get_func(&self, name: String) -> Types {
        assert!(self.enclosing == None, "current env isnt global");
        *self.current.funcs.get(&name).unwrap()
    }
}
