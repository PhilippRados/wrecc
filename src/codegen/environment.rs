use crate::codegen::register::{Register, StackRegister};
use crate::common::{symbol_table::*, types::*};

#[derive(Clone)]
pub struct Environment {
    pub current: Table<Register, Types>, // <register on stack for variable, function return type>
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
            Register::Stack(StackRegister::new(current_bp_offset), type_decl),
        );
    }

    pub fn get_var(&self, name: String) -> Register {
        match self.current.vars.get(&name) {
            Some(v) => v.clone(),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(name),
                None => unreachable!("typechecker catches"),
            },
        }
    }
}
