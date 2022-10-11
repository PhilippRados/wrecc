use crate::codegen::StackRegister;
use crate::error::Error;
use crate::interpreter::*;
use crate::token::Token;
// use crate::types::TypeValues;
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
    // pub fn call(&self, interpreter: &mut Interpreter, args: Vec<TypeValues>) -> TypeValues {
    //     let mut env = Environment::new(Some(Box::new(interpreter.env.clone())));
    //     self.params.iter().enumerate().for_each(|(i, (_, name))| {
    //         env.init_var(name.unwrap_string(), args[i].clone()).unwrap()
    //     });

    //     match interpreter.execute_block(&self.body, env) {
    //         Ok(_) => TypeValues::Void,
    //         Err(return_val) => return_val.unwrap_or(TypeValues::Void),
    //     }
    // }
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
pub struct Environment {
    pub current: Table<Types>,
    pub enclosing: Option<Box<Environment>>,
}
impl Environment {
    pub fn new(enclosing: Option<Box<Environment>>) -> Self {
        Environment {
            current: Table::new(),
            enclosing,
        }
    }
    pub fn declare_var(&mut self, type_decl: Types, name: String) {
        self.current.vars.insert(name, type_decl);
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

#[derive(Clone, PartialEq)]
pub struct CgEnv {
    pub current: HashMap<String, StackRegister>,
    pub enclosing: Option<Box<CgEnv>>,
    current_bp_offset: i32,
}
impl CgEnv {
    pub fn new(enclosing: Option<Box<CgEnv>>) -> Self {
        CgEnv {
            current: HashMap::new(),
            current_bp_offset: 0,
            enclosing,
        }
    }
    pub fn reset_bp_offset(&mut self) {
        self.current_bp_offset = 0;
    }
    pub fn declare_var(&mut self, type_decl: &Types, name: String) {
        self.current_bp_offset -= type_decl.size();
        // let reg = format!("{}(%rbp)", self.bp_offset);
        self.current
            .insert(name, StackRegister::new(self.current_bp_offset));
    }

    pub fn get_var(&self, name: String) -> StackRegister {
        match self.current.get(&name) {
            Some(v) => v.clone(),
            None => match &self.enclosing {
                Some(env) => (**env).get_var(name),
                None => unreachable!("typechecker should catch"),
            },
        }
    }
    // pub fn assign_var(&mut self, name: String, value: &str) -> i32 {
    //     match self.current.contains_key(&name) {
    //         true => {
    //             // self.current.insert(name, value);
    //             value
    //         }
    //         false => match &mut self.enclosing {
    //             Some(env) => env.assign_var(name, value),
    //             None => unreachable!("typechecker should catch"),
    //         },
    //     }
    // }
    pub fn init_var(&mut self, type_decl: &Types, name: String) -> StackRegister {
        self.current_bp_offset -= type_decl.size();
        let stack_reg = StackRegister::new(self.current_bp_offset);
        // let reg_dest = format!("{}(%rbp)", self.bp_offset);
        self.current.insert(name, stack_reg.clone());
        stack_reg

        // format!("\tmovq    {}, {}", reg_value, reg_dest)
    }
}
