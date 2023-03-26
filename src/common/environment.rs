use crate::common::{error::*, token::*, types::*};
use std::collections::HashMap;

pub enum FunctionKind {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq)]
pub struct Function {
    pub params: Vec<(NEWTypes, Token)>,
    pub return_type: NEWTypes,
}
impl Function {
    pub fn new(return_type: NEWTypes, params: Vec<(NEWTypes, Token)>) -> Self {
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
pub enum Symbols<T> {
    Var(T),
    FuncDef(Function),
    FuncDecl(Function),
}
impl<T> Symbols<T> {
    pub fn unwrap_var(self) -> T {
        match self {
            Symbols::Var(v) => v,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Customs {
    // bool indicates wether type is complete or incomplete
    Aggregate(StructRef),
    Enum(Vec<(Token, i32)>),
}
impl Customs {
    pub fn get_kind(&self) -> &TokenType {
        match self {
            Customs::Aggregate(s) => s.get_kind(),
            Customs::Enum(_) => &TokenType::Enum,
        }
    }
    pub fn unwrap_aggr(self) -> StructRef {
        match self {
            Customs::Aggregate(s) => s,
            _ => unreachable!(),
        }
    }
    pub fn unwrap_enum(self) -> Vec<(Token, i32)> {
        match self {
            Customs::Enum(s) => s,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Table<T: EnumValue<T>> {
    pub symbols: HashMap<String, Symbols<T>>,
    pub customs: HashMap<String, Customs>,
}

#[derive(Clone, PartialEq)]
pub struct Environment<T: EnumValue<T>> {
    pub current: Table<T>,
    pub enclosing: Option<Box<Environment<T>>>,
}
impl<T: Clone + EnumValue<T>> Environment<T> {
    pub fn new(enclosing: Option<Box<Environment<T>>>) -> Self {
        Environment {
            current: Table {
                symbols: HashMap::<String, Symbols<T>>::new(),
                customs: HashMap::<String, Customs>::new(),
            },
            enclosing,
        }
    }
    // methods used for typechecker AND codegen
    pub fn declare_var(&mut self, name: String, value: T) {
        self.current.symbols.insert(name, Symbols::Var(value));
    }

    pub fn declare_func(
        &mut self,
        return_type: NEWTypes,
        name: &str,
        params: Vec<(NEWTypes, Token)>,
        kind: FunctionKind,
    ) {
        self.current.symbols.insert(
            name.to_string(),
            match kind {
                FunctionKind::Declaration => Symbols::FuncDecl(Function::new(return_type, params)),
                FunctionKind::Definition => Symbols::FuncDef(Function::new(return_type, params)),
            },
        );
    }

    pub fn get_symbol(&self, var_name: &Token) -> Result<Symbols<T>, Error> {
        let name = var_name.unwrap_string();
        match self.current.symbols.get(&name) {
            Some(v) => Ok(v.clone()),
            None => match &self.enclosing {
                Some(env) => (**env).get_symbol(var_name),
                None => Err(Error::new(var_name, "Undeclared symbol")),
            },
        }
    }
    pub fn get_type(&mut self, var_name: &Token) -> Result<&mut Customs, Error> {
        let name = var_name.unwrap_string();
        match self.current.customs.get_mut(&name) {
            Some(v) => Ok(v),
            None => match &mut self.enclosing {
                Some(env) => (**env).get_type(var_name),
                None => Err(Error::new(var_name, "Undeclared type")),
            },
        }
    }

    // TODO: remove this its same as declare_var
    pub fn init_var(&mut self, name: String, value: T) {
        self.current.symbols.insert(name, Symbols::Var(value));
    }

    pub fn declare_aggregate(&mut self, name: String, token: TokenType) {
        self.current
            .customs
            .insert(name, Customs::Aggregate(StructRef::new(token)));
    }

    pub fn init_enum(&mut self, name: String, members: Vec<(Token, i32)>) {
        self.current.customs.insert(name, Customs::Enum(members));
    }

    pub fn insert_enum_symbols(
        &mut self,
        type_decl: &NEWTypes,
        visited: &mut Vec<NEWTypes>,
    ) -> Result<(), Error> {
        match type_decl {
            NEWTypes::Enum(_, members, true) => {
                for (token, value) in members {
                    let name = token.unwrap_string();
                    if self.current.symbols.contains_key(&name) {
                        return Err(Error::new(
                            token,
                            &format!("Redefinition of symbol '{}'", name),
                        ));
                    }

                    self.declare_var(name, T::enum_value(*value));
                }
            }
            // union definition could be nested deeper into a type
            NEWTypes::Union(s) | NEWTypes::Struct(s) => {
                visited.push(type_decl.clone());

                for m in s.members().iter() {
                    if !visited.contains(&m.0) {
                        self.insert_enum_symbols(&m.0, visited)?
                    }
                }
            }
            NEWTypes::Pointer(to) | NEWTypes::Array { of: to, .. } => {
                if !visited.contains(&to) {
                    self.insert_enum_symbols(to, visited)?
                }
            }
            _ => (),
        }
        Ok(())
    }
}
