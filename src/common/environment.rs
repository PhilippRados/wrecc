use crate::codegen::register::*;
use crate::common::{error::*, token::*, types::*};
use std::collections::HashMap;

#[derive(Clone, PartialEq, Debug)]
pub enum FunctionKind {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Function {
    pub params: Vec<(NEWTypes, Token)>,
    pub return_type: NEWTypes,

    // if function contains var-args
    pub variadic: bool,

    // how much stack space a function needs to allocate info given in typechecker
    pub stack_size: usize,

    // can either be definition/declaration
    pub kind: FunctionKind,

    // all the goto-labels that are unique to that function
    pub labels: HashMap<String, usize>,

    // index of epilogue label in function
    pub epilogue_index: usize,
}
impl Function {
    pub fn new(return_type: NEWTypes) -> Self {
        // can only know return-type at point of declaration
        Function {
            stack_size: 0,
            epilogue_index: 0,
            variadic: false,
            return_type,
            kind: FunctionKind::Declaration,
            params: vec![],
            labels: HashMap::new(),
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
    pub fn cmp(&self, token: &Token, other: &Function) -> Result<(), Error> {
        if self.return_type != other.return_type {
            Err(Error::new(
                token,
                ErrorKind::MismatchedFuncDeclReturn(
                    self.return_type.clone(),
                    other.return_type.clone(),
                ),
            ))
        } else if self.arity() != other.arity() {
            Err(Error::new(
                token,
                ErrorKind::MismatchedFuncDeclArity(self.arity(), other.arity()),
            ))
        } else if self.variadic != other.variadic {
            Err(Error::new(
                token,
                ErrorKind::MismatchedVariadic(self.variadic, other.variadic),
            ))
        } else {
            for (i, (types, token)) in self.params.iter().enumerate() {
                if *types != other.params[i].0 {
                    return Err(Error::new(
                        token,
                        ErrorKind::TypeMismatchFuncDecl(other.params[i].0.clone(), types.clone()),
                    ));
                }
            }
            Ok(())
        }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolInfo {
    // type of identifier given in declaration
    pub type_decl: NEWTypes,

    // optional because info isn't known at moment of insertion
    // stack-register that identifier resides in
    pub reg: Option<Register>,
}

impl SymbolInfo {
    pub fn new(type_decl: NEWTypes) -> Self {
        SymbolInfo { type_decl, reg: None }
    }
    pub fn get_type(&self) -> NEWTypes {
        self.type_decl.clone()
    }
    pub fn get_reg(&self) -> Register {
        self.reg.clone().unwrap()
    }
    pub fn set_reg(&mut self, reg: Register) {
        self.reg = Some(reg)
    }
}
#[derive(Clone, Debug)]
pub enum Symbols {
    // also includes enum-constants
    Variable(SymbolInfo),
    TypeDef(NEWTypes),
    Func(Function),
}
impl Symbols {
    pub fn unwrap_var_mut(&mut self) -> &mut SymbolInfo {
        match self {
            Symbols::Variable(s) => s,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
    pub fn unwrap_var(&self) -> &SymbolInfo {
        match self {
            Symbols::Variable(s) => s,
            _ => unreachable!("cant unwrap var on func"),
        }
    }
    pub fn unwrap_func(&mut self) -> &mut Function {
        match self {
            Symbols::Func(f) => f,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tags {
    // struct/union
    Aggregate(StructRef),
    Enum(Vec<(Token, i32)>),
}
impl Tags {
    pub fn get_kind(&self) -> &TokenType {
        match self {
            Tags::Aggregate(s) => s.get_kind(),
            Tags::Enum(_) => &TokenType::Enum,
        }
    }
    pub fn unwrap_aggr(self) -> StructRef {
        match self {
            Tags::Aggregate(s) => s,
            _ => unreachable!(),
        }
    }
    pub fn unwrap_enum(self) -> Vec<(Token, i32)> {
        match self {
            Tags::Enum(s) => s,
            _ => unreachable!(),
        }
    }
    pub fn is_complete(&self) -> bool {
        match self {
            Tags::Aggregate(s) => s.is_complete(),
            Tags::Enum(_) => true, // can't forward declare enums according to ISO C
        }
    }

    pub fn in_definition(&self) -> bool {
        match self {
            Tags::Aggregate(s) => s.in_definition(),
            Tags::Enum(_) => {
                unreachable!("enums are always complete so declare_type() short circuits")
            }
        }
    }
}

#[derive(Clone, Debug)]
struct NameSpace<T> {
    // (name, depth, index in table, element)
    elems: Vec<(String, usize, usize, T)>,
}
impl<T: Clone + std::fmt::Debug> NameSpace<T> {
    fn new() -> Self {
        NameSpace { elems: vec![] }
    }
    // return sub-array of elements that are in current scope
    fn get_current(&self, depth: usize) -> Vec<&(String, usize, usize, T)> {
        self.elems
            .iter()
            .rev()
            .take_while(|(_, d, ..)| *d >= depth)
            .filter(|(_, d, ..)| *d == depth)
            .collect()
    }

    // checks if element is in current scope
    fn contains_key(&self, expected: &String, depth: usize) -> Option<&(String, usize, usize, T)> {
        self.get_current(depth)
            .into_iter()
            .find(|(name, ..)| name == expected)
    }
    fn declare(&mut self, name: String, depth: usize, element: T) -> Result<usize, Error> {
        self.elems.push((name, depth, self.elems.len(), element));
        Ok(self.elems.len() - 1)
    }
    // returns a specific element and its index in st from all valid scopes
    fn get(&self, var_name: &Token, depth: usize) -> Result<(T, usize), Error> {
        let name = var_name.unwrap_string();
        for d in (0..=depth).rev() {
            if let Some((_, _, i, v)) = self.get_current(d).iter().find(|(id, ..)| *id == name) {
                return Ok((v.clone(), *i));
            }
        }
        // can only be symbol because type throws a special error
        Err(Error::new(var_name, ErrorKind::UndeclaredSymbol(name)))
    }
}

#[derive(Debug)]
pub struct Scope {
    current_depth: usize,
    symbols: NameSpace<Symbols>,
    tags: NameSpace<Tags>,
}
impl Scope {
    pub fn new() -> Self {
        Scope {
            current_depth: 0,
            symbols: NameSpace::new(),
            tags: NameSpace::new(),
        }
    }
    pub fn is_global(&self) -> bool {
        self.current_depth == 0
    }
    pub fn enter(&mut self) {
        self.current_depth += 1
    }
    pub fn exit(&mut self) {
        self.current_depth -= 1;

        // TODO: clean this up
        // hacky solution but need a way to indicate when current env ends
        let _ = self.symbols.declare(
            "".to_string(),
            self.current_depth,
            Symbols::TypeDef(NEWTypes::Primitive(Types::Void)),
        );
        let _ = self
            .tags
            .declare("".to_string(), self.current_depth, Tags::Enum(vec![]));
    }
    pub fn declare_symbol(&mut self, var_name: &Token, symbol: Symbols) -> Result<usize, Error> {
        let name = var_name.unwrap_string();
        if self
            .symbols
            .contains_key(&name, self.current_depth)
            .is_some()
        {
            return Err(Error::new(
                var_name,
                ErrorKind::Redefinition("symbol", name),
            ));
        }
        self.symbols.declare(name, self.current_depth, symbol)
    }
    // function has special checks for Redefinitions because
    // there can be multiple declarations but only a single definition
    pub fn declare_func(&mut self, var_name: &Token, symbol: Symbols) -> Result<usize, Error> {
        self.symbols
            .declare(var_name.unwrap_string(), self.current_depth, symbol)
    }
    pub fn declare_type(&mut self, var_name: &Token, tag: Tags) -> Result<usize, Error> {
        let name = var_name.unwrap_string();
        match self.tags.contains_key(&name, self.current_depth) {
            Some((.., other_tag)) if other_tag.is_complete() || other_tag.in_definition() => {
                return Err(Error::new(var_name, ErrorKind::Redefinition("type", name)));
            }
            Some((.., index, Tags::Aggregate(other_s))) => {
                // if tag is being defined then set other_tag to being defined
                if let Tags::Aggregate(s) = tag {
                    if s.in_definition() {
                        other_s.being_defined();
                    }
                }
                return Ok(*index);
            }
            Some((.., index, _)) => return Ok(*index),
            _ => (),
        }
        self.tags.declare(name, self.current_depth, tag)
    }
    pub fn get_symbol(&self, var_name: &Token) -> Result<(Symbols, usize), Error> {
        self.symbols.get(var_name, self.current_depth)
    }
    pub fn remove_symbol(&mut self, index: usize) {
        self.symbols.elems.remove(index);
    }
    pub fn get_type(&self, var_name: &Token) -> Result<(Tags, usize), Error> {
        self.tags
            .get(var_name, self.current_depth)
            .or(Err(Error::new(
                var_name,
                ErrorKind::UndeclaredType(var_name.unwrap_string()),
            )))
    }
    pub fn get_mut_symbol(&mut self, index: usize) -> &mut Symbols {
        &mut self.symbols.elems.get_mut(index).unwrap().3
    }
    pub fn get_mut_type(&mut self, index: usize) -> &mut Tags {
        &mut self.tags.elems.get_mut(index).unwrap().3
    }

    pub fn get_symbols_ref(&self) -> Vec<&Symbols> {
        self.symbols
            .elems
            .iter()
            .map(|(.., symbol)| symbol)
            .collect()
    }

    pub fn get_symbols(self) -> Vec<Symbols> {
        self.symbols
            .elems
            .into_iter()
            .map(|(.., symbol)| symbol)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl PartialEq for Symbols {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Symbols::Variable(v1), Symbols::Variable(v2)) => v1.type_decl == v2.type_decl,
                (Symbols::TypeDef(t1), Symbols::TypeDef(t2)) => t1 == t2,
                (Symbols::Func(t1), Symbols::Func(t2)) => t1 == t2,
                _ => false,
            }
        }
    }

    #[test]
    fn get_current_env() {
        let namespace = NameSpace {
            elems: vec![
                (
                    "s".to_string(),
                    1,
                    0,
                    Symbols::Variable(SymbolInfo {
                        type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                        reg: None,
                    }),
                ),
                (
                    "foo".to_string(),
                    2,
                    1,
                    Symbols::Variable(SymbolInfo {
                        type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                        reg: None,
                    }),
                ),
                (
                    "n".to_string(),
                    1,
                    2,
                    Symbols::Variable(SymbolInfo {
                        type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                        reg: None,
                    }),
                ),
            ],
        };

        let actual = namespace
            .get_current(1)
            .into_iter()
            .map(|e| e.clone())
            .collect::<Vec<(String, usize, usize, Symbols)>>();
        let expected = vec![
            (
                "n".to_string(),
                1,
                2,
                Symbols::Variable(SymbolInfo {
                    type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                    reg: None,
                }),
            ),
            (
                "s".to_string(),
                1,
                0,
                Symbols::Variable(SymbolInfo {
                    type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                    reg: None,
                }),
            ),
        ];
        assert_eq!(actual, expected);
    }
}
