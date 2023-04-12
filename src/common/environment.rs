use crate::codegen::register::*;
use crate::common::{error::*, token::*, types::*};

#[derive(Clone, PartialEq, Debug)]
pub enum FunctionKind {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Function {
    params: Vec<(NEWTypes, Token)>,
    return_type: NEWTypes,

    // how much stack space a function needs to allocate
    // info given in typechecker
    stack_space: usize,

    kind: FunctionKind,
}
impl Function {
    pub fn new(return_type: NEWTypes) -> Self {
        // can only know return-type at point of declaration
        Function {
            stack_space: 0,
            return_type,
            kind: FunctionKind::Definition,
            params: vec![],
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
    pub fn get_kind(self) -> FunctionKind {
        self.kind
    }
    pub fn get_params(self) -> Vec<(NEWTypes, Token)> {
        self.params
    }
    pub fn get_return_type(self) -> NEWTypes {
        self.return_type
    }
    pub fn set_stack_size(&mut self, size: usize) {
        self.stack_space = size
    }
    pub fn get_stack_size(&mut self) -> usize {
        self.stack_space
    }
    pub fn update(&mut self, params: Vec<(NEWTypes, Token)>, kind: FunctionKind) {
        self.params = params;
        self.kind = kind;
    }
    pub fn cmp(&self, token: &Token, other: &Function) -> Result<(), Error> {
        if self.return_type != other.return_type {
            Err(Error::new(
                token,
                &format!(
                    "Conflicting return-types in function-declarations: expected {}, found {}",
                    self.return_type, other.return_type
                ),
            ))
        } else if self.arity() != other.arity() {
            Err(Error::new(
                token,
                &format!(
                "Mismatched number of parameters in function-declarations: expected {}, found {}",
                self.arity(),
                other.arity()
            ),
            ))
        } else {
            for (i, (types, token)) in self.params.iter().enumerate() {
                if *types != other.params[i].0 {
                    return Err(Error::new(token,
                        &format!("Mismatched parameter-types in function-declarations: expected '{}', found '{}'",
                            other.params[i].0,types)));
                }
            }
            Ok(())
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct SymbolInfo {
    // type of identifier given in declaration
    pub type_decl: NEWTypes,

    // optional because info isn't known at moment of insertion
    // stack-register that identifier resides in
    pub reg: Option<Register>,

    // wether or not symbol was declared in global scope
    pub is_global: bool,
}

impl SymbolInfo {
    pub fn new(type_decl: NEWTypes, is_global: bool) -> Self {
        SymbolInfo {
            type_decl,
            is_global,
            reg: None,
        }
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
trait TypeName {
    fn type_name() -> &'static str;
}
#[derive(Clone, PartialEq, Debug)]
pub enum Symbols {
    // also includes enum-constants
    Variable(SymbolInfo),
    TypeDef(NEWTypes),
    Func(Function),
}
impl TypeName for Symbols {
    fn type_name() -> &'static str {
        "symbol"
    }
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
    pub fn is_global(&self) -> bool {
        match self {
            Symbols::Variable(SymbolInfo { is_global, .. }) => *is_global,
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
impl TypeName for Tags {
    fn type_name() -> &'static str {
        "type"
    }
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
}

#[derive(Clone, PartialEq, Debug)]
struct NameSpace<T> {
    // (name, depth, index in table, element)
    elems: Vec<(String, usize, usize, T)>,
}
impl<T: Clone + TypeName + std::fmt::Debug> NameSpace<T> {
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
    fn contains_key(&self, expected: &String, depth: usize) -> bool {
        self.get_current(depth)
            .iter()
            .any(|(name, ..)| name == expected)
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
        Err(Error::new(
            &var_name,
            &format!("Undeclared {} '{}'", T::type_name(), name),
        ))
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
        if self.symbols.contains_key(&name, self.current_depth) {
            return Err(Error::new(
                &var_name,
                &format!("Redefinition of symbol '{}'", name),
            ));
        }
        self.symbols.declare(name, self.current_depth, symbol)
    }
    // function has special checks for Redefinitions because
    // there can be multiple declaration but only a single definition
    pub fn declare_func(&mut self, var_name: &Token, symbol: Symbols) -> Result<usize, Error> {
        self.symbols
            .declare(var_name.unwrap_string(), self.current_depth, symbol)
    }
    pub fn declare_type(&mut self, var_name: &Token, tag: Tags) -> Result<usize, Error> {
        let name = var_name.unwrap_string();
        if self.tags.contains_key(&name, self.current_depth) {
            return Err(Error::new(
                &var_name,
                &format!("Redefinition of type '{}'", name),
            ));
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
        // TODO: convert this better
        match self.tags.get(var_name, self.current_depth) {
            Ok(t) => Ok(t),
            Err(_) => Err(Error::UndeclaredType(var_name.clone())),
        }
    }
    pub fn get_mut_symbol(&mut self, index: usize) -> &mut Symbols {
        &mut self.symbols.elems.get_mut(index).unwrap().3
    }

    pub fn get_symbol_table(self) -> Vec<Symbols> {
        self.symbols
            .elems
            .into_iter()
            .map(|(_, _, _, symbol)| symbol)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
                        is_global: false,
                    }),
                ),
                (
                    "foo".to_string(),
                    2,
                    1,
                    Symbols::Variable(SymbolInfo {
                        type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                        reg: None,
                        is_global: false,
                    }),
                ),
                (
                    "n".to_string(),
                    1,
                    2,
                    Symbols::Variable(SymbolInfo {
                        type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                        reg: None,
                        is_global: false,
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
                    is_global: false,
                }),
            ),
            (
                "s".to_string(),
                1,
                0,
                Symbols::Variable(SymbolInfo {
                    type_decl: NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                    reg: None,
                    is_global: false,
                }),
            ),
        ];
        assert_eq!(actual, expected);
    }
}
