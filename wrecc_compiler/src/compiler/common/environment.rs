//! The symbol-table used to store information about variables and types

use crate::compiler::codegen::register::*;
use crate::compiler::common::{error::*, token::*, types::*};
use crate::compiler::parser::hir::expr::ExprKind;
use crate::compiler::typechecker::mir::decl::StorageClass;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, PartialEq, Debug)]
pub enum InitType {
    Declaration,
    Definition,
}

pub type SymbolRef = Rc<RefCell<Symbol>>;

/// The information stored for a variable in the symbol-table
#[derive(Clone, Debug)]
pub struct Symbol {
    /// Type of identifier given in declaration
    pub type_decl: Type,

    /// Current storage-class of symbol
    pub storage_class: Option<StorageClass>,

    /// Wether the variable is a declaration or initialization
    pub kind: InitType,

    /// Can be label-register or stack-register
    /// optional because info isn't known at moment of insertion
    pub reg: Option<Register>,

    /// Used in codegen to ensure only single declaration of same symbol
    pub token: Token,
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        let placeholder = Token::default(TokenKind::Semicolon);
        self.cmp(&placeholder, other).is_ok()
    }
}
impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.is_typedef() { "typedef" } else { "variable" })
    }
}

impl Symbol {
    pub fn is_typedef(&self) -> bool {
        matches!(self.storage_class, Some(StorageClass::TypeDef))
    }

    pub fn is_static(&self) -> bool {
        matches!(self.storage_class, Some(StorageClass::Static))
    }

    pub fn is_extern(&self) -> bool {
        match self.storage_class {
            Some(StorageClass::Extern) => true,
            None if self.type_decl.is_func() && self.kind == InitType::Declaration => true,
            _ => false,
        }
    }

    pub fn set_reg(&mut self, reg: Register) {
        self.reg = Some(reg)
    }

    pub fn get_reg(&self) -> Register {
        self.reg.clone().unwrap()
    }

    /// Compares current-symbols type to the already existing symbol
    fn cmp(&self, name: &Token, other: &Symbol) -> Result<(), Error> {
        match (&self.type_decl, &other.type_decl) {
            _ if (self.is_typedef() && !other.is_typedef())
                || (!self.is_typedef() && other.is_typedef()) =>
            {
                Err(Error::new(
                    name,
                    ErrorKind::RedefOtherSymbol(name.unwrap_string(), other.to_string()),
                ))
            }
            (ty1 @ Type::Array(..), ty2 @ Type::Array(..))
                if !self.is_typedef()
                    // placeholder expression
                    && ty1.type_compatible(&ty2, &ExprKind::Nop) =>
            {
                Ok(())
            }
            (ty1, ty2) if ty1 != ty2 => Err(Error::new(
                name,
                ErrorKind::RedefTypeMismatch(name.unwrap_string(), ty1.clone(), ty2.clone()),
            )),
            _ => Ok(()),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tags {
    /// Contains struct/union types
    Aggregate(StructRef),
    Enum(Vec<(Token, i32)>),
}
impl Tags {
    pub fn get_kind(&self) -> &TokenKind {
        match self {
            Tags::Aggregate(s) => s.get_kind(),
            Tags::Enum(_) => &TokenKind::Enum,
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

type Scope<T> = HashMap<String, Rc<RefCell<T>>>;

/// A list of scopes which are popped when you exit the scope
#[derive(Clone, Debug)]
pub struct NameSpace<T> {
    elems: Vec<Scope<T>>,
}
impl<T> NameSpace<T> {
    pub fn new() -> Self {
        NameSpace { elems: vec![Scope::new()] }
    }
    pub fn enter(&mut self) {
        self.elems.push(Scope::new());
    }
    pub fn exit(&mut self) {
        self.elems.pop();
    }

    // checks if element is in current scope
    pub fn get_current(&self, expected: &str) -> Option<Rc<RefCell<T>>> {
        self.elems.last().unwrap().get(expected).map(Rc::clone)
    }
    pub fn declare(&mut self, name: String, elem: T) -> Rc<RefCell<T>> {
        let kind = Rc::new(RefCell::new(elem));
        self.elems.last_mut().unwrap().insert(name, Rc::clone(&kind));
        Rc::clone(&kind)
    }
    pub fn get(&self, name: String) -> Option<Rc<RefCell<T>>> {
        for scope in self.elems.iter().rev() {
            if let Some(elem) = scope.get(&name) {
                return Some(Rc::clone(elem));
            }
        }
        None
    }
}

/// The environment is made up of two seperate namespaces, one for storing symbols and another for
/// storing tags when the user declares a type
#[derive(Debug)]
pub struct Environment {
    symbols: NameSpace<Symbol>,
    tags: NameSpace<Tags>,
}
impl Environment {
    pub fn new() -> Self {
        Environment {
            symbols: NameSpace::new(),
            tags: NameSpace::new(),
        }
    }
    pub fn is_global(&self) -> bool {
        self.symbols.elems.len() == 1
    }
    pub fn enter(&mut self) {
        self.symbols.enter();
        self.tags.enter();
    }
    pub fn exit(&mut self) {
        self.symbols.exit();
        self.tags.exit();
    }
    pub fn declare_symbol(&mut self, var_name: &Token, symbol: Symbol) -> Result<SymbolRef, Error> {
        if let Some(existing_symbol) = self.symbols.get_current(&var_name.unwrap_string()) {
            return self.check_redef(var_name, symbol, existing_symbol);
        }

        Ok(self.symbols.declare(var_name.unwrap_string(), symbol))
    }
    // only used for functions since they have to be inserted before params but need params to be
    // already parsed
    pub fn declare_global(&mut self, var_name: &Token, symbol: Symbol) -> Result<SymbolRef, Error> {
        let global_scope = self.symbols.elems.get_mut(0).expect("always have a global scope");

        if let Some(existing_symbol) = global_scope.get(&var_name.unwrap_string()).map(Rc::clone) {
            return self.check_redef(var_name, symbol, existing_symbol);
        }

        let func = Rc::new(RefCell::new(symbol));
        global_scope.insert(var_name.unwrap_string(), Rc::clone(&func));

        Ok(Rc::clone(&func))
    }

    fn check_storage_class_mismatch(
        &self,
        var_name: &Token,
        type_decl: &Type,
        current: &Option<StorageClass>,
        existing: &Option<StorageClass>,
    ) -> Result<(), Error> {
        let mismatch = if self.is_global() {
            match (current, existing) {
                (Some(StorageClass::Static), other) if other != &Some(StorageClass::Static) => {
                    Err(("static", "non-static"))
                }
                (current, Some(StorageClass::Static))
                    if !matches!(current, &Some(StorageClass::Static | StorageClass::Extern)) =>
                {
                    Err(("non-static", "static"))
                }

                _ => Ok(()),
            }
        } else {
            match (current, existing) {
                _ if type_decl.is_func() => Ok(()),
                (current, Some(StorageClass::Extern)) if current != &Some(StorageClass::Extern) => {
                    Err(("non-extern", "extern"))
                }
                (Some(StorageClass::Extern), other) if other != &Some(StorageClass::Extern) => {
                    Err(("extern", "non-extern"))
                }
                (Some(StorageClass::Extern), Some(StorageClass::Extern))
                | (Some(StorageClass::TypeDef), Some(StorageClass::TypeDef)) => Ok(()),
                _ => {
                    return Err(Error::new(
                        var_name,
                        ErrorKind::Redefinition("symbol", var_name.unwrap_string()),
                    ))
                }
            }
        };

        if let Err((current_sc, existing_sc)) = mismatch {
            Err(Error::new(
                var_name,
                ErrorKind::StorageClassMismatch(var_name.unwrap_string(), current_sc, existing_sc),
            ))
        } else {
            Ok(())
        }
    }

    fn check_redef(
        &self,
        var_name: &Token,
        mut current_symbol: Symbol,
        existing_symbol: SymbolRef,
    ) -> Result<SymbolRef, Error> {
        current_symbol.cmp(var_name, &existing_symbol.borrow())?;

        self.check_storage_class_mismatch(
            var_name,
            &current_symbol.type_decl,
            &current_symbol.storage_class,
            &existing_symbol.borrow().storage_class,
        )?;

        let existing_kind = existing_symbol.borrow().kind.clone();

        match (&current_symbol.kind, existing_kind) {
            (InitType::Definition, InitType::Declaration)
            | (InitType::Declaration, InitType::Declaration) => {
                // make sure that current symbol has known array-size if existing array-size was
                // was known
                if !current_symbol.is_typedef() && current_symbol.type_decl.is_unbounded_array() {
                    current_symbol.type_decl = existing_symbol.borrow().type_decl.clone();
                }

                // can only happen if current symbol is empty or extern and existing is static
                if matches!(existing_symbol.borrow().storage_class, Some(StorageClass::Static)) {
                    current_symbol.storage_class = Some(StorageClass::Static);
                }

                *existing_symbol.borrow_mut() = current_symbol;
                Ok(existing_symbol)
            }

            (InitType::Declaration, InitType::Definition) => Ok(existing_symbol),

            (InitType::Definition, InitType::Definition) => Err(Error::new(
                var_name,
                ErrorKind::Redefinition("symbol", var_name.unwrap_string()),
            )),
        }
    }

    pub fn declare_type(&mut self, var_name: &Token, tag: Tags) -> Result<Rc<RefCell<Tags>>, Error> {
        let name = var_name.unwrap_string();
        match self.tags.get_current(&name) {
            Some(existing_tag)
                if existing_tag.borrow().is_complete() || existing_tag.borrow().in_definition() =>
            {
                return Err(Error::new(var_name, ErrorKind::Redefinition("type", name)));
            }
            Some(existing_tag) if matches!(*existing_tag.borrow(), Tags::Aggregate(_)) => {
                // if tag is being defined then set other_tag to being defined
                let Tags::Aggregate(other_s) = &*existing_tag.borrow_mut() else {
                    unreachable!("just checked if match aggregate")
                };
                if let Tags::Aggregate(s) = tag {
                    if s.in_definition() {
                        other_s.being_defined();
                    }
                }
                return Ok(Rc::clone(&existing_tag));
            }
            Some(existing_tag) => return Ok(existing_tag),
            _ => (),
        }
        Ok(self.tags.declare(name, tag))
    }
    pub fn get_symbol(&self, var_name: &Token) -> Result<SymbolRef, Error> {
        self.symbols
            .get(var_name.unwrap_string())
            .ok_or_else(|| Error::new(var_name, ErrorKind::UndeclaredSymbol(var_name.unwrap_string())))
    }
    pub fn get_type(&self, var_name: &Token) -> Result<Rc<RefCell<Tags>>, Error> {
        self.tags
            .get(var_name.unwrap_string())
            .ok_or_else(|| Error::new(var_name, ErrorKind::UndeclaredType(var_name.unwrap_string())))
    }

    pub fn check_remaining_tentatives(&self) -> Result<(), Vec<Error>> {
        let globals = self.symbols.elems.get(0).expect("global scope never popped");
        let mut errors = Vec::new();

        for symbol in globals.values() {
            if !symbol.borrow().type_decl.is_unbounded_array()
                && !symbol.borrow().type_decl.is_complete()
                && !matches!(symbol.borrow().storage_class, Some(StorageClass::Extern))
            {
                errors.push(Error::new(
                    &symbol.borrow().token,
                    ErrorKind::IncompleteTentative(symbol.borrow().type_decl.clone()),
                ));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
#[rustfmt::skip]
pub mod tests {
    use super::*;
    use crate::setup_type;

    macro_rules! symbol {
        ($name:expr,$ty:expr,$kind:expr) => {{
            let token = Token::default(TokenKind::Ident($name.to_string()));
            let symbol = Symbol {
                kind:$kind,
                storage_class:None,
                token: token.clone(),
                type_decl: setup_type!($ty),
                reg: None,
            };
            (token, symbol)
        }};

        ($name:expr,$ty:expr,$kind:expr,$sc:expr) => {{
            let token = Token::default(TokenKind::Ident($name.to_string()));
            let symbol = Symbol {
                kind:$kind,
                storage_class:Some($sc),
                token: token.clone(),
                type_decl: setup_type!($ty),
                reg: None,
            };
            (token, symbol)
        }};
    }

    fn declare(env: &mut Environment, (token, symbol): (Token, Symbol), global: bool) -> Result<SymbolRef,Error>{
        match global {
            true => env.declare_global(&token, symbol),
            false => env.declare_symbol(&token, symbol),
        }
    }

    #[test]
    fn builds_symbol_table() {
        // int main(){
        //     char* s;
        //     {
        //         char* n;
        //     }
        //     char* n;
        // };

        let mut env = Environment::new();

        env.enter();
        declare(&mut env, symbol!("main","int()", InitType::Definition), true).unwrap();
        assert!(env.symbols.get_current("main").is_none());

        declare(&mut env,symbol!("s", "char*", InitType::Declaration),false).unwrap();
        assert!(env.symbols.get_current("s").is_some());

        env.enter();
        declare(&mut env,symbol!("n", "int", InitType::Declaration),false).unwrap();
        assert!(env.symbols.get_current("n").is_some());
        assert!(env.symbols.get_current("s").is_none());
        env.exit();

        assert!(env.symbols.get_current("s").is_some());

        declare(&mut env,symbol!("n", "long", InitType::Declaration),false).unwrap();
        assert!(matches!(
            env.symbols.get_current("n").map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl: Type::Primitive(Primitive::Long),..})
        ));
        assert!(env.symbols.get_current("s").is_some());

        env.exit();
        assert!(env.symbols.get_current("main").is_some());
    }

    #[test]
    fn func_args() {
        // int foo(int a, int b) {
        //     {
        //         {
        //             long some;
        //         }
        //     }
        //     return 2 + a - b;
        // }
        // int main() {
        // 	   return foo(1, 3);
        // }

        let mut env = Environment::new();

        env.enter();
        declare(&mut env,symbol!("a", "int", InitType::Declaration),false).unwrap();
        declare(&mut env,symbol!("b", "int", InitType::Declaration),false).unwrap();

        declare(&mut env, symbol!("foo","int (int,int)", InitType::Definition), true).unwrap();
        assert!(env.symbols.get_current("foo").is_none());
        assert!(env.symbols.get_current("a").is_some());
        assert!(env.symbols.get_current("b").is_some());

        env.enter();
        assert!(env.symbols.get_current("foo").is_none());
        assert!(env.symbols.get_current("a").is_none());
        env.enter();
        declare(&mut env,symbol!("some", "long", InitType::Declaration),false).unwrap();
        assert!(env.symbols.get("some".to_string()).is_some());
        assert!(env.symbols.get("a".to_string()).is_some());
        assert!(env.symbols.get("foo".to_string()).is_some());

        env.exit();
        assert!(env.symbols.get("some".to_string()).is_none());
        env.exit();
        env.exit();

        declare(&mut env, symbol!("main","int ()", InitType::Definition), true).unwrap();

        assert!(env.symbols.get_current("a").is_none());
        assert!(env.symbols.get_current("foo").is_some());
        assert!(env.symbols.get_current("main").is_some());
    }

    #[test]
    fn func_decls() {
        // int main() {
        //     int a;
        //     {
        //         long a;
        //         {
        //             int foo(char a, int b);
        //         }
        //     }
        // 	return foo(1, 3);
        // }
        let mut env = Environment::new();

        env.enter();
        declare(&mut env, symbol!("main","int ()", InitType::Definition), true).unwrap();
        declare(&mut env, symbol!("a", "int", InitType::Declaration),false).unwrap();
        env.enter();
        assert!(env.symbols.get_current("a").is_none());
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl:Type::Primitive(Primitive::Int),..})
        ));

        declare(&mut env, symbol!("a", "long", InitType::Declaration),false).unwrap();
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl:Type::Primitive(Primitive::Long),..})
        ));
        env.enter();

        env.enter();
        declare(&mut env,symbol!("a", "char", InitType::Declaration),false).unwrap();
        declare(&mut env,symbol!("b", "int", InitType::Declaration),false).unwrap();
        env.exit();
        declare(&mut env, symbol!("foo","int (char, int)", InitType::Declaration), false).unwrap();

        assert!(env.symbols.get_current("a").is_none());
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl:Type::Primitive(Primitive::Long),..})
        ));
        assert!(env.symbols.get("foo".to_string()).is_some());

        env.exit();
        assert!(env.symbols.get("foo".to_string()).is_none());
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl:Type::Primitive(Primitive::Long),..})
        ));
        env.exit();
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {type_decl:Type::Primitive(Primitive::Int),..})
        ));
        env.exit();

        assert!(env.symbols.get("main".to_string()).is_some());
        assert!(env.symbols.get("foo".to_string()).is_none());
    }

    #[test]
    fn redeclarations() {
        let mut env = Environment::new();

        declare(&mut env, symbol!("foo","int ()",InitType::Declaration), true).unwrap();
        declare(&mut env, symbol!("foo","int ()",InitType::Definition), true).unwrap();
        declare(&mut env, symbol!("foo","int ()",InitType::Declaration), true).unwrap();

        assert!(declare(&mut env, symbol!("foo","int ()", InitType::Definition), true).is_err());

        env.enter();
        assert!(matches!(
            env.symbols.get("foo".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {kind:InitType::Definition,type_decl:Type::Function(_),..}
        )));
        assert!(env.symbols.get_current("foo").is_none());

        declare(&mut env, symbol!("bar","void ()", InitType::Declaration), false).unwrap();
        assert!(declare(&mut env, symbol!("bar","void ()", InitType::Declaration), false).is_ok());

        declare(&mut env, symbol!("baz", "int", InitType::Declaration), false).unwrap();
        assert!(declare(&mut env, symbol!("baz", "int", InitType::Declaration), false).is_err());
        assert!(declare(&mut env, symbol!("baz", "int", InitType::Definition), false).is_err());

        env.exit();

        declare(&mut env, symbol!("baz", "int", InitType::Declaration), false).unwrap();
        assert!(declare(&mut env, symbol!("baz", "int", InitType::Declaration), false).is_ok());
        assert!(declare(&mut env, symbol!("baz", "int", InitType::Definition), false).is_ok());
        assert!(declare(&mut env, symbol!("baz", "long", InitType::Declaration), false).is_err());

    }
}
