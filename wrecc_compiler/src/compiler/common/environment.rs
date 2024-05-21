//! The symbol-table used to store information about variables and types

use crate::compiler::codegen::register::*;
use crate::compiler::common::{error::*, token::*, types::*};
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
    pub qtype: QualType,

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

    pub fn is_register(&self) -> bool {
        matches!(self.storage_class, Some(StorageClass::Register))
    }

    pub fn is_extern(&self) -> bool {
        match self.storage_class {
            Some(StorageClass::Extern) => true,
            None if self.qtype.ty.is_func() && self.kind == InitType::Declaration => true,
            _ => false,
        }
    }

    pub fn set_reg(&mut self, reg: Register) {
        self.reg = Some(reg)
    }

    pub fn get_reg(&self) -> Register {
        self.reg.clone().unwrap()
    }

    /// Compares current symbols type to the already existing symbol
    fn cmp(&self, name: &Token, other: &Symbol) -> Result<(), Error> {
        match (&self.qtype, &other.qtype) {
            _ if (self.is_typedef() && !other.is_typedef())
                || (!self.is_typedef() && other.is_typedef()) =>
            {
                Err(Error::new(
                    name,
                    ErrorKind::RedefOtherSymbol(name.unwrap_string(), other.to_string()),
                ))
            }
            (qtype1, qtype2) => {
                // HACK: because arrays are considered equal if their sizes match, have to compare the
                // types' string represantation to exactly compare two types
                // necessary because:
                // `int arr[]; int arr[2]` is valid but
                // `typedef int arr[]; typedef int arr[2]` is not
                // WARN: but this doesn't allow typedefs of function declarations with
                // mismatched qualifiers: `typedef int f(const int); typedef int f(int)`
                let exact_equal = qtype1.to_string() == qtype2.to_string();
                let equal = qtype1 == qtype2;

                if !equal || (self.is_typedef() && !exact_equal) {
                    Err(Error::new(
                        name,
                        ErrorKind::RedefTypeMismatch(
                            name.unwrap_string(),
                            qtype1.clone(),
                            qtype2.clone(),
                        ),
                    ))
                } else {
                    Ok(())
                }
            }
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
        current: &Option<StorageClass>,
        existing: &Option<StorageClass>,
        is_func: bool,
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
                // local function-decl can only be extern
                _ if is_func => Ok(()),
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
            &current_symbol.storage_class,
            &existing_symbol.borrow().storage_class,
            current_symbol.qtype.ty.is_func(),
        )?;

        let existing_kind = existing_symbol.borrow().kind.clone();

        match (&current_symbol.kind, existing_kind) {
            (InitType::Definition, InitType::Declaration)
            | (InitType::Declaration, InitType::Declaration) => {
                // make sure that current symbol has known array-size if existing array-size was
                // was known
                if !current_symbol.is_typedef() && current_symbol.qtype.ty.is_unbounded_array() {
                    current_symbol.qtype = existing_symbol.borrow().qtype.clone();
                }

                // storage classes with extern are either extern or existing storage-class
                if (!current_symbol.qtype.ty.is_func()
                    && matches!(current_symbol.storage_class, Some(StorageClass::Extern)))
                    || (current_symbol.qtype.ty.is_func()
                        && existing_symbol.borrow().storage_class.is_some())
                {
                    current_symbol.storage_class = existing_symbol.borrow().storage_class.clone();
                }

                *existing_symbol.borrow_mut() = current_symbol;
                Ok(existing_symbol)
            }

            (InitType::Declaration, InitType::Definition) => {
                if current_symbol.qtype.ty.is_func() && existing_symbol.borrow().storage_class.is_none()
                {
                    existing_symbol.borrow_mut().storage_class = current_symbol.storage_class;
                }

                Ok(existing_symbol)
            }

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
            let qtype = &symbol.borrow().qtype;

            if !qtype.ty.is_complete()
                && !qtype.ty.is_unbounded_array()
                && !qtype.ty.is_void()
                && !matches!(symbol.borrow().storage_class, Some(StorageClass::Extern))
            {
                errors.push(Error::new(
                    &symbol.borrow().token,
                    ErrorKind::IncompleteTentative(symbol.borrow().qtype.clone()),
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
                qtype: setup_type!($ty),
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
                qtype: setup_type!($ty),
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
        //         int n;
        //     }
        //     long n;
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
            Some(Symbol {qtype: QualType{ty:Type::Primitive(Primitive::Long(false)),..},..})
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
            Some(Symbol {qtype:QualType{ty:Type::Primitive(Primitive::Int(false)),..},..})
        ));

        declare(&mut env, symbol!("a", "long", InitType::Declaration),false).unwrap();
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {qtype:QualType{ty:Type::Primitive(Primitive::Long(false)),..},..})
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
            Some(Symbol {qtype:QualType{ty:Type::Primitive(Primitive::Long(false)),..},..})
        ));
        assert!(env.symbols.get("foo".to_string()).is_some());

        env.exit();
        assert!(env.symbols.get("foo".to_string()).is_none());
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {qtype:QualType{ty:Type::Primitive(Primitive::Long(false)),..},..})
        ));
        env.exit();
        assert!(matches!(
            env.symbols.get("a".to_string()).map(|sy|sy.borrow().clone()),
            Some(Symbol {qtype:QualType{ty:Type::Primitive(Primitive::Int(false)),..},..})
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
            Some(Symbol {kind:InitType::Definition,qtype:QualType{ty:Type::Function(_),..},..}
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

    #[test]
    fn global_static_redeclarations(){
        let mut env = Environment::new();

        declare(&mut env,symbol!("foo","int",InitType::Declaration,StorageClass::Static),true).unwrap();
        declare(&mut env,symbol!("foo","int",InitType::Definition,StorageClass::Static),true).unwrap();
        let symbol = declare(&mut env,symbol!("foo","int",InitType::Declaration,StorageClass::Extern),true).unwrap();

        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Static)));
        assert!(matches!(declare(&mut env,symbol!("foo","int",InitType::Definition,StorageClass::Static),true),Err(Error {kind:ErrorKind::Redefinition(..),..})));
        assert!(matches!(declare(&mut env,symbol!("foo","int",InitType::Declaration),true),Err(Error {kind:ErrorKind::StorageClassMismatch(_,"non-static","static"),..})));

        declare(&mut env,symbol!("bar","int",InitType::Definition),true).unwrap();
        assert!(matches!(declare(&mut env,symbol!("bar","int",InitType::Declaration,StorageClass::Static),true),Err(Error {kind:ErrorKind::StorageClassMismatch(_,"static","non-static"),..})));

        declare(&mut env,symbol!("baz","int",InitType::Declaration,StorageClass::Extern),true).unwrap();
        assert!(matches!(declare(&mut env,symbol!("baz","int",InitType::Declaration,StorageClass::Static),true),Err(Error {kind:ErrorKind::StorageClassMismatch(_,"static","non-static"),..})));
    }

    #[test]
    fn global_extern_redeclarations() {
        let mut env = Environment::new();

        declare(&mut env,symbol!("foo","int",InitType::Declaration,StorageClass::Extern),true).unwrap();
        let symbol = declare(&mut env,symbol!("foo","int",InitType::Declaration,StorageClass::Extern),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Extern)));

        let symbol = declare(&mut env,symbol!("foo","int",InitType::Declaration),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,None));

        declare(&mut env,symbol!("bar","int",InitType::Declaration),true).unwrap();
        let symbol = declare(&mut env,symbol!("bar","int",InitType::Declaration,StorageClass::Extern),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,None));

        declare(&mut env,symbol!("baz","int",InitType::Declaration,StorageClass::Extern),true).unwrap();
        let symbol = declare(&mut env,symbol!("baz","int",InitType::Definition),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,None));
    }

    #[test]
    fn local_storage_classes() {
        let mut env = Environment::new();

        env.enter();
        declare(&mut env,symbol!("baz","int",InitType::Declaration,StorageClass::Extern),false).unwrap();
        declare(&mut env,symbol!("baz","int",InitType::Declaration,StorageClass::Extern),false).unwrap();

        declare(&mut env,symbol!("foo","int",InitType::Declaration),false).unwrap();
        assert!(matches!(declare(&mut env,symbol!("foo","int",InitType::Declaration,StorageClass::Extern),false),Err(Error {kind:ErrorKind::StorageClassMismatch(_,"extern","non-extern"),..})));

        declare(&mut env,symbol!("bar","int",InitType::Declaration,StorageClass::Extern),false).unwrap();
        assert!(matches!(declare(&mut env,symbol!("bar","int",InitType::Declaration),false),Err(Error {kind:ErrorKind::StorageClassMismatch(_,"non-extern","extern"),..})));

        declare(&mut env,symbol!("goo","int ()",InitType::Declaration,StorageClass::Extern),false).unwrap();
        declare(&mut env,symbol!("goo","int ()",InitType::Declaration),false).unwrap();
        declare(&mut env,symbol!("goo","int ()",InitType::Declaration,StorageClass::Extern),false).unwrap();

        declare(&mut env,symbol!("gaa","int",InitType::Declaration,StorageClass::Auto),false).unwrap();
        assert!(matches!(declare(&mut env,symbol!("gaa","int",InitType::Definition,StorageClass::Auto),false),Err(Error {kind:ErrorKind::Redefinition(..),..})));
        assert!(matches!(declare(&mut env,symbol!("gaa","int",InitType::Declaration),false),Err(Error {kind:ErrorKind::Redefinition(..),..})));
        env.exit();
    }

    #[test]
    fn func_storage_classes() {
        let mut env = Environment::new();

        declare(&mut env,symbol!("goo","int ()",InitType::Definition),true).unwrap();
        let symbol = declare(&mut env,symbol!("goo","int ()",InitType::Declaration,StorageClass::Extern),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Extern)));

        declare(&mut env,symbol!("foo","int ()",InitType::Declaration,StorageClass::Extern),true).unwrap();
        let symbol = declare(&mut env,symbol!("foo","int ()",InitType::Definition),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Extern)));

        declare(&mut env,symbol!("zoo","int ()",InitType::Declaration,StorageClass::Extern),true).unwrap();
        let symbol = declare(&mut env,symbol!("zoo","int ()",InitType::Declaration),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Extern)));

        declare(&mut env,symbol!("boo","int ()",InitType::Declaration),true).unwrap();
        let symbol = declare(&mut env,symbol!("boo","int ()",InitType::Declaration,StorageClass::Extern),true).unwrap();
        assert!(matches!(symbol.borrow().storage_class,Some(StorageClass::Extern)));
    }
}
