use crate::compiler::common::{error::*, token::*, types::*};
use crate::compiler::wrecc_codegen::register::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, PartialEq, Debug)]
pub enum InitType {
    Declaration,
    Definition,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Function {
    // parameters to a function with it's corresponding name
    // a parameter-name is optional in a function declaration
    pub params: Vec<(NEWTypes, Option<Token>)>,

    pub return_type: NEWTypes,

    // if function contains var-args
    pub variadic: bool,

    // how much stack space a function needs to allocate info given in typechecker
    pub stack_size: usize,

    // can either be definition/declaration
    pub kind: InitType,

    // all the goto-labels that are unique to that function
    pub labels: HashMap<String, usize>,

    // index of epilogue label in function
    pub epilogue_index: usize,
}
impl Function {
    pub fn new(
        return_type: NEWTypes,
        params: Vec<(NEWTypes, Option<Token>)>,
        variadic: bool,
        kind: InitType,
    ) -> Self {
        Function {
            variadic,
            return_type,
            kind,
            params,
            stack_size: 0,
            epilogue_index: 0,
            labels: HashMap::new(),
        }
    }
    pub fn arity(&self) -> usize {
        self.params.len()
    }
    fn cmp(&self, token: &Token, other: &Function) -> Result<(), Error> {
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
            for (i, (types, param_token)) in self.params.iter().enumerate() {
                if *types != other.params[i].0 {
                    return Err(Error::new(
                        if let Some(param) = param_token {
                            param
                        } else {
                            token
                        },
                        ErrorKind::TypeMismatchFuncDecl(
                            i,
                            other.params[i].0.clone(),
                            types.clone(),
                        ),
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

    // wether the variable is a declaration or initialization
    pub kind: InitType,

    // optional because info isn't known at moment of insertion
    // can be label-register or stack-register
    pub reg: Option<Register>,

    // used in codegen to indicate if declaration needs to be declared as global
    pub is_global: bool,

    // used in codegen to ensure only single declaration of same symbol
    pub token: Token,
}

impl SymbolInfo {
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
    pub fn unwrap_func_mut(&mut self) -> &mut Function {
        match self {
            Symbols::Func(f) => f,
            _ => unreachable!(),
        }
    }
    pub fn unwrap_func(&self) -> &Function {
        match self {
            Symbols::Func(f) => f,
            _ => unreachable!(),
        }
    }
    fn get_kind(&self) -> &InitType {
        match self {
            Symbols::Variable(v) => &v.kind,
            Symbols::Func(f) => &f.kind,
            Symbols::TypeDef(_) => &InitType::Declaration,
        }
    }
    fn cmp(&self, name: &Token, other: &Symbols) -> Result<(), Error> {
        match (self, other) {
            (
                Symbols::Variable(SymbolInfo { type_decl: t1, .. }),
                Symbols::Variable(SymbolInfo { type_decl: t2, .. }),
            )
            | (Symbols::TypeDef(t1), Symbols::TypeDef(t2)) => {
                if t1 != t2 {
                    Err(Error::new(
                        name,
                        ErrorKind::RedefTypeMismatch(name.unwrap_string(), t1.clone(), t2.clone()),
                    ))
                } else {
                    Ok(())
                }
            }
            (Symbols::Func(f1), Symbols::Func(f2)) => f1.cmp(name, f2),
            _ => Err(Error::new(
                name,
                ErrorKind::RedefOtherSymbol(name.unwrap_string(), other.to_string()),
            )),
        }
    }
}

impl PartialEq for Symbols {
    fn eq(&self, other: &Symbols) -> bool {
        let placeholder = Token::default(TokenType::Semicolon);
        self.cmp(&placeholder, other).is_ok()
    }
}
impl std::fmt::Display for Symbols {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Symbols::Variable(_) => "variable",
                Symbols::Func(_) => "function",
                Symbols::TypeDef(_) => "typedef",
            }
        )
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

type Scope<T> = HashMap<String, Rc<RefCell<T>>>;

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
    pub fn get_current(&self, expected: &String) -> Option<Rc<RefCell<T>>> {
        self.elems
            .last()
            .unwrap()
            .get(expected)
            .map(|elem| Rc::clone(&elem))
    }
    pub fn declare(&mut self, name: String, elem: T) -> Rc<RefCell<T>> {
        let kind = Rc::new(RefCell::new(elem));
        self.elems
            .last_mut()
            .unwrap()
            .insert(name, Rc::clone(&kind));
        Rc::clone(&kind)
    }
    pub fn get(&self, name: String) -> Option<Rc<RefCell<T>>> {
        for scope in self.elems.iter().rev() {
            if let Some(elem) = scope.get(&name) {
                return Some(Rc::clone(&elem));
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct Environment {
    pub symbols: NameSpace<Symbols>,
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
    pub fn declare_symbol(
        &mut self,
        var_name: &Token,
        symbol: Symbols,
    ) -> Result<Rc<RefCell<Symbols>>, Error> {
        if let Some(existing_symbol) = self.symbols.get_current(&var_name.unwrap_string()) {
            return self.check_redef(var_name, symbol, existing_symbol);
        }

        Ok(self.symbols.declare(var_name.unwrap_string(), symbol))
    }
    // only used for functions since they have to be inserted before params but need params to be
    // already parsed
    pub fn declare_global(
        &mut self,
        var_name: &Token,
        symbol: Symbols,
    ) -> Result<Rc<RefCell<Symbols>>, Error> {
        let global_scope = self
            .symbols
            .elems
            .get_mut(0)
            .expect("always have a global scope");

        if let Some(existing_symbol) = global_scope
            .get(&var_name.unwrap_string())
            .map(|elem| Rc::clone(&elem))
        {
            return self.check_redef(var_name, symbol, existing_symbol);
        }

        let func = Rc::new(RefCell::new(symbol));
        global_scope.insert(var_name.unwrap_string(), Rc::clone(&func));

        Ok(Rc::clone(&func))
    }

    fn check_redef(
        &self,
        var_name: &Token,
        symbol: Symbols,
        existing_symbol: Rc<RefCell<Symbols>>,
    ) -> Result<Rc<RefCell<Symbols>>, Error> {
        symbol.cmp(var_name, &existing_symbol.borrow())?;

        if matches!(symbol, Symbols::Variable(_)) && !self.is_global() {
            return Err(Error::new(
                var_name,
                ErrorKind::Redefinition("symbol", var_name.unwrap_string()),
            ));
        }

        let existing_kind = existing_symbol.borrow().get_kind().clone();

        match (symbol.get_kind(), existing_kind) {
            (InitType::Declaration, InitType::Declaration)
            | (InitType::Declaration, InitType::Definition) => Ok(existing_symbol),

            (InitType::Definition, InitType::Declaration) => {
                *existing_symbol.borrow_mut() = symbol;
                Ok(existing_symbol)
            }
            (InitType::Definition, InitType::Definition) => Err(Error::new(
                var_name,
                ErrorKind::Redefinition("symbol", var_name.unwrap_string()),
            )),
        }
    }

    pub fn declare_type(
        &mut self,
        var_name: &Token,
        tag: Tags,
    ) -> Result<Rc<RefCell<Tags>>, Error> {
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
    pub fn get_symbol(&self, var_name: &Token) -> Result<Rc<RefCell<Symbols>>, Error> {
        self.symbols.get(var_name.unwrap_string()).ok_or_else(|| {
            Error::new(
                var_name,
                ErrorKind::UndeclaredSymbol(var_name.unwrap_string()),
            )
        })
    }
    pub fn get_type(&self, var_name: &Token) -> Result<Rc<RefCell<Tags>>, Error> {
        self.tags.get(var_name.unwrap_string()).ok_or_else(|| {
            Error::new(
                var_name,
                ErrorKind::UndeclaredType(var_name.unwrap_string()),
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::compiler::scanner::Scanner;
    use crate::compiler::typechecker::TypeChecker;
    use crate::compiler::wrecc_parser::parser::Parser;
    use crate::preprocess;
    use std::path::Path;

    //     fn assert_namespace(input: &str, expected: Vec<(&str, &str, usize)>) {
    //         let pp_tokens = preprocess(Path::new(""), input.to_string()).unwrap();
    //         let mut scanner = Scanner::new(pp_tokens);
    //         let tokens = scanner.scan_token().unwrap();

    //         let mut parser = Parser::new(tokens);
    //         let mut ext_decls = parser.parse().unwrap();

    //         let mut typechecker = TypeChecker::new();
    //         typechecker.check(&mut ext_decls);

    //         let actual = typechecker.env.symbols.elems;

    //         assert_eq!(actual.len(), expected.len());
    //         for (actual, expected) in actual.into_iter().zip(expected) {
    //             assert_eq!(actual.name, expected.0);
    //             assert_eq!(actual.kind.borrow().to_string(), expected.1);
    //             assert_eq!(actual.depth, expected.2);
    //         }
    //     }

    //     #[test]
    //     fn builds_symbol_table() {
    //         let input = "
    // int main(){
    //     char* s;
    //     {
    //         char* n;
    //     }
    //     char* n;
    // }";

    //         let expected = vec![
    //             ("main", "function", 0),
    //             ("s", "variable", 1),
    //             ("n", "variable", 2),
    //             ("n", "variable", 1),
    //         ];

    //         assert_namespace(input, expected);
    //     }
    //     #[test]
    //     fn func_args() {
    //         let input = "
    // int foo(int a, int b) {
    //     {
    //         {
    //             long some;
    //         }
    //     }
    // 	return 2 + a - b;
    // }

    // int main() {
    // 	return foo(1, 3);
    // }";

    //         let expected = vec![
    //             ("foo", "function", 0),
    //             ("a", "variable", 1),
    //             ("b", "variable", 1),
    //             ("some", "variable", 3),
    //             ("main", "function", 0),
    //         ];

    //         assert_namespace(input, expected);
    //     }

    //     #[test]
    //     fn func_decls() {
    //         let input = "
    // int main() {
    //     {
    //         {
    //             int foo(int a, int b);
    //         }
    //     }
    // 	return foo(1, 3);
    // }";

    //         let expected = vec![
    //             ("main", "function", 0),
    //             ("foo", "function", 3),
    //             ("a", "variable", 4),
    //             ("b", "variable", 4),
    //         ];

    //         assert_namespace(input, expected);
    //     }

    //     #[test]
    //     fn get_current() {
    //         todo!()
    //     }
}
