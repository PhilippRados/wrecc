use crate::compiler::ast::{decl::*, expr::*, stmt::*};
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::wrecc_codegen::register::*;
use crate::compiler::wrecc_parser::double_peek::*;
use crate::into_newtype;

use std::collections::VecDeque;

pub struct Parser {
    tokens: DoublePeek<Token>,

    // public so I can set it up in unit-tests
    pub env: Environment,

    // nest-depth to indicate matching synchronizing token
    nest_level: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: DoublePeek::new(tokens),
            env: Environment::new(),
            nest_level: 0,
        }
    }
    pub fn parse(mut self) -> Result<Vec<ExternalDeclaration>, Vec<Error>> {
        let mut external_declarations: Vec<ExternalDeclaration> = Vec::new();
        let mut errors = vec![];

        while self.tokens.peek().is_ok() {
            match self.external_declaration() {
                Ok(decl) => {
                    if let Some(decl) = Self::merge_declarations(&mut external_declarations, decl) {
                        external_declarations.push(decl);
                    }
                }
                Err(e @ Error { kind: ErrorKind::Multiple(..), .. }) => {
                    errors.append(&mut e.flatten_multiple());
                }
                Err(e) => {
                    errors.push(e);
                    self.sync();
                }
            }
        }

        if errors.is_empty() {
            Ok(external_declarations)
        } else {
            Err(errors)
        }
    }
    fn merge_declarations(
        declarations: &mut Vec<ExternalDeclaration>,
        new_decl: ExternalDeclaration,
    ) -> Option<ExternalDeclaration> {
        if let ExternalDeclaration::Declaration(new_decls) = new_decl {
            let mut old_decls = declarations
                .iter_mut()
                .filter_map(|stmt| {
                    if let ExternalDeclaration::Declaration(decls) = stmt {
                        Some(decls)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            let mut updated_decls = Vec::new();
            'outer: for decl in new_decls.into_iter() {
                for old_decl in old_decls.iter_mut() {
                    match Self::find_duplicate_decl(old_decl, &decl) {
                        DupKind::Init(existing_decl) => {
                            *existing_decl = decl;
                            continue 'outer;
                        }
                        DupKind::Decl => continue 'outer,
                        DupKind::None => (),
                    }
                }
                // otherwise add it to the current declaration list again
                updated_decls.push(decl);
            }
            // if all declarations were merged duplicates then don't emit any new statement
            if updated_decls.is_empty() {
                None
            } else {
                Some(ExternalDeclaration::Declaration(updated_decls))
            }
        } else {
            Some(new_decl)
        }
    }
    pub fn has_elements(&self) -> Option<&Token> {
        self.tokens.peek().ok()
    }

    // skips to next valid declaration/statement
    fn sync(&mut self) {
        let mut scope = self.nest_level;

        while let Some(v) = self.tokens.next() {
            match v.token {
                TokenType::Semicolon if scope == 0 => break,
                TokenType::LeftBrace => scope += 1,
                TokenType::RightBrace => {
                    if scope == 0 || scope == 1 {
                        break;
                    }
                    scope -= 1;
                }
                _ => (),
            }
        }
        self.nest_level = 0;
    }

    // <external-declaration> ::= <function-definition>
    //                          | <declaration>
    pub fn external_declaration(&mut self) -> Result<ExternalDeclaration, Error> {
        let (specifier_type, is_typedef) = self.declaration_specifiers(true)?;

        if self.matches(&[TokenKind::Semicolon]).is_some() {
            return Ok(ExternalDeclaration::Declaration(Vec::new()));
        }

        let declarator = self.declarator(
            specifier_type.clone(),
            is_typedef,
            DeclaratorKind::NoAbstract,
        )?;

        if matches!(declarator.type_decl, NEWTypes::Function { .. })
            && self.matches(&[TokenKind::LeftBrace]).is_some()
        {
            return self.function_definition(declarator);
        }

        self.declaration(specifier_type, declarator)
    }

    // <declaration-specifier> ::= <storage-class-specifier>
    //                           | <type-specifier>
    //                           | <type-qualifier> (not supported)
    // <storage-class-specifier> ::= auto
    //                             | register
    //                             | static
    //                             | extern
    //                             | typedef (only typedef currently supported)
    fn declaration_specifiers(
        &mut self,
        allow_storage_classes: bool,
    ) -> Result<(NEWTypes, bool), Error> {
        let start_token = self.tokens.peek()?.clone();
        let mut specifiers = Vec::new();
        let mut is_typedef = false;

        while let Ok(token) = self.tokens.peek() {
            if self.is_type(token) {
                if matches!(token.token, TokenType::Ident(..)) && !specifiers.is_empty() {
                    break;
                }

                specifiers.push(self.type_specifier()?);
            } else if let Some(token) = self.matches(&[TokenKind::TypeDef]) {
                if !allow_storage_classes {
                    return Err(Error::new(
                        &token,
                        ErrorKind::Regular("Storage classes not allowed in this specifier"),
                    ));
                }
                is_typedef = true;
            } else {
                break;
            };
        }

        // TODO: this should emit a warning
        let type_decl = if specifiers.is_empty() {
            NEWTypes::Primitive(Types::Int)
        } else {
            Self::merge_specifiers(&start_token, specifiers)?
        };

        Ok((type_decl, is_typedef))
    }
    fn merge_specifiers(token: &Token, mut specifiers: Vec<NEWTypes>) -> Result<NEWTypes, Error> {
        specifiers.sort_by(|s1, s2| s2.size().cmp(&s1.size()));

        if let Some(not_primitive) = specifiers
            .iter()
            .find(|spec| !matches!(spec, NEWTypes::Primitive(_)))
        {
            if specifiers.len() > 1 {
                return Err(Error::new(
                    token,
                    ErrorKind::Regular("Can only have single specifier if non-primitive specifier"),
                ));
            }
            return Ok(not_primitive.clone());
        }

        let primitive = match specifiers
            .into_iter()
            .map(|spec| spec.unwrap_primitive())
            .collect::<Vec<_>>()
            .as_slice()
        {
            [Types::Void] => Types::Void,
            [Types::Char] => Types::Char,
            [Types::Int] => Types::Int,
            [Types::Long]
            | [Types::Long, Types::Int]
            | [Types::Long, Types::Long]
            | [Types::Long, Types::Long, Types::Int] => Types::Long,
            _ => {
                return Err(Error::new(
                    token,
                    ErrorKind::Regular("Invalid combination of type-specifiers"),
                ));
            }
        };

        Ok(NEWTypes::Primitive(primitive))
    }

    // <declarator> ::= <pointers> <direct-declarator> {<type-suffix>}*
    fn declarator(
        &mut self,
        type_decl: NEWTypes,
        is_typedef: bool,
        kind: DeclaratorKind,
    ) -> Result<Declarator, Error> {
        let type_decl = self.pointers(type_decl);
        let (declarator, derived_types) = self.direct_declarator(type_decl, is_typedef, kind)?;
        let mut declarator = self.type_suffix(declarator)?;

        if let Some(mut type_decl) = derived_types {
            declarator.type_decl = type_decl.append_type(&mut declarator.type_decl).clone();
        }

        Ok(declarator)
    }

    fn pointers(&mut self, type_decl: NEWTypes) -> NEWTypes {
        let mut type_decl = type_decl;
        while self.matches(&[TokenKind::Star]).is_some() {
            type_decl = type_decl.pointer_to();
        }
        type_decl
    }

    // <direct-declarator> ::= <identifier>
    //                       | ( <declarator> )
    fn direct_declarator(
        &mut self,
        type_decl: NEWTypes,
        is_typedef: bool,
        kind: DeclaratorKind,
    ) -> Result<(Declarator, Option<NEWTypes>), Error> {
        if self.matches(&[TokenKind::LeftParen]).is_some() {
            let declarator = self.declarator(NEWTypes::default(), is_typedef, kind)?;
            self.consume(
                TokenKind::RightParen,
                "Expected closing ')' after declarator",
            )?;
            let derived_types = Some(declarator.type_decl);
            return Ok((
                Declarator {
                    name: declarator.name,
                    type_decl,
                    is_typedef,
                },
                derived_types,
            ));
        }

        let name = match kind {
            DeclaratorKind::NoAbstract => Some(self.consume(
                TokenKind::Ident,
                "Expected identifier following type-specifier",
            )?),
            DeclaratorKind::MaybeAbstract => self.matches(&[TokenKind::Ident]),
            DeclaratorKind::Abstract => None,
        };

        Ok((Declarator { name, type_decl, is_typedef }, None))
    }

    // <type-suffix>         ::= [ {<constant-expression>}? ]
    //                         | ( <parameter-type-list> )
    fn type_suffix(&mut self, declarator: Declarator) -> Result<Declarator, Error> {
        if self.matches(&[TokenKind::LeftParen]).is_some() {
            return self.parameter_type_list(declarator);
        }

        if let Some(token) = self.matches(&[TokenKind::LeftBracket]) {
            return self.parse_arr(token, declarator);
        }

        Ok(declarator)
    }
    fn parameter_type_list(&mut self, declarator: Declarator) -> Result<Declarator, Error> {
        // FIX: this only works if single param list per declarator otherwise more envs entered
        // than exited
        self.env.enter();
        let (params, variadic) = self.parse_params()?;

        let mut declarator = self.type_suffix(declarator)?;
        declarator.type_decl = declarator.type_decl.function_of(params, variadic);

        Ok(declarator)
    }

    fn parse_arr(&mut self, token: Token, declarator: Declarator) -> Result<Declarator, Error> {
        let mut size = self.assignment()?;
        let size = size.get_literal_constant(&token, "Array size specifier")?;

        self.consume(
            TokenKind::RightBracket,
            "Expect closing ']' after array initialization",
        )?;

        if size > 0 {
            let mut declarator = self.type_suffix(declarator)?;
            declarator.type_decl = declarator.type_decl.array_of(size as usize);

            Ok(declarator)
        } else {
            Err(Error::new(&token, ErrorKind::NegativeArraySize))
        }
    }

    // <type-name> ::= {<specifier-qualifier>}+ {<abstract-declarator>}?
    fn type_name(&mut self) -> Result<NEWTypes, Error> {
        let (specifier_type, _) = self.declaration_specifiers(false)?;
        let Declarator { type_decl, .. } =
            self.declarator(specifier_type, false, DeclaratorKind::Abstract)?;
        // TODO: have to check that its a valid type can have illegal function types int()[]

        Ok(type_decl)
    }

    fn function_declaration(
        &mut self,
        mut name: Token,
        type_decl: NEWTypes,
        is_definition: bool,
    ) -> Result<Token, Error> {
        let NEWTypes::Function{ return_type,params,variadic } = type_decl else {
            unreachable!("previously checked that is function type");
        };

        if let NEWTypes::Array { .. } | NEWTypes::Function { .. } = *return_type {
            return Err(Error::new(
                &name,
                ErrorKind::InvalidReturnType(*return_type),
            ));
        }

        let mut func = Function::new(*return_type);

        func.kind = if is_definition {
            InitType::Definition
        } else {
            InitType::Declaration
        };
        func.variadic = variadic;
        func.params = params;

        let symbol = self.env.declare_prev_scope(&name, Symbols::Func(func))?;

        if !is_definition {
            self.env.exit();
        }

        name.token.update_entry(TableEntry::Symbol(symbol));

        Ok(name)
    }
    fn function_definition(
        &mut self,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        self.nest_level += 1;
        let name =
            self.function_declaration(declarator.name.unwrap(), declarator.type_decl, true)?;
        self.nest_level -= 1;

        let func_symbol = name.token.get_symbol_entry();
        let return_type = func_symbol.borrow().unwrap_func().return_type.clone();

        if !return_type.is_complete() && !return_type.is_void() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteReturnType(name.unwrap_string(), return_type.clone()),
            ));
        }

        if let Some(param_type) = func_symbol.borrow().unwrap_func().has_incomplete_params() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteFuncArg(name.unwrap_string(), param_type.clone()),
            ));
        }

        if func_symbol.borrow().unwrap_func().has_abstract_params() {
            return Err(Error::new(&name, ErrorKind::UnnamedFuncParams));
        }

        let body = self.block()?;

        Ok(ExternalDeclaration::Function(name, body))
    }

    fn declaration(
        &mut self,
        specifier_type: NEWTypes,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        let mut decls = Vec::new();
        let decl = self.init_declarator(declarator.clone())?;

        Self::add_decl(&mut decls, decl);

        while self.matches(&[TokenKind::Comma]).is_some() {
            let declarator = self.declarator(
                specifier_type.clone(),
                declarator.is_typedef,
                DeclaratorKind::NoAbstract,
            )?;
            let decl = self.init_declarator(declarator)?;

            Self::add_decl(&mut decls, decl);
        }
        self.consume(TokenKind::Semicolon, "Expect ';' after declaration")?;

        Ok(ExternalDeclaration::Declaration(decls))
    }
    fn add_decl(decls: &mut Vec<DeclarationKind>, new_decl: Option<DeclarationKind>) {
        if let Some(new_decl) = new_decl {
            match Self::find_duplicate_decl(decls, &new_decl) {
                DupKind::Init(existing_decl) => *existing_decl = new_decl,
                DupKind::Decl => (),
                DupKind::None => decls.push(new_decl),
            }
        }
    }
    fn find_duplicate_decl<'a>(
        decls: &'a mut Vec<DeclarationKind>,
        new_decl: &DeclarationKind,
    ) -> DupKind<'a> {
        if let Some(existing_decl) = decls.iter_mut().find(|old_decl| **old_decl == *new_decl) {
            if matches!(new_decl, DeclarationKind::VarDecl(.., Some(_init), _)) {
                return DupKind::Init(existing_decl);
            } else {
                return DupKind::Decl;
            }
        }
        DupKind::None
    }
    fn init_declarator(
        &mut self,
        Declarator { name, type_decl, is_typedef }: Declarator,
    ) -> Result<Option<DeclarationKind>, Error> {
        let is_global = self.env.is_global();
        let mut name = name.expect("init declarator cannot be called with abstract-declarator");

        // TODO: have to check typedef function decl
        if is_typedef {
            self.env
                .declare_symbol(&name, Symbols::TypeDef(type_decl))?;
            return Ok(None);
        }

        if matches!(type_decl, NEWTypes::Function { .. }) {
            let name = self.function_declaration(name, type_decl, false)?;
            return Ok(Some(DeclarationKind::FuncDecl(name)));
        }

        if self.matches(&[TokenKind::Equal]).is_some() {
            if !type_decl.is_complete() {
                return Err(Error::new(&name, ErrorKind::IncompleteType(type_decl)));
            }

            let symbol = self.env.declare_symbol(
                &name,
                Symbols::Variable(SymbolInfo {
                    type_decl: type_decl.clone(),
                    kind: InitType::Definition,
                    reg: None,
                }),
            )?;
            name.token.update_entry(TableEntry::Symbol(symbol));

            let init = self.initializers(&name, None)?;

            Ok(Some(DeclarationKind::VarDecl(
                type_decl,
                name,
                Some(init),
                is_global,
            )))
        } else {
            let symbol = self
                .env
                .declare_symbol(&name, Symbols::Variable(SymbolInfo::new(type_decl.clone())))?;
            name.token.update_entry(TableEntry::Symbol(symbol));

            let tentative_decl = self.env.is_global() && type_decl.is_aggregate();
            if !type_decl.is_complete() && !tentative_decl {
                return Err(Error::new(&name, ErrorKind::IncompleteType(type_decl)));
            }

            Ok(Some(DeclarationKind::VarDecl(
                type_decl, name, None, is_global,
            )))
        }
    }
    fn initializers(
        &mut self,
        token: &Token,
        designator: Option<VecDeque<Designator>>,
    ) -> Result<Init, Error> {
        if self.matches(&[TokenKind::LeftBrace]).is_some() {
            self.nest_level += 1;
            let init_list = self.initializer_list(token, designator)?;
            self.nest_level -= 1;

            Ok(init_list)
        } else {
            let r_value = self.assignment()?;

            Ok(Init {
                token: token.clone(),
                designator,
                kind: InitKind::Scalar(r_value),
                offset: 0,
            })
        }
    }

    fn initializer_list(
        &mut self,
        token: &Token,
        designator: Option<VecDeque<Designator>>,
    ) -> Result<Init, Error> {
        let mut init_list = Vec::new();

        while !self.check(TokenKind::RightBrace) {
            let designator = self.parse_designator()?;
            if designator.is_some() {
                self.consume(TokenKind::Equal, "Expect '=' after array designator")?;
            }

            let token = self.tokens.peek()?.clone();
            let init = self.initializers(&token, designator)?;

            init_list.push(Box::new(init));

            if !self.check(TokenKind::RightBrace) {
                self.consume(
                    TokenKind::Comma,
                    "Expect ',' seperating expressions in initializer-list",
                )?;
            }
        }
        self.consume(
            TokenKind::RightBrace,
            "Expected closing '}' after initializer-list",
        )?;

        Ok(Init {
            token: token.clone(),
            designator,
            kind: InitKind::Aggr(init_list),
            offset: 0,
        })
    }

    fn parse_designator(&mut self) -> Result<Option<VecDeque<Designator>>, Error> {
        let mut result = VecDeque::new();

        while let Some(t) = self.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
            if let TokenType::Dot = t.token {
                if let Some(ident) = self.matches(&[TokenKind::Ident]) {
                    result.push_back(Designator {
                        token: ident.clone(),
                        kind: DesignatorKind::Member(ident.unwrap_string()),
                    });
                } else {
                    return Err(Error::new(
                        &t,
                        ErrorKind::Regular("Expect identifier as member designator"),
                    ));
                }
            } else {
                let mut designator_expr = self.assignment()?;
                let literal = designator_expr.get_literal_constant(&t, "Array designator")?;

                if literal < 0 {
                    return Err(Error::new(
                        &t,
                        ErrorKind::Regular("Array designator must be positive number"),
                    ));
                }
                self.consume(
                    TokenKind::RightBracket,
                    "Expect closing ']' after array designator",
                )?;

                result.push_back(Designator {
                    token: t,
                    kind: DesignatorKind::Array(literal),
                })
            }
        }
        if result.is_empty() {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }
    // <parameter-type-list> ::= <parameter-list>
    //                         | <parameter-list> , ...

    // <parameter-list> ::= <parameter-declaration>
    //                    | <parameter-list> , <parameter-declaration>
    fn parse_params(&mut self) -> Result<(Vec<(NEWTypes, Option<Token>)>, bool), Error> {
        let mut params = Vec::new();
        let mut variadic = false;

        if self.matches(&[TokenKind::RightParen]).is_some() {
            return Ok((params, variadic));
        }
        loop {
            match (self.matches(&[TokenKind::Ellipsis]), params.len()) {
                (Some(t), 0) => return Err(Error::new(&t, ErrorKind::InvalidVariadic)),
                (Some(_), _) => {
                    variadic = true;
                    break;
                }
                _ => (),
            }

            // TODO: have to check that func-type doesnt return arr or func
            let mut param_decl = self.parameter_declaration()?;

            param_decl.type_decl = match param_decl.type_decl {
                NEWTypes::Array { of, .. } => of.pointer_to(),
                NEWTypes::Function { .. } => param_decl.type_decl.pointer_to(),
                ty => ty,
            };

            if let Some(name) = &mut param_decl.name {
                // insert parameters into symbol table
                let symbol = self.env.declare_symbol(
                    name,
                    Symbols::Variable(SymbolInfo::new(param_decl.type_decl.clone())),
                )?;
                name.token.update_entry(TableEntry::Symbol(symbol));
            }

            params.push((param_decl.type_decl, param_decl.name));

            if self.matches(&[TokenKind::Comma]).is_none() {
                break;
            }
        }
        let paren = self.consume(
            TokenKind::RightParen,
            "Expect ')' after function parameters",
        )?;

        // single unnamed void param is equivalent to empty params
        if let [(NEWTypes::Primitive(Types::Void), None)] = params.as_slice() {
            params.pop();
        } else if params.iter().any(|(type_decl, _)| type_decl.is_void()) {
            return Err(Error::new(&paren, ErrorKind::VoidFuncArg));
        }

        Ok((params, variadic))
    }

    // <parameter-declaration> ::= {<declaration-specifier>}+ <declarator>
    //                           | {<declaration-specifier>}+ <abstract-declarator>
    //                           | {<declaration-specifier>}+
    fn parameter_declaration(&mut self) -> Result<Declarator, Error> {
        let (specifier_type, _) = self.declaration_specifiers(false)?;

        self.declarator(specifier_type, false, DeclaratorKind::MaybeAbstract)
    }

    // <enumerator-list> ::= {enumerator}+
    // <enumerator> ::= <identifier>
    //                | <identifier> = <conditional-expression>
    fn enumerator_list(&mut self, token: &Token) -> Result<Vec<(Token, i32)>, Error> {
        let mut members = Vec::new();
        let mut index: i32 = 0;
        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }
        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let ident = self.consume(TokenKind::Ident, "Expect identifier in enum definition")?;
            if let Some(t) = self.matches(&[TokenKind::Equal]) {
                let mut index_expr = self.ternary_conditional()?;
                index = index_expr.get_literal_constant(&t, "Enum Constant")? as i32;
            }
            members.push((ident.clone(), index));

            // insert enum constant into symbol table
            self.env.declare_symbol(
                &ident,
                Symbols::Variable(SymbolInfo {
                    type_decl: NEWTypes::Primitive(Types::Int),
                    kind: InitType::Definition,
                    reg: Some(Register::Literal(
                        index as i64,
                        NEWTypes::Primitive(Types::Int),
                    )),
                }),
            )?;

            if let Some(inc) = index.checked_add(1) {
                index = inc;
            } else {
                return Err(Error::new(&ident, ErrorKind::EnumOverflow));
            }
            if !self.check(TokenKind::RightBrace) {
                self.consume(
                    TokenKind::Comma,
                    "Expect ',' seperating expressions in enum-specifier",
                )?;
            }
        }
        Ok(members)
    }
    // <struct-declaration> ::= {<specifier-qualifier>}* <struct-declarator-list>
    // <struct-declarator-list> ::= <struct-declarator>
    //                            | <struct-declarator-list> , <struct-declarator>
    // <struct-declarator> ::= <declarator>
    fn struct_declaration(&mut self, token: &Token) -> Result<Vec<(NEWTypes, Token)>, Error> {
        let mut members = Vec::new();

        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }

        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let (specifier_type, _) = self.declaration_specifiers(false)?;
            loop {
                let member =
                    self.declarator(specifier_type.clone(), false, DeclaratorKind::NoAbstract)?;

                if !member.type_decl.is_complete() {
                    return Err(Error::new(
                        &member.name.unwrap(),
                        ErrorKind::IncompleteType(member.type_decl),
                    ));
                }

                members.push((
                    member.type_decl,
                    member.name.expect("abstract declarations are not allowed"),
                ));
                if self.matches(&[TokenKind::Comma]).is_none() {
                    break;
                }
            }

            self.consume(TokenKind::Semicolon, "Expect ';' after member declaration")?;
        }

        check_duplicate(&members)?;

        Ok(members)
    }
    // <struct-or-union-specifier> ::= <struct-or-union> <identifier> { {<parse-members>}+ }
    //                               | <struct-or-union> { {<parse-members>}+ }
    //                               | <struct-or-union> <identifier>
    // <enum-specifier> ::= enum <identifier> { <enumerator-list> }
    //                    | enum { <enumerator-list> }
    //                    | enum <identifier>
    fn parse_aggregate(&mut self, token: &Token) -> Result<NEWTypes, Error> {
        let name = self.matches(&[TokenKind::Ident]);
        let has_members = self.matches(&[TokenKind::LeftBrace]);

        match (&name, has_members) {
            (Some(name), Some(_)) => {
                Ok(match token.token {
                    TokenType::Struct | TokenType::Union => {
                        self.nest_level += 1;
                        let custom_type = self.env.declare_type(
                            name,
                            Tags::Aggregate(StructRef::new(token.clone().token, true)),
                        )?;

                        let members = self.struct_declaration(token)?;
                        self.nest_level -= 1;

                        if let Tags::Aggregate(struct_ref) = &*custom_type.borrow_mut() {
                            struct_ref.update(members);
                        }

                        into_newtype!(token, name.unwrap_string(), custom_type.borrow())
                    }
                    TokenType::Enum => {
                        self.nest_level += 1;
                        let members = self.enumerator_list(token)?;
                        self.nest_level -= 1;

                        // declare the enum tag in the tag namespace
                        self.env.declare_type(name, Tags::Enum(members.clone()))?;

                        NEWTypes::Enum(Some(name.unwrap_string()), members)
                    }
                    _ => unreachable!("only enums,structs and unions are aggregates"),
                })
            }
            (Some(name), None) => {
                // lookup type-definition
                let custom_type = match self.env.get_type(name) {
                    Ok(tag) => {
                        if &token.token != tag.borrow().get_kind() {
                            return Err(Error::new(
                                name,
                                ErrorKind::TypeAlreadyExists(
                                    name.unwrap_string(),
                                    token.token.clone(),
                                ),
                            ));
                        }
                        tag
                    }
                    Err(_) => self.env.declare_type(
                        name,
                        match token.token {
                            TokenType::Union | TokenType::Struct => {
                                Tags::Aggregate(StructRef::new(token.clone().token, false))
                            }
                            TokenType::Enum => {
                                return Err(Error::new(token, ErrorKind::EnumForwardDecl));
                            }
                            _ => unreachable!(),
                        },
                    )?,
                };

                Ok(into_newtype!(
                    token,
                    name.unwrap_string(),
                    custom_type.borrow()
                ))
            }
            (None, Some(_)) => Ok(if token.token == TokenType::Enum {
                self.nest_level += 1;
                let enum_values = self.enumerator_list(token)?;
                self.nest_level -= 1;

                into_newtype!(enum_values)
            } else {
                self.nest_level += 1;
                let members = self.struct_declaration(token)?;
                self.nest_level -= 1;

                into_newtype!(token, members)
            }),
            (None, None) => Err(Error::new(
                token,
                ErrorKind::EmptyAggregate(token.token.clone()),
            )),
        }
    }

    fn statement(&mut self) -> Result<Stmt, Error> {
        if let Some(token) = self.matches(&[
            TokenKind::For,
            TokenKind::Return,
            TokenKind::If,
            TokenKind::While,
            TokenKind::Break,
            TokenKind::Continue,
            TokenKind::LeftBrace,
            TokenKind::Do,
            TokenKind::Switch,
            TokenKind::Case,
            TokenKind::Default,
            TokenKind::Semicolon,
            TokenKind::Goto,
        ]) {
            return match token.token {
                TokenType::For => self.for_statement(),
                TokenType::Return => self.return_statement(token),
                TokenType::If => self.if_statement(token),
                TokenType::While => self.while_statement(),
                TokenType::Do => self.do_statement(token),
                TokenType::Break => self.break_statement(token),
                TokenType::Continue => self.continue_statement(token),
                TokenType::LeftBrace => {
                    self.env.enter();
                    Ok(Stmt::Block(self.block()?))
                }
                TokenType::Switch => self.switch_statement(token),
                TokenType::Case => self.case_statement(token),
                TokenType::Default => self.default_statement(token),
                TokenType::Goto => self.goto_statement(),
                TokenType::Semicolon => Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue))),
                _ => unreachable!(),
            };
        }
        if let TokenType::Ident(..) = self.tokens.peek()?.token {
            if let TokenType::Colon = self.tokens.double_peek()?.token {
                let ident = self.tokens.next().expect("value is peeked");
                self.tokens.next();

                return self.label_statement(ident);
            }
        }
        self.expression_statement()
    }
    fn goto_statement(&mut self) -> Result<Stmt, Error> {
        let ident = self.consume(TokenKind::Ident, "Expect identifier following 'goto'")?;
        self.consume(TokenKind::Semicolon, "Expect ';' after goto-statement")?;

        Ok(Stmt::Goto(ident))
    }
    fn label_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        let body = self.statement()?;

        Ok(Stmt::Label(token, Box::new(body)))
    }
    fn switch_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        self.consume(TokenKind::LeftParen, "Expect '(' after switch keyword")?;
        let cond = self.expression()?;

        self.consume(TokenKind::RightParen, "Expect ')' after switch condition")?;

        let body = self.statement()?;

        Ok(Stmt::Switch(token, cond, Box::new(body)))
    }
    fn case_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        let mut value = self.assignment()?;
        let value = value.get_literal_constant(&token, "Case value")?;

        self.consume(TokenKind::Colon, "Expect ':' following case-statement")?;

        let body = self.statement()?;

        Ok(Stmt::Case(token, value, Box::new(body)))
    }
    fn default_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        self.consume(TokenKind::Colon, "Expect ':' following default-statement")?;

        let body = self.statement()?;

        Ok(Stmt::Default(token, Box::new(body)))
    }
    fn do_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        let body = self.statement()?;

        self.consume(TokenKind::While, "Expect 'while' after do/while loop-body")?;
        self.consume(TokenKind::LeftParen, "Expect '(' after while keyword")?;

        let cond = self.expression()?;

        self.consume(
            TokenKind::RightParen,
            "Expected closing ')' after do/while-condition",
        )?;
        self.consume(TokenKind::Semicolon, "Expect ';' after do/while statement")?;

        Ok(Stmt::Do(keyword, Box::new(body), cond))
    }
    fn break_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        self.consume(TokenKind::Semicolon, "Expect ';' after break statement")?;
        Ok(Stmt::Break(keyword))
    }
    fn continue_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        self.consume(TokenKind::Semicolon, "Expect ';' after continue statement")?;
        Ok(Stmt::Continue(keyword))
    }
    fn return_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        let mut value = None;
        if !self.check(TokenKind::Semicolon) {
            value = Some(self.expression()?);
        }
        self.consume(TokenKind::Semicolon, "Expect ';' after return statement")?;
        Ok(Stmt::Return(keyword, value))
    }
    fn for_statement(&mut self) -> Result<Stmt, Error> {
        let left_paren = self.consume(TokenKind::LeftParen, "Expect '(' after for-statement")?;

        // Wrapper guarantees that even if error occurs exit() is always called
        self.env.enter();
        let for_stmt = self.parse_for(left_paren);
        self.env.exit();

        for_stmt
    }
    fn parse_for(&mut self, left_paren: Token) -> Result<Stmt, Error> {
        let init = match self.is_specifier(self.tokens.peek()?) {
            true => self.external_declaration().and_then(|decl| match decl {
                ExternalDeclaration::Declaration(decl) => {
                    if let Some(decl_kind) = decl
                        .iter()
                        .find(|kind| !matches!(kind, DeclarationKind::VarDecl(..)))
                    {
                        return Err(Error::new(
                            decl_kind.get_token(),
                            ErrorKind::Regular(
                                "Cannot have non-variable declaration in 'for'-loop",
                            ),
                        ));
                    } else {
                        Ok(Some(Box::new(Stmt::Declaration(decl))))
                    }
                }
                ExternalDeclaration::Function(name, _) => {
                    return Err(Error::new(
                        &name,
                        ErrorKind::Regular("Cannot define functions in 'for'-loop"),
                    ));
                }
            }),
            false if !self.check(TokenKind::Semicolon) => {
                Ok(Some(Box::new(self.expression_statement()?)))
            }
            false => {
                self.consume(TokenKind::Semicolon, "Expect ';' in for loop")?;
                Ok(None)
            }
        }?;

        let cond = match self.check(TokenKind::Semicolon) {
            false => Some(self.expression()?),
            true => None,
        };
        self.consume(TokenKind::Semicolon, "Expect ';' after for condition")?;

        let inc = match self.check(TokenKind::RightParen) {
            false => Some(self.expression()?),
            true => None,
        };
        self.consume(TokenKind::RightParen, "Expect ')' after for increment")?;

        let body = Box::new(self.statement()?);

        Ok(Stmt::For(left_paren, init, cond, inc, body))
    }
    fn while_statement(&mut self) -> Result<Stmt, Error> {
        let left_paren = self.consume(TokenKind::LeftParen, "Expect '(' after while-statement")?;
        let cond = self.expression()?;
        self.consume(
            TokenKind::RightParen,
            "Expected closing ')' after while-condition",
        )?;

        let body = self.statement()?;

        Ok(Stmt::While(left_paren, cond, Box::new(body)))
    }
    fn block(&mut self) -> Result<Vec<Stmt>, Error> {
        let mut statements = Vec::new();
        let mut errors = Vec::new();

        while let Ok(token) = self.tokens.peek() {
            if token.token == TokenType::RightBrace {
                break;
            }
            let stmt = match self.is_specifier(token) {
                true => self.external_declaration().and_then(|decl| match decl {
                    ExternalDeclaration::Declaration(decl) => Ok(Stmt::Declaration(decl)),
                    ExternalDeclaration::Function(name, _) => Err(Error::new(
                        &name,
                        ErrorKind::Regular("Cannot define functions in 'block'-statement"),
                    )),
                }),
                false => self.statement(),
            };

            match stmt {
                Ok(s) => statements.push(s),
                Err(e) if matches!(e.kind, ErrorKind::Multiple(_)) => {
                    // if error is multiple then stmt has already been synchronized
                    errors.push(e);
                }
                Err(e) => {
                    errors.push(e);
                    self.sync();
                }
            }
        }

        if let Err(e) = self.consume(TokenKind::RightBrace, "Expected closing '}' after Block") {
            errors.push(e);
        }
        self.env.exit();

        if errors.is_empty() {
            Ok(statements)
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    fn expression_statement(&mut self) -> Result<Stmt, Error> {
        let expr = self.expression()?;
        self.consume(TokenKind::Semicolon, "Expect ';' after expression")?;
        Ok(Stmt::Expr(expr))
    }
    fn if_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        self.consume(TokenKind::LeftParen, "Expect '(' after 'if'")?;
        let condition = self.expression()?;
        self.consume(
            TokenKind::RightParen,
            "Expect closing ')' after if condition",
        )?;

        let then_branch = self.statement()?;
        let mut else_branch = None;
        if self.matches(&[TokenKind::Else]).is_some() {
            else_branch = Some(Box::new(self.statement()?))
        }
        Ok(Stmt::If(
            keyword,
            condition,
            Box::new(then_branch),
            else_branch,
        ))
    }

    pub fn expression(&mut self) -> Result<Expr, Error> {
        self.comma()
    }
    fn comma(&mut self) -> Result<Expr, Error> {
        let mut expr = self.assignment()?;

        while self.matches(&[TokenKind::Comma]).is_some() {
            expr = Expr::new(
                ExprKind::Comma {
                    left: Box::new(expr),
                    right: Box::new(self.assignment()?),
                },
                ValueKind::Rvalue,
            )
        }

        Ok(expr)
    }
    fn assignment(&mut self) -> Result<Expr, Error> {
        let expr = self.ternary_conditional()?;

        if let Some(t) = self.matches(&[TokenKind::Equal]) {
            let value = self.assignment()?;
            return Ok(Expr::new(
                ExprKind::Assign {
                    l_expr: Box::new(expr),
                    token: t,
                    r_expr: Box::new(value),
                },
                ValueKind::Rvalue,
            ));
        } else if let Some(t) = self.matches(&[
            TokenKind::PlusEqual,
            TokenKind::MinusEqual,
            TokenKind::StarEqual,
            TokenKind::SlashEqual,
            TokenKind::ModEqual,
            TokenKind::PipeEqual,
            TokenKind::AmpEqual,
            TokenKind::XorEqual,
            TokenKind::GreaterGreaterEqual,
            TokenKind::LessLessEqual,
        ]) {
            let value = self.assignment()?;

            return Ok(Expr::new(
                ExprKind::CompoundAssign {
                    l_expr: Box::new(expr),
                    token: t,
                    r_expr: Box::new(value),
                },
                ValueKind::Rvalue,
            ));
        }
        Ok(expr)
    }
    fn ternary_conditional(&mut self) -> Result<Expr, Error> {
        let mut expr = self.or()?;

        while let Some(token) = self.matches(&[TokenKind::Question]) {
            let true_expr = self.expression()?;
            self.consume(
                TokenKind::Colon,
                "Expect ':' to seperate ternary expression",
            )?;
            let false_expr = self.expression()?;

            expr = Expr::new(
                ExprKind::Ternary {
                    token,
                    cond: Box::new(expr),
                    true_expr: Box::new(true_expr),
                    false_expr: Box::new(false_expr),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn or(&mut self) -> Result<Expr, Error> {
        let mut expr = self.and()?;

        while let Some(token) = self.matches(&[TokenKind::PipePipe]) {
            let right = self.and()?;
            expr = Expr::new(
                ExprKind::Logical {
                    left: Box::new(expr),
                    token,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn and(&mut self) -> Result<Expr, Error> {
        let mut expr = self.bit_or()?;

        while let Some(token) = self.matches(&[TokenKind::AmpAmp]) {
            let right = self.bit_or()?;
            expr = Expr::new(
                ExprKind::Logical {
                    left: Box::new(expr),
                    token,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn bit_or(&mut self) -> Result<Expr, Error> {
        let mut expr = self.bit_xor()?;

        while let Some(token) = self.matches(&[TokenKind::Pipe]) {
            let right = self.bit_xor()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn bit_xor(&mut self) -> Result<Expr, Error> {
        let mut expr = self.bit_and()?;

        while let Some(token) = self.matches(&[TokenKind::Xor]) {
            let right = self.bit_and()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn bit_and(&mut self) -> Result<Expr, Error> {
        let mut expr = self.equality()?;

        while let Some(token) = self.matches(&[TokenKind::Amp]) {
            let right = self.equality()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn equality(&mut self) -> Result<Expr, Error> {
        let mut expr = self.comparison()?;

        while let Some(token) = self.matches(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = token;
            let right = self.comparison()?;
            expr = Expr::new(
                ExprKind::Comparison {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            )
        }
        Ok(expr)
    }
    fn comparison(&mut self) -> Result<Expr, Error> {
        let mut expr = self.shift()?;

        while let Some(token) = self.matches(&[
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::Less,
            TokenKind::LessEqual,
        ]) {
            let operator = token;
            let right = self.shift()?;
            expr = Expr::new(
                ExprKind::Comparison {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            );
        }
        Ok(expr)
    }
    fn shift(&mut self) -> Result<Expr, Error> {
        let mut expr = self.term()?;

        while let Some(token) = self.matches(&[TokenKind::GreaterGreater, TokenKind::LessLess]) {
            let operator = token;
            let right = self.term()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            );
        }
        Ok(expr)
    }

    fn term(&mut self) -> Result<Expr, Error> {
        let mut expr = self.factor()?;

        while let Some(token) = self.matches(&[TokenKind::Minus, TokenKind::Plus]) {
            let operator = token;
            let right = self.factor()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            );
        }
        Ok(expr)
    }
    fn factor(&mut self) -> Result<Expr, Error> {
        let mut expr = self.unary()?;

        while let Some(token) = self.matches(&[TokenKind::Slash, TokenKind::Star, TokenKind::Mod]) {
            let operator = token;
            let right = self.unary()?;
            expr = Expr::new(
                ExprKind::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                },
                ValueKind::Rvalue,
            );
        }
        Ok(expr)
    }
    fn unary(&mut self) -> Result<Expr, Error> {
        if let kind @ (TokenType::Star
        | TokenType::Amp
        | TokenType::Bang
        | TokenType::Tilde
        | TokenType::Minus
        | TokenType::Plus
        | TokenType::PlusPlus
        | TokenType::MinusMinus
        | TokenType::LeftParen
        | TokenType::Sizeof) = self.tokens.peek()?.token.clone()
        {
            return Ok(match kind {
                // ++a or --a is equivalent to a += 1 or a -= 1
                TokenType::PlusPlus | TokenType::MinusMinus => {
                    let token = self.tokens.next().unwrap();
                    let right = self.unary()?;
                    Expr::new(
                        ExprKind::CompoundAssign {
                            l_expr: Box::new(right),
                            token,
                            r_expr: Box::new(Expr::new_literal(1, Types::Int)),
                        },
                        ValueKind::Rvalue,
                    )
                }
                // typecast
                // have to check whether expression or type inside of parentheses
                TokenType::LeftParen => {
                    if self.is_type(self.tokens.double_peek()?) {
                        let token = self.tokens.next().unwrap();
                        let type_decl = self.type_name()?;

                        self.typecast(token, type_decl)?
                    } else {
                        self.postfix()?
                    }
                }
                TokenType::Sizeof => {
                    // sizeof expr doesnt need parentheses but sizeof type does
                    self.tokens.next().unwrap();
                    if let TokenType::LeftParen = self.tokens.peek()?.token {
                        if self.is_type(self.tokens.double_peek()?) {
                            self.tokens.next().unwrap();
                            let type_decl = self.type_name()?;

                            self.consume(TokenKind::RightParen, "Expect closing ')' after sizeof")?;
                            return Ok(Expr::new(
                                ExprKind::SizeofType { value: type_decl.size() },
                                ValueKind::Rvalue,
                            ));
                        }
                    }

                    let right = self.unary()?;
                    Expr::new(
                        ExprKind::SizeofExpr { expr: Box::new(right), value: None },
                        ValueKind::Rvalue,
                    )
                }
                _ => {
                    let token = self.tokens.next().unwrap();
                    let right = self.unary()?;
                    Expr::new(
                        ExprKind::Unary {
                            right: Box::new(right),
                            token: token.clone(),
                        },
                        match token.token {
                            TokenType::Star => ValueKind::Lvalue,
                            _ => ValueKind::Rvalue,
                        },
                    )
                }
            });
        }
        self.postfix()
    }
    fn typecast(&mut self, token: Token, type_decl: NEWTypes) -> Result<Expr, Error> {
        self.consume(TokenKind::RightParen, "Expect closing ')' after type-cast")?;
        let expr = self.unary()?;

        Ok(Expr::new(
            ExprKind::Cast {
                token,
                new_type: type_decl,
                direction: None,
                expr: Box::new(expr),
            },
            ValueKind::Rvalue,
        ))
    }
    fn postfix(&mut self) -> Result<Expr, Error> {
        let mut expr = self.primary()?;

        while let Some(token) = self.matches(&[
            TokenKind::LeftBracket,
            TokenKind::LeftParen,
            TokenKind::PlusPlus,
            TokenKind::MinusMinus,
            TokenKind::Dot,
            TokenKind::Arrow,
        ]) {
            match token.token {
                TokenType::LeftBracket => {
                    // a[expr]
                    let index = self.expression()?;
                    self.consume(
                        TokenKind::RightBracket,
                        "Expect closing ']' after array-index",
                    )?;
                    expr = index_sugar(token, expr, index);
                }
                TokenType::LeftParen => {
                    // a()
                    expr = self.call(token, expr)?;
                }
                TokenType::Dot | TokenType::Arrow => {
                    self.has_complete_ident(&expr, &token)?;

                    // some.member or some->member
                    if let Some(member) = self.matches(&[TokenKind::Ident]) {
                        expr = match token.token {
                            TokenType::Dot => Expr::new(
                                ExprKind::MemberAccess { token, member, expr: Box::new(expr) },
                                ValueKind::Lvalue,
                            ),
                            TokenType::Arrow => arrow_sugar(expr, member, token),
                            _ => unreachable!(),
                        }
                    } else {
                        return Err(Error::new(
                            &token,
                            ErrorKind::Regular("A member access must be followed by an identifer"),
                        ));
                    }
                }
                _ => {
                    // a++ or a--
                    expr = Expr::new(
                        ExprKind::PostUnary {
                            token,
                            left: Box::new(expr),
                            by_amount: 1,
                        },
                        ValueKind::Rvalue,
                    )
                }
            }
        }
        Ok(expr)
    }
    // get var-name to lookup if type incomplete or not
    // has to happen in parser otherwise type could be defined after member-access
    fn has_complete_ident(&self, expr: &Expr, token: &Token) -> Result<(), Error> {
        let Some(ident) = get_ident(expr) else {return Ok(())};

        if let Ok(existing_symbol) = self.env.get_symbol(ident) {
            if let Symbols::Variable(SymbolInfo { type_decl, .. })
            | Symbols::Func(Function { return_type: type_decl, .. }) = &*existing_symbol.borrow()
            {
                complete_access(token, type_decl)?
            }
        }
        Ok(())
    }
    fn call(&mut self, left_paren: Token, callee: Expr) -> Result<Expr, Error> {
        let mut args = Vec::new();
        if !self.check(TokenKind::RightParen) {
            loop {
                args.push(self.assignment()?);
                if self.matches(&[TokenKind::Comma]).is_none() {
                    break;
                }
            }
        }
        self.consume(TokenKind::RightParen, "Expect ')' after function call")?;
        if let ExprKind::Ident(name) = callee.kind {
            Ok(Expr::new(
                ExprKind::Call { left_paren, name, args },
                ValueKind::Rvalue,
            ))
        } else {
            Err(Error::new(
                &left_paren,
                ErrorKind::Regular("Function-name has to be identifier"),
            ))
        }
    }
    fn primary(&mut self) -> Result<Expr, Error> {
        if let Some(n) = self.matches(&[TokenKind::Number]) {
            let n = n.unwrap_num();
            return Ok(Expr::new_literal(n, integer_type(n)));
        }
        if let Some(c) = self.matches(&[TokenKind::CharLit]) {
            return Ok(Expr::new_literal(c.unwrap_char() as i64, Types::Char));
        }
        if let Some(mut s) = self.matches(&[TokenKind::Ident]) {
            // if identifier isn't known in symbol table then error
            let symbol = self.env.get_symbol(&s)?;

            // give the token the reference of the symbol in symbol-table
            s.token.update_entry(TableEntry::Symbol(symbol.clone()));

            return Ok(match &*symbol.borrow() {
                Symbols::Variable(v) => Expr {
                    kind: ExprKind::Ident(s),
                    value_kind: ValueKind::Lvalue,
                    type_decl: Some(v.get_type()),
                },
                _ => Expr::new(ExprKind::Ident(s), ValueKind::Lvalue),
            });
        }
        if let Some(s) = self.matches(&[TokenKind::String]) {
            return Ok(Expr::new(ExprKind::String(s), ValueKind::Lvalue));
        }

        if self.matches(&[TokenKind::LeftParen]).is_some() {
            let expr = self.expression()?;
            self.consume(TokenKind::RightParen, "missing closing ')'")?;

            return Ok(Expr::new(
                ExprKind::Grouping { expr: Box::new(expr.clone()) },
                expr.value_kind,
            ));
        }

        let t = self.tokens.peek()?;
        Err(Error::new(
            t,
            ErrorKind::ExpectedExpression(t.token.clone()),
        ))
    }
    fn consume(&mut self, token: TokenKind, msg: &'static str) -> Result<Token, Error> {
        match self.tokens.peek() {
            Ok(v) => {
                if TokenKind::from(&v.token) != token {
                    Err(Error::new(v, ErrorKind::Regular(msg)))
                } else {
                    Ok(self.tokens.next().unwrap())
                }
            }
            Err((Some(token), _)) => Err(Error::new(&token, ErrorKind::Eof(msg))),
            Err(_) => Err(Error::eof(msg)),
        }
    }
    fn check(&mut self, expected: TokenKind) -> bool {
        if let Ok(token) = self.tokens.peek() {
            return TokenKind::from(&token.token) == expected;
        }
        false
    }

    fn matches(&mut self, expected: &[TokenKind]) -> Option<Token> {
        match self.tokens.peek() {
            Ok(v) => {
                if !expected.contains(&TokenKind::from(&v.token)) {
                    return None;
                }
            }
            Err(_) => return None,
        }
        self.tokens.next()
    }
    fn type_specifier(&mut self) -> Result<NEWTypes, Error> {
        let token = self.tokens.peek()?;
        match token.token {
            TokenType::Struct | TokenType::Union | TokenType::Enum => {
                let token = self
                    .tokens
                    .next()
                    .expect("can unwrap because successfull peek");
                self.parse_aggregate(&token)
            }
            // typedefed type
            TokenType::Ident(..) => {
                if let Ok(Symbols::TypeDef(t)) = self
                    .env
                    .get_symbol(token)
                    .map(|symbol| symbol.borrow().clone())
                {
                    self.tokens.next();
                    Ok(t)
                } else {
                    Err(Error::new(token, ErrorKind::NotType(token.token.clone())))
                }
            }
            _ if !token.is_type() => {
                Err(Error::new(token, ErrorKind::NotType(token.token.clone())))
            }
            // otherwise parse primitive
            _ => Ok(self
                .tokens
                .next()
                .expect("can only be types because of previous check")
                .into_type()),
        }
    }
    fn is_type(&self, token: &Token) -> bool {
        if let TokenType::Ident(..) = token.token {
            return matches!(
                self.env
                    .get_symbol(token)
                    .map(|symbol| symbol.borrow().clone()),
                Ok(Symbols::TypeDef(_))
            );
        }
        token.is_type()
    }
    fn is_specifier(&self, token: &Token) -> bool {
        self.is_type(token) || matches!(token.token, TokenType::TypeDef)
    }
}
enum DupKind<'a> {
    Init(&'a mut DeclarationKind),
    Decl,
    None,
}

impl From<(Option<Token>, ErrorKind)> for Error {
    fn from((eof_token, kind): (Option<Token>, ErrorKind)) -> Self {
        if let Some(eof_token) = eof_token {
            Error::new(&eof_token, kind)
        } else {
            Error::eof("Expected expression")
        }
    }
}

// get ident from an expression passed to a member access so:
// expr.member or expr->member
fn get_ident(expr: &Expr) -> Option<&Token> {
    match &expr.kind {
        ExprKind::Ident(s) | ExprKind::Call { name: s, .. } => Some(s),
        ExprKind::Grouping { expr }
        | ExprKind::MemberAccess { expr, .. }
        | ExprKind::PostUnary { left: expr, .. }
        | ExprKind::Unary { right: expr, .. }
        | ExprKind::Binary { left: expr, .. } => get_ident(expr),
        _ => None,
    }
}

fn check_duplicate(vec: &[(NEWTypes, Token)]) -> Result<(), Error> {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    for token in vec.iter().map(|(_, name)| name) {
        if !set.insert(token.unwrap_string()) {
            return Err(Error::new(
                token,
                ErrorKind::DuplicateMember(token.unwrap_string()),
            ));
        }
    }
    Ok(())
}

// checks if member-access-ident is eligible
fn complete_access(token: &Token, type_decl: &NEWTypes) -> Result<(), Error> {
    let is_complete = match type_decl {
        NEWTypes::Struct(s) | NEWTypes::Union(s) => s.is_complete(),
        NEWTypes::Pointer(to) | NEWTypes::Array { of: to, .. } => {
            complete_access(token, to).and(Ok(true))?
        }
        _ => true,
    };

    if !is_complete {
        Err(Error::new(
            token,
            ErrorKind::IncompleteMemberAccess(type_decl.clone()),
        ))
    } else {
        Ok(())
    }
}

// some_struct->member
// equivalent to:
// (*some_struct).member
fn arrow_sugar(left: Expr, member: Token, arrow_token: Token) -> Expr {
    Expr::new(
        ExprKind::MemberAccess {
            token: arrow_token,
            member: member.clone(),
            expr: Box::new(Expr::new(
                ExprKind::Grouping {
                    expr: Box::new(Expr::new(
                        ExprKind::Unary {
                            token: Token { token: TokenType::Star, ..member },
                            right: Box::new(left),
                        },
                        ValueKind::Lvalue,
                    )),
                },
                ValueKind::Lvalue,
            )),
        },
        ValueKind::Lvalue,
    )
}

// a[i] <=> *(a + i)
pub fn index_sugar(token: Token, expr: Expr, index: Expr) -> Expr {
    Expr::new(
        ExprKind::Unary {
            token: Token { token: TokenType::Star, ..token.clone() },
            right: Box::new(Expr::new(
                ExprKind::Grouping {
                    expr: Box::new(Expr::new(
                        ExprKind::Binary {
                            left: Box::new(expr),
                            token: Token { token: TokenType::Plus, ..token },
                            right: Box::new(index),
                        },
                        ValueKind::Lvalue,
                    )),
                },
                ValueKind::Lvalue,
            )),
        },
        ValueKind::Lvalue,
    )
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::compiler::scanner::Scanner;
    use crate::preprocess;
    use std::path::Path;
    use std::path::PathBuf;

    macro_rules! token_default {
        ($token_type:expr) => {
            Token::new($token_type, 1, 1, "".to_string(), PathBuf::new())
        };
    }

    pub fn setup(input: &str) -> Parser {
        let pp_tokens = preprocess(Path::new(""), input.to_string()).unwrap();
        let mut scanner = Scanner::new(pp_tokens);
        let tokens = scanner.scan_token().unwrap();

        Parser::new(tokens)
    }
    fn setup_expr(input: &str) -> String {
        setup(input).ternary_conditional().unwrap().to_string()
    }
    fn setup_stmt(input: &str) -> String {
        setup(input)
            .parse()
            .unwrap()
            .iter()
            .map(|stmt| stmt.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn unary_precedence() {
        let actual = setup_expr("-2++.some");
        let expected = "Unary: '-'\n\
            -MemberAccess: 'some'\n\
            --PostUnary: '++'\n\
            ---Literal: 2";

        assert_eq!(actual, expected);
    }

    #[test]
    fn creates_ast_for_expression() {
        let actual = setup_expr("32 + 1 * 2");
        let expected = "Binary: '+'\n\
            -Literal: 32\n\
            -Binary: '*'\n\
            --Literal: 1\n\
            --Literal: 2";

        assert_eq!(actual, expected);
    }
    #[test]
    fn nested_groupings() {
        let actual = setup_expr("(3 / (6 - 7) * 2) + 1");
        let expected = "Binary: '+'\n\
            -Grouping:\n\
            --Binary: '*'\n\
            ---Binary: '/'\n\
            ----Literal: 3\n\
            ----Grouping:\n\
            -----Binary: '-'\n\
            ------Literal: 6\n\
            ------Literal: 7\n\
            ---Literal: 2\n\
            -Literal: 1";

        assert_eq!(actual, expected);
    }

    #[test]
    fn stmt_ast() {
        let actual = setup_stmt(
            r#"
int printf(char *, ...);

struct Some {
  int age;
};

struct Some a[2] = {{.age = 21}, 33};

int main() {
  int i = 0,b;
  if (1) {
    switch (b) {
    case 1 + 2: {
      printf("case");
      break;
    }
    default:
      printf("hello");
    }
  } else {
    for (int i = 5;; i -= 2) {
      goto end;
    }
  }
  return 1 == 2 ? i - 1 : b;
  int a;
end:
  return 1;
}
"#,
        );
        let expected = r#"Decl:
-FuncDecl: 'printf'
Decl:
-VarInit: 'a'
--Aggregate:
---Aggregate:
----Scalar:
-----Literal: 21
---Scalar:
----Literal: 33
Func: 'main'
-Decl:
--VarInit: 'i'
---Scalar:
----Literal: 0
--VarDecl: 'b'
-If:
--Literal: 1
--Block:
---Switch:
----Ident: 'b'
----Block:
-----Case:
------Value: 3
------Block:
-------Expr:
--------FuncCall: 'printf'
---------String: 'case'
-------Break
-----Default:
------Expr:
-------FuncCall: 'printf'
--------String: 'hello'
--Block:
---For:
----Decl:
-----VarInit: 'i'
------Scalar:
-------Literal: 5
----CompoundAssign: '-='
-----Ident: 'i'
-----Literal: 2
----Block:
-----Goto: 'end'
-Return:
--Ternary:
---Comparison: '=='
----Literal: 1
----Literal: 2
---Binary: '-'
----Ident: 'i'
----Literal: 1
---Ident: 'b'
-Decl:
--VarDecl: 'a'
-Label: 'end'
--Return:
---Literal: 1"#;

        assert_eq!(actual, expected);
    }

    #[test]
    fn matches_works_on_enums_with_values() {
        let tokens = vec![
            token_default!(TokenType::Number(2)),
            token_default!(TokenType::Plus),
        ];
        let mut p = Parser::new(tokens);

        let result = p.matches(&[TokenKind::Number, TokenKind::String]);
        let expected = Some(token_default!(TokenType::Number(2)));

        assert_eq!(result, expected);
    }
}
