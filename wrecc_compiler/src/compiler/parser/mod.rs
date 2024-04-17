//! Recursive descent parser building [parse-tree](hir) as described in [C99 grammar](https://cs.wmich.edu/~gupta/teaching/cs4850/sumII06/The%20syntax%20of%20C%20in%20Backus-Naur%20form.htm)
//! and checking syntax errors.<br>
//! Does not stop after first error but synchronizes parser back into valid state to emit multiple
//! errors at once

pub mod double_peek;
pub mod fold;
pub mod hir;

use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::double_peek::*;
use crate::compiler::parser::hir::{decl::*, expr::*, stmt::*};

use std::collections::VecDeque;

// helper macros that allow comparing enums without specifying their fields: TokenKind::Ident(_)
macro_rules! match_next {
    ($parser:expr, $expected:pat) => {{
        let matched = match $parser.tokens.peek("") {
            Ok(token) => matches!(token.kind, $expected),
            Err(_) => false,
        };
        if matched {
            $parser.tokens.next()
        } else {
            None
        }
    }};
}
macro_rules! consume {
    ($parser:expr,$expected:pat,$msg:expr) => {{
        let token = $parser.tokens.peek($msg)?;
        if matches!(token.kind, $expected) {
            Ok($parser.tokens.next().unwrap())
        } else {
            Err(Error::new(token, ErrorKind::Regular($msg)))
        }
    }};
}
macro_rules! check {
    ($parser:expr,$expected:pat) => {
        if let Ok(token) = $parser.tokens.peek("") {
            matches!(token.kind, $expected)
        } else {
            false
        }
    };
}

pub struct Parser {
    tokens: DoublePeek<Token>,

    // only used as indicator if an identifier was declared as a typedef
    typedefs: NameSpace<()>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: DoublePeek::new(tokens),
            typedefs: NameSpace::new(),
        }
    }
    pub fn parse(mut self) -> Result<Vec<ExternalDeclaration>, Vec<Error>> {
        let mut external_declarations: Vec<ExternalDeclaration> = Vec::new();
        let mut errors = Vec::new();

        while self.tokens.peek("").is_ok() {
            match self.external_declaration() {
                Ok(decl) => {
                    external_declarations.push(decl);
                }
                Err(e @ Error { kind: ErrorKind::Multiple(..), .. }) => {
                    errors.append(&mut e.flatten_multiple());
                }
                Err(e) => {
                    errors.push(e);
                    self.sync(TokenKind::Semicolon);
                }
            }
        }

        if errors.is_empty() {
            Ok(external_declarations)
        } else {
            Err(errors)
        }
    }
    pub fn has_elements(&self) -> Option<&Token> {
        self.tokens.peek("").ok()
    }

    fn maybe_sync(
        &mut self,
        result: Result<(), Error>,
        errors: &mut Vec<Error>,
        until: TokenKind,
    ) -> bool {
        if let Err(err) = result {
            // if multiple errors then parser has already been synchronized
            if !matches!(err.kind, ErrorKind::Multiple(_)) {
                self.sync(until);
            }
            errors.push(err);
            return true;
        }
        false
    }
    // skips tokens until the next synchronizing token is reached
    fn sync(&mut self, until: TokenKind) {
        let mut open_braces = 0;

        while let Some(token) = self.tokens.next() {
            match token.kind {
                tok if tok == until && open_braces <= 0 => {
                    break;
                }
                TokenKind::LeftBrace => open_braces += 1,
                TokenKind::RightBrace => {
                    if open_braces <= 1 {
                        break;
                    }
                    open_braces -= 1
                }
                _ => (),
            }
        }
    }

    // <external-declaration> ::= <function-definition>
    //                          | <declaration>
    pub fn external_declaration(&mut self) -> Result<ExternalDeclaration, Error> {
        let (specifiers, storage_classes) = self.declaration_specifiers(true)?;

        if match_next!(self, TokenKind::Semicolon).is_some() {
            return Ok(ExternalDeclaration::Declaration(Declaration {
                specifiers,
                storage_classes,
                declarators: Vec::new(),
            }));
        }

        let declarator = self.declarator(DeclaratorKind::NoAbstract)?;

        if matches!(declarator.modifiers.last(), Some(DeclModifier::Function { .. }))
            && matches!(self.tokens.peek(""), Ok(Token { kind: TokenKind::LeftBrace, .. }))
        {
            return self.function_definition(specifiers, storage_classes, declarator);
        }

        self.declaration(specifiers, storage_classes, declarator)
    }

    // <declaration-specifier> ::= <storage-class-specifier>
    //                           | <type-specifier>
    //                           | <type-qualifier> (not supported)
    // <storage-class-specifier> ::= auto
    //                             | register
    //                             | static
    //                             | extern
    //                             | typedef
    fn declaration_specifiers(
        &mut self,
        allow_storage_classes: bool,
    ) -> Result<(Vec<DeclSpecifier>, Vec<StorageClass>), Error> {
        let mut specifiers = Vec::new();
        let mut storage_classes = Vec::new();

        while let Ok(token) = self.tokens.peek("") {
            if self.is_type(token) {
                if matches!(token.kind, TokenKind::Ident(..)) && !specifiers.is_empty() {
                    break;
                }

                specifiers.push(DeclSpecifier {
                    token: token.clone(),
                    kind: self.type_specifier()?,
                });
            } else if let Some(token) = match_next!(
                self,
                TokenKind::TypeDef
                    | TokenKind::Extern
                    | TokenKind::Static
                    | TokenKind::Auto
                    | TokenKind::Register
            ) {
                if !allow_storage_classes {
                    return Err(Error::new(
                        &token,
                        ErrorKind::Regular("storage classes not allowed in this specifier"),
                    ));
                }

                storage_classes.push(StorageClass { kind: token.kind.clone().into(), token });
            } else {
                break;
            };
        }

        Ok((specifiers, storage_classes))
    }

    // <declarator> ::= <pointers> <direct-declarator> {<type-suffix>}*
    fn declarator(&mut self, kind: DeclaratorKind) -> Result<Declarator, Error> {
        let mut modifiers = Vec::new();

        self.pointers(&mut modifiers);
        let (name, preceding_modifiers) = self.direct_declarator(kind)?;
        self.type_suffix(&mut modifiers)?;

        if let Some(mut preceding_modifiers) = preceding_modifiers {
            modifiers.append(&mut preceding_modifiers);
        }

        Ok(Declarator { name, modifiers })
    }

    fn pointers(&mut self, modifiers: &mut Vec<DeclModifier>) {
        while match_next!(self, TokenKind::Star).is_some() {
            modifiers.push(DeclModifier::Pointer)
        }
    }

    // <direct-declarator> ::= <identifier>
    //                       | ( <declarator> )
    fn direct_declarator(
        &mut self,
        kind: DeclaratorKind,
    ) -> Result<(Option<Token>, Option<Vec<DeclModifier>>), Error> {
        if let Ok(left_paren @ Token { kind: TokenKind::LeftParen, .. }) = self.tokens.peek("") {
            // have to check that abstract function-decl `int (<type>)` is not mistaken as `int (<declarator>)`
            // also have to catch that `int ()` is not `int` with missing declarator but a
            // function `int (void)`.
            match self.tokens.first_token_after(left_paren) {
                Some(Token { kind: TokenKind::RightParen, .. }) => (),
                Some(token) if !self.is_type(token) => {
                    self.tokens.next();
                    let declarator = self.declarator(kind)?;
                    consume!(
                        self,
                        TokenKind::RightParen,
                        "expected closing ')' after declarator"
                    )?;
                    return Ok((declarator.name, Some(declarator.modifiers)));
                }
                _ => (),
            }
        }

        let name = match kind {
            DeclaratorKind::NoAbstract => Some(consume!(
                self,
                TokenKind::Ident(_),
                "expected identifier following type-specifier"
            )?),
            DeclaratorKind::MaybeAbstract => match_next!(self, TokenKind::Ident(_)),
            DeclaratorKind::Abstract => None,
        };

        Ok((name, None))
    }

    // <type-suffix>         ::= [ {<constant-expression>}? ]
    //                         | ( <parameter-type-list> )
    fn type_suffix(&mut self, modifiers: &mut Vec<DeclModifier>) -> Result<(), Error> {
        let mut suffixes = Vec::new();

        while let Some(token) = match_next!(self, TokenKind::LeftParen | TokenKind::LeftBracket) {
            suffixes.push(if let TokenKind::LeftParen = token.kind {
                self.parameter_type_list(token)?
            } else {
                self.parse_arr(token)?
            })
        }
        for s in suffixes.into_iter().rev() {
            modifiers.push(s)
        }

        Ok(())
    }

    fn parse_arr(&mut self, token: Token) -> Result<DeclModifier, Error> {
        let size = if let TokenKind::RightBracket = self.tokens.peek("array-declaration")?.kind {
            None
        } else {
            Some(self.assignment()?)
        };

        consume!(
            self,
            TokenKind::RightBracket,
            "expected closing ']' after array declaration"
        )?;
        Ok(DeclModifier::Array(token, size))
    }

    // <parameter-type-list> ::= <parameter-list>
    //                         | <parameter-list> , ...

    // <parameter-list> ::= <parameter-declaration>
    //                    | <parameter-list> , <parameter-declaration>
    fn parameter_type_list(&mut self, token: Token) -> Result<DeclModifier, Error> {
        let mut params = Vec::new();
        let mut variadic = false;

        if match_next!(self, TokenKind::RightParen).is_some() {
            return Ok(DeclModifier::Function { token, params, variadic });
        }
        loop {
            match (match_next!(self, TokenKind::Ellipsis), params.len()) {
                (Some(t), 0) => return Err(Error::new(&t, ErrorKind::InvalidVariadic)),
                (Some(_), _) => {
                    variadic = true;
                    break;
                }
                _ => (),
            }

            params.push(self.parameter_declaration()?);

            if match_next!(self, TokenKind::Comma).is_none() {
                break;
            }
        }
        consume!(
            self,
            TokenKind::RightParen,
            "expected ')' after function parameters"
        )?;

        Ok(DeclModifier::Function { token, params, variadic })
    }

    // <parameter-declaration> ::= {<declaration-specifier>}+ <declarator>
    //                           | {<declaration-specifier>}+ <abstract-declarator>
    //                           | {<declaration-specifier>}+
    fn parameter_declaration(&mut self) -> Result<ParamDecl, Error> {
        let (specifiers, storage_classes) = self.declaration_specifiers(true)?;
        let declarator = self.declarator(DeclaratorKind::MaybeAbstract)?;

        Ok(ParamDecl { specifiers, storage_classes, declarator })
    }

    // <type-name> ::= {<specifier-qualifier>}+ {<abstract-declarator>}?
    pub fn type_name(&mut self) -> Result<DeclType, Error> {
        let (specifiers, _) = self.declaration_specifiers(false)?;
        let Declarator { modifiers, .. } = self.declarator(DeclaratorKind::Abstract)?;

        Ok(DeclType { specifiers, modifiers })
    }

    fn function_definition(
        &mut self,
        specifiers: Vec<DeclSpecifier>,
        storage_classes: Vec<StorageClass>,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        self.tokens.next().expect("consume peeked left-brace");

        let body = self.block()?;

        Ok(ExternalDeclaration::Function(
            FuncDecl {
                specifiers,
                storage_classes,
                name: declarator.name.expect("external-decls cannot be abstract"),
                modifiers: declarator.modifiers,
            },
            body,
        ))
    }

    fn declaration(
        &mut self,
        specifiers: Vec<DeclSpecifier>,
        storage_classes: Vec<StorageClass>,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        let mut declarators = Vec::new();
        let init = self.init_declarator(&storage_classes, &declarator)?;

        declarators.push((declarator, init));

        while match_next!(self, TokenKind::Comma).is_some() {
            let declarator = self.declarator(DeclaratorKind::NoAbstract)?;
            let init = self.init_declarator(&storage_classes, &declarator)?;

            declarators.push((declarator, init));
        }
        consume!(self, TokenKind::Semicolon, "expected ';' after declaration")?;

        Ok(ExternalDeclaration::Declaration(Declaration {
            specifiers,
            declarators,
            storage_classes,
        }))
    }
    fn init_declarator(
        &mut self,
        storage_classes: &Vec<StorageClass>,
        Declarator { name, .. }: &Declarator,
    ) -> Result<Option<Init>, Error> {
        let name = name.clone().unwrap();

        if storage_classes
            .iter()
            .any(|storage| storage.kind == StorageClassKind::TypeDef)
        {
            self.typedefs.declare(name.unwrap_string(), ());
        }

        let init = if match_next!(self, TokenKind::Equal).is_some() {
            Some(self.initializers(&name, None)?)
        } else {
            None
        };

        Ok(init)
    }
    fn initializers(
        &mut self,
        token: &Token,
        designator: Option<VecDeque<Designator>>,
    ) -> Result<Init, Error> {
        if match_next!(self, TokenKind::LeftBrace).is_some() {
            let init_list = self.initializer_list(token, designator)?;

            Ok(init_list)
        } else {
            let r_value = self.assignment()?;

            Ok(Init {
                token: token.clone(),
                designator,
                kind: InitKind::Scalar(r_value),
            })
        }
    }

    fn initializer_list(
        &mut self,
        token: &Token,
        designator: Option<VecDeque<Designator>>,
    ) -> Result<Init, Error> {
        let mut init_list = Vec::new();
        let mut errors = Vec::new();

        while !check!(self, TokenKind::RightBrace) {
            let result = || -> Result<(), Error> {
                let designator = self.parse_designator()?;
                if designator.is_some() {
                    consume!(self, TokenKind::Equal, "expected '=' after array designator")?;
                }

                let token = self.tokens.peek("expected expression")?.clone();
                let init = self.initializers(&token, designator)?;

                init_list.push(Box::new(init));

                if !check!(self, TokenKind::RightBrace) {
                    consume!(
                        self,
                        TokenKind::Comma,
                        "expected ',' seperating expressions in initializer-list"
                    )?;
                }

                Ok(())
            }();

            if self.maybe_sync(result, &mut errors, TokenKind::RightBrace) {
                break;
            }
        }

        if errors.is_empty() {
            consume!(
                self,
                TokenKind::RightBrace,
                "expected closing '}' after initializer-list"
            )?;

            Ok(Init {
                token: token.clone(),
                designator,
                kind: InitKind::Aggr(init_list),
            })
        } else {
            Err(Error::new_multiple(errors))
        }
    }

    fn parse_designator(&mut self) -> Result<Option<VecDeque<Designator>>, Error> {
        let mut result = VecDeque::new();

        while let Some(token) = match_next!(self, TokenKind::Dot | TokenKind::LeftBracket) {
            if let TokenKind::Dot = token.kind {
                if let Some(ident) = match_next!(self, TokenKind::Ident(_)) {
                    result.push_back(Designator {
                        token: ident.clone(),
                        kind: DesignatorKind::Member(ident.unwrap_string()),
                    });
                } else {
                    return Err(Error::new(
                        &token,
                        ErrorKind::Regular("expected identifier as member designator"),
                    ));
                }
            } else {
                let designator_expr = self.assignment()?;

                consume!(
                    self,
                    TokenKind::RightBracket,
                    "expected closing ']' after array designator"
                )?;

                result.push_back(Designator {
                    token,
                    kind: DesignatorKind::Array(designator_expr),
                })
            }
        }
        if result.is_empty() {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }

    // <enumerator-list> ::= {enumerator}+
    // <enumerator> ::= <identifier>
    //                | <identifier> = <conditional-expression>
    fn enumerator_list(&mut self, token: &Token) -> Result<Vec<(Token, Option<ExprKind>)>, Error> {
        let mut constants = Vec::new();
        let mut errors = Vec::new();

        if check!(self, TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.kind.clone())));
        }

        while let Ok(token) = self.tokens.peek("") {
            if let TokenKind::RightBrace = token.kind {
                break;
            }
            let result = || -> Result<(), Error> {
                let ident = consume!(
                    self,
                    TokenKind::Ident(_),
                    "expected identifier in enum definition"
                )?;
                let init = if match_next!(self, TokenKind::Equal).is_some() {
                    Some(self.ternary_conditional()?)
                } else {
                    None
                };
                constants.push((ident.clone(), init));

                if !check!(self, TokenKind::RightBrace) {
                    consume!(
                        self,
                        TokenKind::Comma,
                        "expected ',' seperating expressions in enum-specifier"
                    )?;
                }
                Ok(())
            }();

            if self.maybe_sync(result, &mut errors, TokenKind::RightBrace) {
                break;
            }
        }

        if let Err(e) = consume!(
            self,
            TokenKind::RightBrace,
            "expected closing '}' after enum definition"
        ) {
            errors.push(e);
        }

        if errors.is_empty() {
            Ok(constants)
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    // <struct-declaration> ::= {<specifier-qualifier>}* <struct-declarator-list>
    // <struct-declarator-list> ::= <struct-declarator>
    //                            | <struct-declarator-list> , <struct-declarator>
    // <struct-declarator> ::= <declarator>
    fn struct_declaration(&mut self, token: &Token) -> Result<Vec<MemberDeclaration>, Error> {
        let mut members = Vec::new();
        let mut errors = Vec::new();

        while let Ok(token) = self.tokens.peek("") {
            if let TokenKind::RightBrace = token.kind {
                break;
            }
            let result = || -> Result<(), Error> {
                let (specifiers, _) = self.declaration_specifiers(false)?;
                let mut declarators = Vec::new();

                loop {
                    // allows `int;` but not `int *;`
                    if let TokenKind::Semicolon = self.tokens.peek("expected member-declarator")?.kind {
                        break;
                    }

                    let Declarator { name, modifiers } = self.declarator(DeclaratorKind::NoAbstract)?;
                    declarators.push(MemberDeclarator {
                        name: name.expect("member cannot be abstract declarator"),
                        modifiers,
                    });

                    if match_next!(self, TokenKind::Comma).is_none() {
                        break;
                    }
                }
                members.push((specifiers, declarators));

                // dont return Error directly because then then can't sync properly
                if let Err(e) = consume!(
                    self,
                    TokenKind::Semicolon,
                    "expected ';' after member declaration"
                ) {
                    errors.push(e);
                }
                Ok(())
            }();

            self.maybe_sync(result, &mut errors, TokenKind::Semicolon);
        }

        if members.iter().all(|(_, decl)| decl.is_empty()) {
            errors.push(Error::new(token, ErrorKind::IsEmpty(token.kind.clone())))
        }

        if let Err(e) = consume!(
            self,
            TokenKind::RightBrace,
            "expected closing '}' after struct declaration"
        ) {
            errors.push(e);
        }

        if errors.is_empty() {
            Ok(members)
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    // <struct-or-union-specifier> ::= <struct-or-union> <identifier> { {<parse-members>}+ }
    //                               | <struct-or-union> { {<parse-members>}+ }
    //                               | <struct-or-union> <identifier>
    fn struct_or_union_specifier(&mut self, token: &Token) -> Result<SpecifierKind, Error> {
        let name = match_next!(self, TokenKind::Ident(_));

        let members = if match_next!(self, TokenKind::LeftBrace).is_some() {
            Some(self.struct_declaration(token)?)
        } else {
            None
        };

        Ok(match token.kind {
            TokenKind::Struct => SpecifierKind::Struct(name, members),
            TokenKind::Union => SpecifierKind::Union(name, members),
            _ => unreachable!("not struct/union specifier"),
        })
    }

    // <enum-specifier> ::= enum <identifier> { <enumerator-list> }
    //                    | enum { <enumerator-list> }
    //                    | enum <identifier>
    fn enum_specifier(&mut self, token: &Token) -> Result<SpecifierKind, Error> {
        let name = match_next!(self, TokenKind::Ident(_));

        let members = if match_next!(self, TokenKind::LeftBrace).is_some() {
            Some(self.enumerator_list(token)?)
        } else {
            None
        };

        Ok(SpecifierKind::Enum(name, members))
    }

    fn statement(&mut self) -> Result<Stmt, Error> {
        if let Some(token) = match_next!(
            self,
            TokenKind::For
                | TokenKind::Return
                | TokenKind::If
                | TokenKind::While
                | TokenKind::Break
                | TokenKind::Continue
                | TokenKind::LeftBrace
                | TokenKind::Do
                | TokenKind::Switch
                | TokenKind::Case
                | TokenKind::Default
                | TokenKind::Semicolon
                | TokenKind::Goto
        ) {
            return match token.kind {
                TokenKind::For => self.for_statement(),
                TokenKind::Return => self.return_statement(token),
                TokenKind::If => self.if_statement(token),
                TokenKind::While => self.while_statement(),
                TokenKind::Do => self.do_statement(token),
                TokenKind::Break => self.break_statement(token),
                TokenKind::Continue => self.continue_statement(token),
                TokenKind::LeftBrace => Ok(Stmt::Block(self.block()?)),
                TokenKind::Switch => self.switch_statement(token),
                TokenKind::Case => self.case_statement(token),
                TokenKind::Default => self.default_statement(token),
                TokenKind::Goto => self.goto_statement(),
                TokenKind::Semicolon => Ok(Stmt::Expr(ExprKind::Nop)),
                _ => unreachable!(),
            };
        }
        if let TokenKind::Ident(..) = self.tokens.peek("expected expression")?.kind {
            if let TokenKind::Colon = self.tokens.double_peek("expected expression")?.kind {
                let ident = self.tokens.next().expect("value is peeked");
                self.tokens.next();

                return self.label_statement(ident);
            }
        }
        self.expression_statement()
    }
    fn goto_statement(&mut self) -> Result<Stmt, Error> {
        let ident = consume!(self, TokenKind::Ident(_), "expected identifier following 'goto'")?;
        consume!(self, TokenKind::Semicolon, "expected ';' after goto-statement")?;

        Ok(Stmt::Goto(ident))
    }
    fn label_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        let body = self.statement()?;

        Ok(Stmt::Label(token, Box::new(body)))
    }
    fn switch_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        consume!(self, TokenKind::LeftParen, "expected '(' after switch-keyword")?;
        let cond = self.expression()?;

        consume!(self, TokenKind::RightParen, "expected ')' after switch-condition")?;

        let body = self.statement()?;

        Ok(Stmt::Switch(token, cond, Box::new(body)))
    }
    fn case_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        let value = self.assignment()?;

        consume!(self, TokenKind::Colon, "expected ':' following case-statement")?;

        let body = self.statement()?;

        Ok(Stmt::Case(token, value, Box::new(body)))
    }
    fn default_statement(&mut self, token: Token) -> Result<Stmt, Error> {
        consume!(self, TokenKind::Colon, "expected ':' following default-statement")?;

        let body = self.statement()?;

        Ok(Stmt::Default(token, Box::new(body)))
    }
    fn do_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        let body = self.statement()?;

        consume!(
            self,
            TokenKind::While,
            "expected 'while' after do/while loop-body"
        )?;
        consume!(self, TokenKind::LeftParen, "expected '(' after while keyword")?;

        let cond = self.expression()?;

        consume!(
            self,
            TokenKind::RightParen,
            "expected closing ')' after do/while-condition"
        )?;
        consume!(
            self,
            TokenKind::Semicolon,
            "expected ';' after do/while-statement"
        )?;

        Ok(Stmt::Do(keyword, Box::new(body), cond))
    }
    fn break_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        consume!(self, TokenKind::Semicolon, "expected ';' after break-statement")?;
        Ok(Stmt::Break(keyword))
    }
    fn continue_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        consume!(
            self,
            TokenKind::Semicolon,
            "expected ';' after continue-statement"
        )?;
        Ok(Stmt::Continue(keyword))
    }
    fn return_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        let value = match check!(self, TokenKind::Semicolon) {
            false => Some(self.expression()?),
            true => None,
        };

        consume!(self, TokenKind::Semicolon, "expected ';' after return statement")?;
        Ok(Stmt::Return(keyword, value))
    }
    fn for_statement(&mut self) -> Result<Stmt, Error> {
        let left_paren = consume!(self, TokenKind::LeftParen, "expected '(' after for-statement")?;

        self.typedefs.enter();

        let init = match self.is_specifier(self.tokens.peek("expected type-specifier")?) {
            true => self.external_declaration().and_then(|decl| match decl {
                ExternalDeclaration::Declaration(decl) => Ok(Some(Box::new(Stmt::Declaration(decl)))),
                ExternalDeclaration::Function(FuncDecl { name, .. }, _) => Err(Error::new(
                    &name,
                    ErrorKind::Regular("cannot define functions in for-statement"),
                )),
            }),
            false if !check!(self, TokenKind::Semicolon) => {
                Ok(Some(Box::new(self.expression_statement()?)))
            }
            false => {
                consume!(self, TokenKind::Semicolon, "expected ';' in for-statement")?;
                Ok(None)
            }
        }?;

        let cond = match check!(self, TokenKind::Semicolon) {
            false => Some(self.expression()?),
            true => None,
        };
        consume!(self, TokenKind::Semicolon, "expected ';' after for-condition")?;

        let inc = match check!(self, TokenKind::RightParen) {
            false => Some(self.expression()?),
            true => None,
        };
        consume!(self, TokenKind::RightParen, "expected ')' after for-increment")?;

        let body = Box::new(self.statement()?);

        self.typedefs.exit();

        Ok(Stmt::For(left_paren, init, cond, inc, body))
    }
    fn while_statement(&mut self) -> Result<Stmt, Error> {
        let left_paren = consume!(self, TokenKind::LeftParen, "expected '(' after while-statement")?;
        let cond = self.expression()?;
        consume!(
            self,
            TokenKind::RightParen,
            "expected closing ')' after while-condition"
        )?;

        let body = self.statement()?;

        Ok(Stmt::While(left_paren, cond, Box::new(body)))
    }
    fn block(&mut self) -> Result<Vec<Stmt>, Error> {
        let mut statements = Vec::new();
        let mut errors = Vec::new();

        self.typedefs.enter();

        while let Ok(token) = self.tokens.peek("").map(|tok| tok.clone()) {
            if token.kind == TokenKind::RightBrace {
                break;
            }
            let result = || -> Result<(), Error> {
                let stmt = match self.is_specifier(&token) {
                    // have to catch label-statement that might be mistaken for type
                    true if !matches!(
                        self.tokens.double_peek(""),
                        Ok(Token { kind: TokenKind::Colon, .. })
                    ) =>
                    {
                        self.external_declaration().and_then(|decl| match decl {
                            ExternalDeclaration::Declaration(decl) => Ok(Stmt::Declaration(decl)),
                            ExternalDeclaration::Function(FuncDecl { name, .. }, _) => Err(Error::new(
                                &name,
                                ErrorKind::Regular("cannot define functions in 'block'-statement"),
                            )),
                        })
                    }
                    _ => self.statement(),
                }?;

                statements.push(stmt);
                Ok(())
            }();

            self.maybe_sync(result, &mut errors, TokenKind::Semicolon);
        }

        if let Err(e) = consume!(self, TokenKind::RightBrace, "expected closing '}' after block") {
            errors.push(e);
        }

        self.typedefs.exit();

        if errors.is_empty() {
            Ok(statements)
        } else {
            Err(Error::new_multiple(errors))
        }
    }
    fn expression_statement(&mut self) -> Result<Stmt, Error> {
        let expr = self.expression()?;
        consume!(self, TokenKind::Semicolon, "expected ';' after expression")?;
        Ok(Stmt::Expr(expr))
    }
    fn if_statement(&mut self, keyword: Token) -> Result<Stmt, Error> {
        consume!(self, TokenKind::LeftParen, "expected '(' after 'if'")?;
        let condition = self.expression()?;
        consume!(
            self,
            TokenKind::RightParen,
            "expected closing ')' after if condition"
        )?;

        let then_branch = self.statement()?;
        let else_branch = if match_next!(self, TokenKind::Else).is_some() {
            Some(Box::new(self.statement()?))
        } else {
            None
        };
        Ok(Stmt::If(keyword, condition, Box::new(then_branch), else_branch))
    }

    pub fn expression(&mut self) -> Result<ExprKind, Error> {
        self.comma()
    }
    fn comma(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.assignment()?;

        while match_next!(self, TokenKind::Comma).is_some() {
            expr = ExprKind::Comma {
                left: Box::new(expr),
                right: Box::new(self.assignment()?),
            }
        }

        Ok(expr)
    }
    fn assignment(&mut self) -> Result<ExprKind, Error> {
        let expr = self.ternary_conditional()?;

        if let Some(t) = match_next!(self, TokenKind::Equal) {
            let value = self.assignment()?;
            return Ok(ExprKind::Assign {
                l_expr: Box::new(expr),
                token: t,
                r_expr: Box::new(value),
            });
        } else if let Some(t) = match_next!(
            self,
            TokenKind::PlusEqual
                | TokenKind::MinusEqual
                | TokenKind::StarEqual
                | TokenKind::SlashEqual
                | TokenKind::ModEqual
                | TokenKind::PipeEqual
                | TokenKind::AmpEqual
                | TokenKind::XorEqual
                | TokenKind::GreaterGreaterEqual
                | TokenKind::LessLessEqual
        ) {
            let value = self.assignment()?;

            return Ok(ExprKind::CompoundAssign {
                l_expr: Box::new(expr),
                token: t,
                r_expr: Box::new(value),
            });
        }
        Ok(expr)
    }
    fn ternary_conditional(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.or()?;

        while let Some(token) = match_next!(self, TokenKind::Question) {
            let true_expr = self.expression()?;
            consume!(
                self,
                TokenKind::Colon,
                "expected ':' to seperate ternary expression"
            )?;
            let false_expr = self.expression()?;

            expr = ExprKind::Ternary {
                token,
                cond: Box::new(expr),
                true_expr: Box::new(true_expr),
                false_expr: Box::new(false_expr),
            }
        }
        Ok(expr)
    }
    fn or(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.and()?;

        while let Some(token) = match_next!(self, TokenKind::PipePipe) {
            let right = self.and()?;
            expr = ExprKind::Logical {
                left: Box::new(expr),
                token,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn and(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.bit_or()?;

        while let Some(token) = match_next!(self, TokenKind::AmpAmp) {
            let right = self.bit_or()?;
            expr = ExprKind::Logical {
                left: Box::new(expr),
                token,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn bit_or(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.bit_xor()?;

        while let Some(token) = match_next!(self, TokenKind::Pipe) {
            let right = self.bit_xor()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn bit_xor(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.bit_and()?;

        while let Some(token) = match_next!(self, TokenKind::Xor) {
            let right = self.bit_and()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn bit_and(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.equality()?;

        while let Some(token) = match_next!(self, TokenKind::Amp) {
            let right = self.equality()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn equality(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.comparison()?;

        while let Some(token) = match_next!(self, TokenKind::BangEqual | TokenKind::EqualEqual) {
            let operator = token;
            let right = self.comparison()?;
            expr = ExprKind::Comparison {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn comparison(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.shift()?;

        while let Some(token) = match_next!(
            self,
            TokenKind::Greater | TokenKind::GreaterEqual | TokenKind::Less | TokenKind::LessEqual
        ) {
            let operator = token;
            let right = self.shift()?;
            expr = ExprKind::Comparison {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn shift(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.term()?;

        while let Some(token) = match_next!(self, TokenKind::GreaterGreater | TokenKind::LessLess) {
            let operator = token;
            let right = self.term()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }

    fn term(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.factor()?;

        while let Some(token) = match_next!(self, TokenKind::Minus | TokenKind::Plus) {
            let operator = token;
            let right = self.factor()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn factor(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.unary()?;

        while let Some(token) = match_next!(self, TokenKind::Slash | TokenKind::Star | TokenKind::Mod) {
            let operator = token;
            let right = self.unary()?;
            expr = ExprKind::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
        }
        Ok(expr)
    }
    fn unary(&mut self) -> Result<ExprKind, Error> {
        if let kind @ (TokenKind::Star
        | TokenKind::Amp
        | TokenKind::Bang
        | TokenKind::Tilde
        | TokenKind::Minus
        | TokenKind::Plus
        | TokenKind::PlusPlus
        | TokenKind::MinusMinus
        | TokenKind::LeftParen
        | TokenKind::Sizeof) = self.tokens.peek("expected expression")?.kind.clone()
        {
            return Ok(match kind {
                // ++a or --a is equivalent to a += 1 or a -= 1
                TokenKind::PlusPlus | TokenKind::MinusMinus => {
                    let token = self.tokens.next().unwrap();
                    let right = self.unary()?;

                    ExprKind::CompoundAssign {
                        l_expr: Box::new(right),
                        token,
                        r_expr: Box::new(ExprKind::Literal(1, Type::Primitive(Primitive::Int))),
                    }
                }
                // typecast
                // have to check whether expression or type inside of parentheses
                TokenKind::LeftParen => {
                    if self.is_type(self.tokens.double_peek("expected expression")?) {
                        let token = self.tokens.next().unwrap();
                        let decl_type = self.type_name()?;

                        self.typecast(token, decl_type)?
                    } else {
                        self.postfix()?
                    }
                }
                TokenKind::Sizeof => {
                    // sizeof expr doesnt need parentheses but sizeof type does
                    let token = self.tokens.next().unwrap();
                    if let TokenKind::LeftParen = self.tokens.peek("expected expression")?.kind {
                        if self
                            .is_type(self.tokens.double_peek("expected expression or type-specifier")?)
                        {
                            let token = self.tokens.next().unwrap();
                            let decl_type = self.type_name()?;

                            consume!(self, TokenKind::RightParen, "expected closing ')' after sizeof")?;
                            return Ok(ExprKind::SizeofType { token, decl_type });
                        }
                    }

                    let right = self.unary()?;
                    ExprKind::SizeofExpr { token, expr: Box::new(right) }
                }
                _ => {
                    let token = self.tokens.next().unwrap();
                    let right = self.unary()?;

                    ExprKind::Unary {
                        right: Box::new(right),
                        token: token.clone(),
                    }
                }
            });
        }
        self.postfix()
    }
    fn typecast(&mut self, token: Token, decl_type: DeclType) -> Result<ExprKind, Error> {
        consume!(
            self,
            TokenKind::RightParen,
            "expected closing ')' after type-cast"
        )?;
        let expr = self.unary()?;

        Ok(ExprKind::Cast { token, decl_type, expr: Box::new(expr) })
    }
    fn postfix(&mut self) -> Result<ExprKind, Error> {
        let mut expr = self.primary()?;

        while let Some(token) = match_next!(
            self,
            TokenKind::LeftBracket
                | TokenKind::LeftParen
                | TokenKind::PlusPlus
                | TokenKind::MinusMinus
                | TokenKind::Dot
                | TokenKind::Arrow
        ) {
            match token.kind {
                // a[expr]
                TokenKind::LeftBracket => {
                    let index = self.expression()?;
                    consume!(
                        self,
                        TokenKind::RightBracket,
                        "expected closing ']' after array-index"
                    )?;
                    expr = index_sugar(token, expr, index);
                }
                // a()
                TokenKind::LeftParen => {
                    expr = self.call(token, expr)?;
                }
                // some.member or some->member
                TokenKind::Dot | TokenKind::Arrow => {
                    if let Some(member) = match_next!(self, TokenKind::Ident(_)) {
                        expr = match token.kind {
                            TokenKind::Dot => {
                                ExprKind::MemberAccess { token, member, expr: Box::new(expr) }
                            }
                            TokenKind::Arrow => arrow_sugar(expr, member, token),
                            _ => unreachable!(),
                        }
                    } else {
                        return Err(Error::new(
                            &token,
                            ErrorKind::Regular("member access must be followed by an identifer"),
                        ));
                    }
                }
                _ => {
                    // a++ or a--
                    expr = ExprKind::PostUnary { token, left: Box::new(expr) }
                }
            }
        }
        Ok(expr)
    }
    fn call(&mut self, left_paren: Token, caller: ExprKind) -> Result<ExprKind, Error> {
        let mut args = Vec::new();
        if !check!(self, TokenKind::RightParen) {
            loop {
                args.push(self.assignment()?);
                if match_next!(self, TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        consume!(self, TokenKind::RightParen, "expected ')' after function call")?;
        Ok(ExprKind::Call {
            left_paren,
            caller: Box::new(caller),
            args,
        })
    }
    fn primary(&mut self) -> Result<ExprKind, Error> {
        if let Some(n) = match_next!(self, TokenKind::Number(_)) {
            let n = n.unwrap_num();
            return Ok(ExprKind::Literal(n, Type::Primitive(integer_type(n))));
        }
        if let Some(c) = match_next!(self, TokenKind::CharLit(_)) {
            return Ok(ExprKind::Literal(
                c.unwrap_char() as i64,
                Type::Primitive(Primitive::Char),
            ));
        }
        if let Some(s) = match_next!(self, TokenKind::Ident(_)) {
            return Ok(ExprKind::Ident(s));
        }
        if let Some(s) = match_next!(self, TokenKind::String(_)) {
            return Ok(ExprKind::String(s));
        }

        if match_next!(self, TokenKind::LeftParen).is_some() {
            let expr = self.expression()?;
            consume!(self, TokenKind::RightParen, "expected closing ')'")?;

            return Ok(expr);
        }

        let token = self.tokens.peek("expected expression")?;
        Err(Error::new(
            token,
            ErrorKind::ExpectedExpression(token.kind.clone()),
        ))
    }
    fn type_specifier(&mut self) -> Result<SpecifierKind, Error> {
        let token = self.tokens.peek("expected type-specifier")?;
        match token.kind {
            TokenKind::Struct | TokenKind::Union => {
                let token = self.tokens.next().unwrap();
                self.struct_or_union_specifier(&token)
            }
            TokenKind::Enum => {
                let token = self.tokens.next().unwrap();
                self.enum_specifier(&token)
            }
            // typedefed type
            TokenKind::Ident(..) => {
                if self.typedefs.get(token.unwrap_string()).is_some() {
                    self.tokens.next().unwrap();
                    Ok(SpecifierKind::UserType)
                } else {
                    Err(Error::new(token, ErrorKind::NotType(token.kind.clone())))
                }
            }
            _ if !token.is_type() => Err(Error::new(token, ErrorKind::NotType(token.kind.clone()))),
            // otherwise parse primitive
            _ => Ok(self
                .tokens
                .next()
                .expect("can only be types because of previous check")
                .into()),
        }
    }
    fn is_type(&self, token: &Token) -> bool {
        if let TokenKind::Ident(..) = token.kind {
            return self.typedefs.get(token.unwrap_string()).is_some();
        }
        token.is_type()
    }
    fn is_specifier(&self, token: &Token) -> bool {
        self.is_type(token) || token.is_storageclass()
    }
}

// some_struct->member
// equivalent to:
// (*some_struct).member
fn arrow_sugar(left: ExprKind, member: Token, arrow_token: Token) -> ExprKind {
    ExprKind::MemberAccess {
        token: arrow_token,
        member: member.clone(),
        expr: Box::new(ExprKind::Unary {
            token: Token { kind: TokenKind::Star, ..member },
            right: Box::new(left),
        }),
    }
}

// a[i] <=> *(a + i)
pub fn index_sugar(token: Token, expr: ExprKind, index: ExprKind) -> ExprKind {
    ExprKind::Unary {
        token: Token { kind: TokenKind::Star, ..token.clone() },
        right: Box::new(ExprKind::Binary {
            left: Box::new(expr),
            token: Token { kind: TokenKind::Plus, ..token },
            right: Box::new(index),
        }),
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::compiler::scanner::Scanner;
    use crate::preprocess;
    use std::collections::HashMap;
    use std::path::Path;
    use std::path::PathBuf;

    macro_rules! token_default {
        ($token_type:expr) => {
            Token::new($token_type, 1, 1, "".to_string(), PathBuf::new())
        };
    }

    pub fn setup(input: &str) -> Parser {
        let pp_tokens = preprocess(
            Path::new(""),
            &Vec::new(),
            &Vec::new(),
            HashMap::new(),
            input.to_string(),
        )
        .unwrap();
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
            -Binary: '*'\n\
            --Binary: '/'\n\
            ---Literal: 3\n\
            ---Binary: '-'\n\
            ----Literal: 6\n\
            ----Literal: 7\n\
            --Literal: 2\n\
            -Literal: 1";

        assert_eq!(actual, expected);
    }

    #[test]
    fn label_statement() {
        let actual = setup_stmt(
            r#"
int main(){
    typedef int s;
    s:
        return 0;
}"#,
        );

        let expected = "FuncDef: 'main'
-Typedef-Declaration:
--Decl: 's'
-Label: 's'
--Return:
---Literal: 0";

        assert_eq!(actual, expected);
    }

    #[test]
    fn typedef_print() {
        let actual = setup_stmt(
            r#"
typedef int n, a = 2;

n some_var;"#,
        );
        let expected = r#"Typedef-Declaration:
-Decl: 'n'
-Init: 'a'
--Scalar:
---Literal: 2
Declaration:
-Decl: 'some_var'"#;

        assert_eq!(actual, expected);
    }
    #[test]
    fn cast_print() {
        let actual = setup_stmt(
            r#"
int main(){
    int a = (long*)12;
    int b = (long char)3;
}"#,
        );
        let expected = r#"FuncDef: 'main'
-Declaration:
--Init: 'a'
---Scalar:
----Cast: 'long *'
-----Literal: 12
-Declaration:
--Init: 'b'
---Scalar:
----Cast: 'invalid type'
-----Literal: 3"#;

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
        let expected = r#"Declaration:
-Decl: 'printf'
Declaration:
-Empty
Declaration:
-Init: 'a'
--Aggregate:
---Aggregate:
----Scalar:
-----Literal: 21
---Scalar:
----Literal: 33
FuncDef: 'main'
-Declaration:
--Init: 'i'
---Scalar:
----Literal: 0
--Decl: 'b'
-If:
--Literal: 1
--Block:
---Switch:
----Ident: 'b'
----Block:
-----Case:
------Binary: '+'
-------Literal: 1
-------Literal: 2
------Block:
-------Expr:
--------FuncCall:
---------Ident: 'printf'
---------String: 'case'
-------Break
-----Default:
------Expr:
-------FuncCall:
--------Ident: 'printf'
--------String: 'hello'
--Block:
---For:
----Declaration:
-----Init: 'i'
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
-Declaration:
--Decl: 'a'
-Label: 'end'
--Return:
---Literal: 1"#;

        assert_eq!(actual, expected);
    }

    #[test]
    fn empty_stmts() {
        let actual = setup_stmt(
            "
long a[10] = {};
int;
int main() {}
int some() {
  long b[10] = {};
  int a;

  {}
  return a;
}",
        );

        let expected = "Declaration:
-Init: 'a'
--Aggregate:
---Empty
Declaration:
-Empty
FuncDef: 'main'
-Empty
FuncDef: 'some'
-Declaration:
--Init: 'b'
---Aggregate:
----Empty
-Declaration:
--Decl: 'a'
-Block:
--Empty
-Return:
--Ident: 'a'";

        assert_eq!(actual, expected);
    }

    #[test]
    fn matches_works_on_enums_with_values() {
        let tokens = vec![
            token_default!(TokenKind::Number(2)),
            token_default!(TokenKind::Plus),
        ];
        let mut p = Parser::new(tokens);

        let result = match_next!(p, TokenKind::Number(_) | TokenKind::String(_));
        let expected = Some(token_default!(TokenKind::Number(2)));

        assert_eq!(result, expected);
    }
}
