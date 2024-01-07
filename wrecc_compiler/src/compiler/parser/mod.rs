pub mod double_peek;
pub mod fold;

use crate::compiler::ast::{decl::*, expr::*, stmt::*};
use crate::compiler::common::{environment::*, error::*, token::*, types::*};
use crate::compiler::parser::double_peek::*;

use std::collections::VecDeque;

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
        let mut errors = vec![];

        while self.tokens.peek().is_ok() {
            match self.external_declaration() {
                Ok(decl) => {
                    external_declarations.push(decl);
                }
                Err(e @ Error { kind: ErrorKind::Multiple(..), .. }) => {
                    errors.append(&mut e.flatten_multiple());
                }
                Err(e) => {
                    errors.push(e);
                    self.sync(TokenType::Semicolon);
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
        self.tokens.peek().ok()
    }

    fn maybe_sync(
        &mut self,
        result: Result<(), Error>,
        errors: &mut Vec<Error>,
        until: TokenType,
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
    fn sync(&mut self, until: TokenType) {
        let mut open_braces = 0;

        while let Some(token) = self.tokens.next() {
            match token.token {
                tok if tok == until && open_braces <= 0 => {
                    break;
                }
                TokenType::LeftBrace => open_braces += 1,
                TokenType::RightBrace => {
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
        let (specifiers, is_typedef) = self.declaration_specifiers(true)?;

        if self.matches(&[TokenKind::Semicolon]).is_some() {
            return Ok(ExternalDeclaration::Declaration(Declaration {
                specifiers,
                is_typedef,
                declarators: Vec::new(),
            }));
        }

        let declarator = self.declarator(DeclaratorKind::NoAbstract)?;

        if matches!(
            declarator.modifiers.last(),
            Some(DeclModifier::Function { .. })
        ) && matches!(
            self.tokens.peek(),
            Ok(Token { token: TokenType::LeftBrace, .. })
        ) {
            return self.function_definition(specifiers, is_typedef, declarator);
        }

        self.declaration(specifiers, is_typedef, declarator)
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
    ) -> Result<(Vec<DeclSpecifier>, bool), Error> {
        let mut specifiers = Vec::new();
        let mut is_typedef = false;

        while let Ok(token) = self.tokens.peek() {
            if self.is_type(token) {
                if matches!(token.token, TokenType::Ident(..)) && !specifiers.is_empty() {
                    break;
                }

                specifiers.push(DeclSpecifier {
                    token: token.clone(),
                    kind: self.type_specifier()?,
                });
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

        Ok((specifiers, is_typedef))
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
        while self.matches(&[TokenKind::Star]).is_some() {
            modifiers.push(DeclModifier::Pointer)
        }
    }

    // <direct-declarator> ::= <identifier>
    //                       | ( <declarator> )
    fn direct_declarator(
        &mut self,
        kind: DeclaratorKind,
    ) -> Result<(Option<Token>, Option<Vec<DeclModifier>>), Error> {
        if self.matches(&[TokenKind::LeftParen]).is_some() {
            let declarator = self.declarator(kind)?;
            self.consume(
                TokenKind::RightParen,
                "Expected closing ')' after declarator",
            )?;
            return Ok((declarator.name, Some(declarator.modifiers)));
        }

        let name = match kind {
            DeclaratorKind::NoAbstract => Some(self.consume(
                TokenKind::Ident,
                "Expected identifier following type-specifier",
            )?),
            DeclaratorKind::MaybeAbstract => self.matches(&[TokenKind::Ident]),
            DeclaratorKind::Abstract => None,
        };

        Ok((name, None))
    }

    // <type-suffix>         ::= [ {<constant-expression>}? ]
    //                         | ( <parameter-type-list> )
    fn type_suffix(&mut self, modifiers: &mut Vec<DeclModifier>) -> Result<(), Error> {
        let mut suffixes = Vec::new();

        while let Some(token) = self.matches(&[TokenKind::LeftParen, TokenKind::LeftBracket]) {
            suffixes.push(if let TokenType::LeftParen = token.token {
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
        let size = self.assignment()?;

        self.consume(
            TokenKind::RightBracket,
            "Expect closing ']' after array initialization",
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

        if self.matches(&[TokenKind::RightParen]).is_some() {
            return Ok(DeclModifier::Function { token, params, variadic });
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

            params.push(self.parameter_declaration()?);

            if self.matches(&[TokenKind::Comma]).is_none() {
                break;
            }
        }
        self.consume(
            TokenKind::RightParen,
            "Expect ')' after function parameters",
        )?;

        Ok(DeclModifier::Function { token, params, variadic })
    }

    // <parameter-declaration> ::= {<declaration-specifier>}+ <declarator>
    //                           | {<declaration-specifier>}+ <abstract-declarator>
    //                           | {<declaration-specifier>}+
    fn parameter_declaration(&mut self) -> Result<(Vec<DeclSpecifier>, Declarator), Error> {
        let (specifiers, _) = self.declaration_specifiers(false)?;
        let declarator = self.declarator(DeclaratorKind::MaybeAbstract)?;

        Ok((specifiers, declarator))
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
        is_typedef: bool,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        let name = declarator.name.expect("external-decls cannot be abstract");

        if is_typedef {
            return Err(Error::new(
                &name,
                ErrorKind::Regular("Typedef not allowed in function-definition"),
            ));
        }

        self.tokens.next().expect("consume peeked left-brace");

        let body = self.block()?;

        Ok(ExternalDeclaration::Function(
            DeclType {
                specifiers,
                modifiers: declarator.modifiers,
            },
            name,
            body,
        ))
    }

    fn declaration(
        &mut self,
        specifiers: Vec<DeclSpecifier>,
        is_typedef: bool,
        declarator: Declarator,
    ) -> Result<ExternalDeclaration, Error> {
        let mut declarators = Vec::new();
        let init = self.init_declarator(is_typedef, &declarator)?;

        declarators.push((declarator, init));

        while self.matches(&[TokenKind::Comma]).is_some() {
            let declarator = self.declarator(DeclaratorKind::NoAbstract)?;
            let init = self.init_declarator(is_typedef, &declarator)?;

            declarators.push((declarator, init));
        }
        self.consume(TokenKind::Semicolon, "Expect ';' after declaration")?;

        Ok(ExternalDeclaration::Declaration(Declaration {
            specifiers,
            declarators,
            is_typedef,
        }))
    }
    fn init_declarator(
        &mut self,
        is_typedef: bool,
        Declarator { name, .. }: &Declarator,
    ) -> Result<Option<Init>, Error> {
        let name = name.clone().unwrap();

        if is_typedef {
            self.typedefs.declare(name.unwrap_string(), ());
        }

        let init = if self.matches(&[TokenKind::Equal]).is_some() {
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
        if self.matches(&[TokenKind::LeftBrace]).is_some() {
            let init_list = self.initializer_list(token, designator)?;

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
        let mut errors = Vec::new();

        while !self.check(TokenKind::RightBrace) {
            let result = || -> Result<(), Error> {
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

                Ok(())
            }();

            if self.maybe_sync(result, &mut errors, TokenType::RightBrace) {
                break;
            }
        }

        if errors.is_empty() {
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
        } else {
            Err(Error::new_multiple(errors))
        }
    }

    fn parse_designator(&mut self) -> Result<Option<VecDeque<Designator>>, Error> {
        let mut result = VecDeque::new();

        while let Some(token) = self.matches(&[TokenKind::Dot, TokenKind::LeftBracket]) {
            if let TokenType::Dot = token.token {
                if let Some(ident) = self.matches(&[TokenKind::Ident]) {
                    result.push_back(Designator {
                        token: ident.clone(),
                        kind: DesignatorKind::Member(ident.unwrap_string()),
                    });
                } else {
                    return Err(Error::new(
                        &token,
                        ErrorKind::Regular("Expect identifier as member designator"),
                    ));
                }
            } else {
                let designator_expr = self.assignment()?;

                self.consume(
                    TokenKind::RightBracket,
                    "Expect closing ']' after array designator",
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
    fn enumerator_list(&mut self, token: &Token) -> Result<Vec<(Token, Option<Expr>)>, Error> {
        let mut constants = Vec::new();
        let mut errors = Vec::new();

        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }

        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let result = || -> Result<(), Error> {
                let ident =
                    self.consume(TokenKind::Ident, "Expect identifier in enum definition")?;
                let init = if self.matches(&[TokenKind::Equal]).is_some() {
                    Some(self.ternary_conditional()?)
                } else {
                    None
                };
                constants.push((ident.clone(), init));

                if !self.check(TokenKind::RightBrace) {
                    self.consume(
                        TokenKind::Comma,
                        "Expect ',' seperating expressions in enum-specifier",
                    )?;
                }
                Ok(())
            }();

            if self.maybe_sync(result, &mut errors, TokenType::RightBrace) {
                break;
            }
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

        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }

        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let result = || -> Result<(), Error> {
                let (specifiers, _) = self.declaration_specifiers(false)?;
                let mut declarators = Vec::new();

                loop {
                    let declarator = self.declarator(DeclaratorKind::NoAbstract)?;
                    declarators.push(declarator);

                    if self.matches(&[TokenKind::Comma]).is_none() {
                        break;
                    }
                }
                members.push((specifiers, declarators));

                if let Err(e) =
                    self.consume(TokenKind::Semicolon, "Expect ';' after member declaration")
                {
                    errors.push(e);
                }
                Ok(())
            }();

            self.maybe_sync(result, &mut errors, TokenType::Semicolon);
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
        let name = self.matches(&[TokenKind::Ident]);

        let members = if self.matches(&[TokenKind::LeftBrace]).is_some() {
            Some(self.struct_declaration(token)?)
        } else {
            None
        };

        Ok(match token.token {
            TokenType::Struct => SpecifierKind::Struct(name, members),
            TokenType::Union => SpecifierKind::Union(name, members),
            _ => unreachable!("not struct/union specifier"),
        })
    }

    // <enum-specifier> ::= enum <identifier> { <enumerator-list> }
    //                    | enum { <enumerator-list> }
    //                    | enum <identifier>
    fn enum_specifier(&mut self, token: &Token) -> Result<SpecifierKind, Error> {
        let name = self.matches(&[TokenKind::Ident]);

        let members = if self.matches(&[TokenKind::LeftBrace]).is_some() {
            Some(self.enumerator_list(token)?)
        } else {
            None
        };

        Ok(SpecifierKind::Enum(name, members))
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
                TokenType::LeftBrace => Ok(Stmt::Block(self.block()?)),
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
        let value = self.assignment()?;

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
        let value = match self.check(TokenKind::Semicolon) {
            false => Some(self.expression()?),
            true => None,
        };

        self.consume(TokenKind::Semicolon, "Expect ';' after return statement")?;
        Ok(Stmt::Return(keyword, value))
    }
    fn for_statement(&mut self) -> Result<Stmt, Error> {
        let left_paren = self.consume(TokenKind::LeftParen, "Expect '(' after for-statement")?;

        self.typedefs.enter();

        let init = match self.is_specifier(self.tokens.peek()?) {
            true => self.external_declaration().and_then(|decl| match decl {
                ExternalDeclaration::Declaration(decl) => {
                    // if let Some(decl_kind) = decl
                    //     .iter()
                    //     .find(|kind| !matches!(kind, DeclarationKind::VarDecl(..)))
                    // {
                    //     return Err(Error::new(
                    //         decl_kind.get_token(),
                    //         ErrorKind::Regular(
                    //             "Cannot have non-variable declaration in 'for'-loop",
                    //         ),
                    //     ));
                    // } else {
                    Ok(Some(Box::new(Stmt::Declaration(decl))))
                    // }
                }
                ExternalDeclaration::Function(_, name, _) => {
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

        self.typedefs.exit();

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

        self.typedefs.enter();

        while let Ok(token) = self.tokens.peek().map(|tok| tok.clone()) {
            if token.token == TokenType::RightBrace {
                break;
            }
            let result = || -> Result<(), Error> {
                let stmt = match self.is_specifier(&token) {
                    true => self.external_declaration().and_then(|decl| match decl {
                        ExternalDeclaration::Declaration(decl) => Ok(Stmt::Declaration(decl)),
                        ExternalDeclaration::Function(_, name, _) => Err(Error::new(
                            &name,
                            ErrorKind::Regular("Cannot define functions in 'block'-statement"),
                        )),
                    }),
                    false => self.statement(),
                }?;

                statements.push(stmt);
                Ok(())
            }();

            self.maybe_sync(result, &mut errors, TokenType::Semicolon);
        }

        if let Err(e) = self.consume(TokenKind::RightBrace, "Expected closing '}' after Block") {
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
        let else_branch = if self.matches(&[TokenKind::Else]).is_some() {
            Some(Box::new(self.statement()?))
        } else {
            None
        };
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
                        let decl_type = self.type_name()?;

                        self.typecast(token, decl_type)?
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
                            let decl_type = self.type_name()?;

                            self.consume(TokenKind::RightParen, "Expect closing ')' after sizeof")?;
                            return Ok(Expr::new(
                                ExprKind::SizeofType { decl_type, value: 0 },
                                ValueKind::Rvalue,
                            ));
                        }
                    }

                    let right = self.unary()?;
                    Expr::new(
                        ExprKind::SizeofExpr { expr: Box::new(right), value: 0 },
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
    fn typecast(&mut self, token: Token, decl_type: DeclType) -> Result<Expr, Error> {
        self.consume(TokenKind::RightParen, "Expect closing ')' after type-cast")?;
        let expr = self.unary()?;

        Ok(Expr::new(
            ExprKind::Cast {
                token,
                decl_type,
                direction: None,
                new_type: NEWTypes::default(),
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
                // a[expr]
                TokenType::LeftBracket => {
                    let index = self.expression()?;
                    self.consume(
                        TokenKind::RightBracket,
                        "Expect closing ']' after array-index",
                    )?;
                    expr = index_sugar(token, expr, index);
                }
                // a()
                TokenType::LeftParen => {
                    expr = self.call(token, expr)?;
                }
                // some.member or some->member
                TokenType::Dot | TokenType::Arrow => {
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
        if let Some(s) = self.matches(&[TokenKind::Ident]) {
            return Ok(Expr::new(ExprKind::Ident(s), ValueKind::Lvalue));
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
    fn type_specifier(&mut self) -> Result<SpecifierKind, Error> {
        let token = self.tokens.peek()?;
        match token.token {
            TokenType::Struct | TokenType::Union => {
                let token = self.tokens.next().unwrap();
                self.struct_or_union_specifier(&token)
            }
            TokenType::Enum => {
                let token = self.tokens.next().unwrap();
                self.enum_specifier(&token)
            }
            // typedefed type
            TokenType::Ident(..) => {
                if self.typedefs.get(token.unwrap_string()).is_some() {
                    self.tokens.next().unwrap();
                    Ok(SpecifierKind::UserType)
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
                .into()),
        }
    }
    fn is_type(&self, token: &Token) -> bool {
        if let TokenType::Ident(..) = token.token {
            return self.typedefs.get(token.unwrap_string()).is_some();
        }
        token.is_type()
    }
    fn is_specifier(&self, token: &Token) -> bool {
        self.is_type(token) || matches!(token.token, TokenType::TypeDef)
    }
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
