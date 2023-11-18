use crate::compiler::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use crate::compiler::wrecc_codegen::register::*;
use crate::compiler::wrecc_parser::double_peek::*;
use crate::into_newtype;

use std::collections::VecDeque;

pub struct Parser {
    tokens: DoublePeek<Token>,

    // public so I can set it up in unit-tests
    pub env: Scope,

    // nest-depth to indicate matching synchronizing token
    nest_level: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: DoublePeek::new(tokens),
            env: Scope::new(),
            nest_level: 0,
        }
    }
    // return list of all statements and identifier namespace table
    pub fn parse(mut self) -> Result<(Vec<Stmt>, Vec<Symbols>), Vec<Error>> {
        let mut statements: Vec<Stmt> = Vec::new();
        let mut errors = vec![];

        while self.tokens.peek().is_ok() {
            match self.external_declaration() {
                Ok(v) => statements.push(v),
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
            Ok((statements, self.env.get_symbols()))
        } else {
            Err(errors)
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

    pub fn external_declaration(&mut self) -> Result<Stmt, Error> {
        if self.matches(&[TokenKind::Semicolon]).is_some() {
            return Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)));
        }

        if self.matches(&[TokenKind::TypeDef]).is_some() {
            return self.typedef();
        }

        let type_decl = self.matches_type()?;
        if let Some(left) = self.matches(&[TokenKind::LeftBracket]) {
            return Err(Error::new(&left, ErrorKind::BracketsNotAllowed));
        }
        if self.matches(&[TokenKind::Semicolon]).is_some() {
            Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)))
        } else {
            self.declaration(type_decl)
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
        let mut value = self.var_assignment()?;
        let value = value.get_literal_constant(&token, &self.env, "Case value")?;

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
        let init = match self.matches_specifier() {
            Ok(type_decl) => Some(Box::new(self.declaration(type_decl)?)),
            _ if !self.check(TokenKind::Semicolon) => Some(Box::new(self.expression_statement()?)),
            _ => {
                self.consume(TokenKind::Semicolon, "Expect ';' in for loop")?;
                None
            }
        };

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
            let stmt = match self.external_declaration() {
                Err(e) if matches!(e.kind, ErrorKind::UndeclaredType(_)) => {
                    if let TokenType::Ident(..) = self.tokens.double_peek()?.token {
                        self.tokens.next().unwrap();
                        Err(e)
                    } else {
                        self.statement()
                    }
                }
                Err(e) if matches!(e.kind, ErrorKind::NotType(_)) => self.statement(),
                stmt => stmt,
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
    fn parse_ptr(&mut self, mut type_decl: NEWTypes) -> NEWTypes {
        while self.matches(&[TokenKind::Star]).is_some() {
            type_decl.pointer_to();
        }
        type_decl
    }
    fn parse_arr(&mut self, type_decl: NEWTypes) -> Result<NEWTypes, Error> {
        if let Some(token) = self.matches(&[TokenKind::LeftBracket]) {
            let mut size = self.var_assignment()?;
            let size = size.get_literal_constant(&token, &self.env, "Array size specifier")?;

            self.consume(
                TokenKind::RightBracket,
                "Expect closing ']' after array initialization",
            )?;

            if size > 0 {
                Ok(array_of(self.parse_arr(type_decl)?, size))
            } else {
                Err(Error::new(&token, ErrorKind::NegativeArraySize))
            }
        } else {
            Ok(type_decl)
        }
    }
    fn parse_enum(&mut self, token: &Token) -> Result<Vec<(Token, i32)>, Error> {
        let mut members = Vec::new();
        let mut index: i32 = 0;
        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }
        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let ident = self.consume(TokenKind::Ident, "Expect identifier in enum definition")?;
            if let Some(t) = self.matches(&[TokenKind::Equal]) {
                let mut index_expr = self.var_assignment()?;
                index = index_expr.get_literal_constant(&t, &self.env, "Enum Constant")? as i32;
            }
            members.push((ident.clone(), index));

            // insert enum constant into symbol table
            self.env.declare_symbol(
                &ident,
                Symbols::Variable(SymbolInfo {
                    type_decl: NEWTypes::Primitive(Types::Int),
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
    fn parse_members(&mut self, token: &Token) -> Result<Vec<(NEWTypes, Token)>, Error> {
        let mut members = Vec::new();

        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(token, ErrorKind::IsEmpty(token.token.clone())));
        }

        while self.matches(&[TokenKind::RightBrace]).is_none() {
            let member_type = self.matches_type()?;
            loop {
                let member_specifier = self.parse_ptr(member_type.clone());
                let name = self.consume(TokenKind::Ident, "Expect identifier after type")?;
                let member_specifier = self.parse_arr(member_specifier)?;

                if !member_specifier.is_complete() {
                    return Err(Error::new(
                        &name,
                        ErrorKind::IncompleteType(member_specifier),
                    ));
                }

                members.push((member_specifier, name));
                if self.matches(&[TokenKind::Comma]).is_none() {
                    break;
                }
            }

            self.consume(TokenKind::Semicolon, "Expect ';' after member declaration")?;
        }

        check_duplicate(&members)?;

        Ok(members)
    }
    fn parse_aggregate(&mut self, token: &Token) -> Result<NEWTypes, Error> {
        let name = self.matches(&[TokenKind::Ident]);
        let has_members = self.matches(&[TokenKind::LeftBrace]);

        match (&name, has_members) {
            (Some(name), Some(_)) => {
                Ok(match token.token {
                    TokenType::Struct | TokenType::Union => {
                        self.nest_level += 1;
                        let index = self.env.declare_type(
                            name,
                            Tags::Aggregate(StructRef::new(token.clone().token, true)),
                        )?;

                        let members = self.parse_members(token)?;
                        self.nest_level -= 1;

                        let custom_type = self.env.get_mut_type(index);
                        let Tags::Aggregate(struct_ref) = custom_type else { unreachable!()};

                        struct_ref.update(members);

                        into_newtype!(&token, name.unwrap_string(), custom_type.clone())
                    }
                    TokenType::Enum => {
                        self.nest_level += 1;
                        let members = self.parse_enum(token)?;
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
                    Ok((t, _)) => {
                        if token.token != *t.get_kind() {
                            return Err(Error::new(
                                name,
                                ErrorKind::TypeAlreadyExists(
                                    name.unwrap_string(),
                                    token.token.clone(),
                                ),
                            ));
                        }
                        t
                    }
                    Err(_) => {
                        let index = self.env.declare_type(
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
                        )?;
                        self.env.get_mut_type(index).clone()
                    }
                };

                Ok(into_newtype!(&token, name.unwrap_string(), custom_type))
            }
            (None, Some(_)) => Ok(if token.token == TokenType::Enum {
                self.nest_level += 1;
                let enum_values = self.parse_enum(token)?;
                self.nest_level -= 1;

                into_newtype!(enum_values)
            } else {
                self.nest_level += 1;
                let members = self.parse_members(token)?;
                self.nest_level -= 1;

                into_newtype!(token, members)
            }),
            (None, None) => Err(Error::new(
                token,
                ErrorKind::EmptyAggregate(token.token.clone()),
            )),
        }
    }

    fn typedef(&mut self) -> Result<Stmt, Error> {
        let type_decl = self.matches_specifier()?;
        let name = self.consume(TokenKind::Ident, "Expect identifier following type")?;

        self.env
            .declare_symbol(&name, Symbols::TypeDef(type_decl))?;
        self.consume(TokenKind::Semicolon, "Expect ';' after typedef-declaration")?;

        // Doesn't need to generate any statements for later stages because types get resolved in the parser
        Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)))
    }
    fn declaration(&mut self, type_decl: NEWTypes) -> Result<Stmt, Error> {
        let mut decls = Vec::new();
        let decl = self.init_decl(type_decl.clone())?;

        if let (DeclarationKind::FuncDecl(name), true) = (
            decl.clone(),
            self.matches(&[TokenKind::LeftBrace]).is_some(),
        ) {
            return self.function_definition(name);
        }

        decls.push(decl);
        while self.matches(&[TokenKind::Comma]).is_some() {
            let decl = self.init_decl(type_decl.clone())?;
            decls.push(decl);
        }
        self.consume(TokenKind::Semicolon, "Expect ';' after declaration")?;

        Ok(Stmt::Declaration(decls))
    }
    fn init_decl(&mut self, mut type_decl: NEWTypes) -> Result<DeclarationKind, Error> {
        type_decl = self.parse_ptr(type_decl);
        let mut name = self.consume(
            TokenKind::Ident,
            "Expect identifier following type-specifier",
        )?;

        if self.matches(&[TokenKind::LeftParen]).is_some() {
            self.function_decl(type_decl, name)
        } else {
            let is_global = self.env.is_global();
            type_decl = self.parse_arr(type_decl)?;

            let index = self
                .env
                .declare_symbol(&name, Symbols::Variable(SymbolInfo::new(type_decl.clone())))?;
            name.token.update_index(index);

            if self.matches(&[TokenKind::Equal]).is_some() {
                if !type_decl.is_complete() {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(type_decl)));
                }

                self.var_initialization(name, type_decl, is_global)
            } else {
                let tentative_decl = self.env.is_global() && type_decl.is_aggregate();
                if !type_decl.is_complete() && !tentative_decl {
                    return Err(Error::new(&name, ErrorKind::IncompleteType(type_decl)));
                }

                Ok(DeclarationKind::Decl(type_decl, name, is_global))
            }
        }
    }
    fn var_initialization(
        &mut self,
        name: Token,
        type_decl: NEWTypes,
        is_global: bool,
    ) -> Result<DeclarationKind, Error> {
        let init = self.initializers(&name, None)?;

        Ok(DeclarationKind::Initializer(
            type_decl, name, init, is_global,
        ))
    }
    fn initializers(
        &mut self,
        token: &Token,
        designator: Option<VecDeque<Designator>>,
    ) -> Result<Init, Error> {
        if self.matches(&[TokenKind::LeftBrace]).is_some() {
            self.nest_level += 1;
            let init_list = self.initializer_list(&token, designator)?;
            self.nest_level -= 1;

            Ok(init_list)
        } else {
            let r_value = self.var_assignment()?;

            Ok(Init {
                token: token.clone(),
                designator,
                kind: InitKind::Scalar(r_value),
                offset: 0,
            })
        }
    }

    fn compare_existing(
        &mut self,
        name: &Token,
        index: usize,
        existing: Option<(Symbols, usize)>,
    ) -> Result<(), Error> {
        // compare with existing symbol in symbol table
        let is_def = self.tokens.peek()?.token == TokenType::LeftBrace;
        match existing {
            Some((Symbols::Func(other), ..)) => {
                if is_def && other.kind == FunctionKind::Definition {
                    return Err(Error::new(
                        name,
                        ErrorKind::Redefinition("function", name.unwrap_string()),
                    ));
                }

                self.env
                    .get_mut_symbol(index)
                    .unwrap_func()
                    .cmp(name, &other)?;

                // if existing element is a definition remove newly added declaration
                // so that last function symbol with this name is a definition
                // and can properly check for redefinitions
                if !is_def && other.kind == FunctionKind::Definition {
                    self.env.remove_symbol(index);
                }
            }
            Some(..) => {
                return Err(Error::new(
                    name,
                    ErrorKind::Redefinition("symbol", name.unwrap_string()),
                ));
            }
            None => {}
        }
        if !is_def {
            self.env.exit();
        }
        Ok(())
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
                    result.push_back(Designator::Member(ident.unwrap_string()));
                } else {
                    return Err(Error::new(
                        &t,
                        ErrorKind::Regular("Expect identifier as member designator"),
                    ));
                }
            } else {
                let mut designator_expr = self.var_assignment()?;
                let literal =
                    designator_expr.get_literal_constant(&t, &self.env, "Array designator")?;

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

                result.push_back(Designator::Array(literal))
            }
        }
        if result.is_empty() {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }
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

            let mut param_type = self.matches_specifier()?;
            let mut name = self.matches(&[TokenKind::Ident]);

            param_type = self.parse_arr(param_type)?;
            if let NEWTypes::Array { of, .. } = param_type {
                param_type = NEWTypes::Pointer(of);
            }

            if let Some(name) = &mut name {
                // insert parameters into symbol table
                let index = self
                    .env
                    .declare_symbol(name, Symbols::Variable(SymbolInfo::new(param_type.clone())))?;
                name.token.update_index(index);
            }

            params.push((param_type, name));

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
    fn function_decl(
        &mut self,
        return_type: NEWTypes,
        mut name: Token,
    ) -> Result<DeclarationKind, Error> {
        // TODO: function declarations CAN be declared in non-global scope
        if !self.env.is_global() {
            return Err(Error::new(
                &name,
                ErrorKind::Regular("Can only define functions in global scope"),
            ));
        }
        let existing = self.env.get_symbol(&name).ok();
        let func = Function::new(return_type);
        let index = self.env.declare_func(&name, Symbols::Func(func))?;

        name.token.update_index(index);

        // params can't be in same scope as function-name so they get added after they
        // have been parsed
        self.env.enter();
        let (params, variadic) = self.parse_params().map_err(|e| {
            self.env.exit();
            e
        })?;

        self.env.get_mut_symbol(index).unwrap_func().params = params;
        self.env.get_mut_symbol(index).unwrap_func().variadic = variadic;

        self.compare_existing(&name, index, existing).map_err(|e| {
            self.env.exit();
            e
        })?;

        Ok(DeclarationKind::FuncDecl(name))
    }
    fn function_definition(&mut self, name: Token) -> Result<Stmt, Error> {
        let index = name.token.get_index();
        let func = self.env.get_mut_symbol(index).unwrap_func();

        let return_type = func.return_type.clone();
        if !return_type.is_complete() && !return_type.is_void() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteReturnType(name.unwrap_string(), return_type),
            ));
        }

        if let Some(param_type) = func.has_incomplete_params() {
            return Err(Error::new(
                &name,
                ErrorKind::IncompleteFuncArg(name.unwrap_string(), param_type.clone()),
            ));
        }

        if func.has_unnamed_params() {
            return Err(Error::new(&name, ErrorKind::UnnamedFuncParams));
        }

        func.kind = FunctionKind::Definition;
        let body = self.block()?;

        Ok(Stmt::Function(name, body))
    }
    pub fn expression(&mut self) -> Result<Expr, Error> {
        self.comma()
    }
    fn comma(&mut self) -> Result<Expr, Error> {
        let mut expr = self.var_assignment()?;

        while self.matches(&[TokenKind::Comma]).is_some() {
            expr = Expr::new(
                ExprKind::Comma {
                    left: Box::new(expr),
                    right: Box::new(self.var_assignment()?),
                },
                ValueKind::Rvalue,
            )
        }

        Ok(expr)
    }
    fn var_assignment(&mut self) -> Result<Expr, Error> {
        let expr = self.ternary_conditional()?;

        if let Some(t) = self.matches(&[TokenKind::Equal]) {
            let value = self.var_assignment()?;
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
            let value = self.var_assignment()?;

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
                        let type_decl = self.matches_specifier()?;
                        let type_decl = self.parse_arr(type_decl)?;

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
                            let type_decl = self.matches_specifier()?;
                            let type_decl = self.parse_arr(type_decl)?;

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

        if let Ok((
            Symbols::Variable(SymbolInfo { type_decl, .. })
            | Symbols::Func(Function { return_type: type_decl, .. }),
            _,
        )) = self.env.get_symbol(ident)
        {
            complete_access(token, &type_decl)?
        }
        Ok(())
    }
    fn call(&mut self, left_paren: Token, callee: Expr) -> Result<Expr, Error> {
        let mut args = Vec::new();
        if !self.check(TokenKind::RightParen) {
            loop {
                args.push(self.var_assignment()?);
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
            let (symbol, table_index) = self.env.get_symbol(&s)?;

            // give the token the position of the symbol in symbol-table
            s.token.update_index(table_index);

            return Ok(match symbol {
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
    fn matches_type(&mut self) -> Result<NEWTypes, Error> {
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
                if let Ok((Symbols::TypeDef(t), _)) = self.env.get_symbol(token) {
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
            return matches!(self.env.get_symbol(token), Ok((Symbols::TypeDef(_), _)));
        }
        token.is_type()
    }
    fn matches_specifier(&mut self) -> Result<NEWTypes, Error> {
        let t = self.matches_type()?;
        Ok(self.parse_ptr(t))
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

fn array_of(type_decl: NEWTypes, size: i64) -> NEWTypes {
    NEWTypes::Array {
        amount: size as usize,
        of: Box::new(type_decl),
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
mod tests {
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

    fn setup(input: &str) -> Parser {
        let pp_tokens = preprocess(Path::new(""), input).unwrap();
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
            .map(|(stmt, _)| stmt)
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
  int i = 0;
  int b;
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
        let expected = r#"FuncDecl: 'printf'
Expr:
-Nop
Init: 'a'
-Aggregate:
--Aggregate:
---Scalar:
----Literal: 21
--Scalar:
---Literal: 33
Func: 'main'
-Init: 'i'
--Scalar:
---Literal: 0
-VarDecl: 'b'
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
----Init: 'i'
-----Scalar:
------Literal: 5
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
-VarDecl: 'a'
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
