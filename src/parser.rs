use crate::codegen::register::*;
use crate::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use crate::into_newtype;
use initializer_list_types::*;
use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    // public so I can set it up in unit-tests
    pub env: Scope,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: tokens.into_iter().peekable(),
            env: Scope::new(),
        }
    }
    // return identifier namespace table
    pub fn parse(mut self) -> Option<(Vec<Stmt>, Vec<Symbols>)> {
        let mut statements: Vec<Stmt> = Vec::new();
        let mut had_error = false;

        while self.tokens.peek().is_some() {
            match self.external_declaration() {
                Ok(v) => statements.push(v),
                Err(e) => {
                    e.print_error();
                    self.synchronize();
                    had_error = true;
                }
            }
        }
        if had_error {
            None
        } else {
            Some((statements, self.env.get_symbols()))
        }
    }
    fn synchronize(&mut self) {
        let mut prev = self.tokens.next();

        while let Some(v) = self.tokens.peek() {
            if prev.unwrap().token == TokenType::Semicolon {
                match v.token {
                    TokenType::If
                    | TokenType::Return
                    | TokenType::While
                    | TokenType::For
                    | TokenType::Char
                    | TokenType::Int
                    | TokenType::Long
                    | TokenType::Void
                    | TokenType::Struct
                    | TokenType::Union
                    | TokenType::Enum => return,
                    _ => (),
                }
            }
            prev = self.tokens.next();
        }
    }
    fn external_declaration(&mut self) -> Result<Stmt, Error> {
        if self.matches(vec![TokenKind::Semicolon]).is_some() {
            return Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)));
        }
        match self.matches_type() {
            Ok(t) => {
                if let Some(left) = self.matches(vec![TokenKind::LeftBracket]) {
                    return Err(Error::new(&left, ErrorKind::BracketsNotAllowed));
                }
                if self.matches(vec![TokenKind::Semicolon]).is_some() {
                    Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)))
                } else {
                    self.declaration(t)
                }
            }
            Err(_) if self.matches(vec![TokenKind::TypeDef]).is_some() => self.typedef(),
            Err(e) => Err(e),
        }
    }
    fn statement(&mut self) -> Result<Stmt, Error> {
        if let Some(token) = self.matches(vec![
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
        if let Some(ident) = self.matches(vec![TokenKind::Ident]) {
            if self.matches(vec![TokenKind::Colon]).is_some() {
                return self.label_statement(ident);
            }
            // if not a label then has to be expression so have to insert ident back into iter
            self.insert_token(ident)
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

        self.env.enter();

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

        self.env.exit();

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

        while let Some(token) = self.tokens.peek() {
            if token.token == TokenType::RightBrace {
                break;
            }
            let s = match self.external_declaration() {
                Err(e @ Error { kind: ErrorKind::UndeclaredType(..), .. }) => {
                    let token = self.tokens.next().ok_or(Error::eof())?;
                    if let TokenType::Ident(..) = self.peek()?.token {
                        return Err(e);
                    } else {
                        self.insert_token(token);
                        self.statement()?
                    }
                }
                Err(Error { kind: ErrorKind::NotType(..), .. }) => self.statement()?,
                Err(e) => return Err(e),
                Ok(s) => s,
            };
            statements.push(s);
        }
        self.consume(TokenKind::RightBrace, "Expect '}' after Block")?;
        self.env.exit();

        Ok(statements)
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
        if self.matches(vec![TokenKind::Else]).is_some() {
            else_branch = Some(self.statement()?)
        }
        Ok(Stmt::If(
            keyword,
            condition,
            Box::new(then_branch),
            Box::new(else_branch),
        ))
    }
    fn parse_ptr(&mut self, mut type_decl: NEWTypes) -> NEWTypes {
        while self.matches(vec![TokenKind::Star]).is_some() {
            type_decl.pointer_to();
        }
        type_decl
    }
    fn parse_arr(&mut self, type_decl: NEWTypes) -> Result<NEWTypes, Error> {
        if let Some(token) = self.matches(vec![TokenKind::LeftBracket]) {
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
        while self.matches(vec![TokenKind::RightBrace]).is_none() {
            let ident = self.consume(TokenKind::Ident, "Expect identifier in enum definition")?;
            if let Some(t) = self.matches(vec![TokenKind::Equal]) {
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
        while self.matches(vec![TokenKind::RightBrace]).is_none() {
            let member_type = self.matches_type()?;
            loop {
                let member_specifier = self.parse_ptr(member_type.clone());
                let name = self.consume(TokenKind::Ident, "Expect identifier after type")?;

                match member_specifier {
                    NEWTypes::Struct(ref s) | NEWTypes::Union(ref s) if !s.is_complete() => {
                        return Err(Error::new(
                            &name,
                            ErrorKind::IncompleteType(member_specifier),
                        ));
                    }
                    _ if member_specifier.is_void() => {
                        return Err(Error::new(
                            &name,
                            ErrorKind::IncompleteType(member_specifier),
                        ));
                    }
                    _ => (),
                }

                let member_specifier = self.parse_arr(member_specifier)?;

                members.push((member_specifier, name));
                if self.matches(vec![TokenKind::Comma]).is_none() {
                    break;
                }
            }

            self.consume(TokenKind::Semicolon, "Expect ';' after member declaration")?;
        }

        check_duplicate(&members)?;

        Ok(members)
    }
    fn parse_aggregate(&mut self, token: &Token) -> Result<NEWTypes, Error> {
        let name = self.matches(vec![TokenKind::Ident]);
        let has_members = self.matches(vec![TokenKind::LeftBrace]);

        match (&name, has_members) {
            (Some(name), Some(_)) => {
                Ok(match token.token {
                    TokenType::Struct | TokenType::Union => {
                        let index = self.env.declare_type(
                            name,
                            Tags::Aggregate(StructRef::new(token.clone().token)),
                        )?;

                        let members = self.parse_members(token)?;

                        let custom_type = self.env.get_mut_type(index);
                        let Tags::Aggregate(struct_ref) = custom_type else { unreachable!()};

                        struct_ref.update(members);

                        into_newtype!(&token.token, name.unwrap_string(), custom_type.clone())
                    }
                    TokenType::Enum => {
                        let members = self.parse_enum(token)?;

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
                                    Tags::Aggregate(StructRef::new(token.clone().token))
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

                Ok(into_newtype!(
                    &token.token,
                    name.unwrap_string(),
                    custom_type
                ))
            }
            (None, Some(_)) => Ok(if token.token == TokenType::Enum {
                into_newtype!(self.parse_enum(token)?)
            } else {
                into_newtype!(token.token, self.parse_members(token)?)
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

        // doesnt need to generate any statements for later stages
        // because types get resolved in the parser
        Ok(Stmt::Expr(Expr::new(ExprKind::Nop, ValueKind::Rvalue)))
    }
    fn declaration(&mut self, type_decl: NEWTypes) -> Result<Stmt, Error> {
        let mut decls = Vec::new();
        let decl = self.init_decl(type_decl.clone())?;

        if let (DeclarationKind::FuncDecl(name), true) = (
            decl.clone(),
            self.matches(vec![TokenKind::LeftBrace]).is_some(),
        ) {
            return self.function_definition(name);
        }

        decls.push(decl);
        while self.matches(vec![TokenKind::Comma]).is_some() {
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

        if self.matches(vec![TokenKind::LeftParen]).is_some() {
            self.function_decl(type_decl, name)
        } else {
            let is_global = self.env.is_global();
            type_decl = self.parse_arr(type_decl)?;

            let index = self
                .env
                .declare_symbol(&name, Symbols::Variable(SymbolInfo::new(type_decl.clone())))?;
            name.token.update_index(index);

            if self.matches(vec![TokenKind::Equal]).is_some() {
                self.var_initialization(name, type_decl, is_global)
            } else {
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
        match self.initializers(&type_decl) {
            Some(elements) => {
                let assign_sugar = list_sugar_assign(
                    name.clone(),
                    &mut elements?,
                    type_decl.clone(),
                    true,
                    Expr::new(ExprKind::Ident(name.clone()), ValueKind::Lvalue),
                );

                Ok(DeclarationKind::InitList(
                    type_decl,
                    name,
                    assign_sugar,
                    is_global,
                ))
            }
            None => {
                let r_value = self.var_assignment()?;

                Ok(DeclarationKind::Init(type_decl, name, r_value, is_global))
            }
        }
    }
    fn compare_existing(
        &mut self,
        name: &Token,
        index: usize,
        existing: Option<(Symbols, usize)>,
    ) -> Result<(), Error> {
        // compare with existing symbol in symbol table
        let is_def = self.peek()?.token == TokenType::LeftBrace;
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

    fn parse_designator(&mut self, type_decl: &NEWTypes) -> Result<((usize, usize), bool), Error> {
        let mut result = (0, 0);
        let mut found = false;
        if let Some(t) = self.matches(vec![TokenKind::Dot]) {
            // parse member-designator {.member = value}
            if let NEWTypes::Struct(s) | NEWTypes::Union(s) = type_decl {
                if let Some(ident) = self.matches(vec![TokenKind::Ident]) {
                    let member = ident.unwrap_string();
                    let index = if let Some(i) = s
                        .members()
                        .iter()
                        .position(|(_, name)| name.unwrap_string() == member)
                    {
                        i
                    } else {
                        return Err(Error::new(
                            &ident,
                            ErrorKind::NonExistantMember(member, type_decl.clone()),
                        ));
                    };
                    result.0 = s
                        .members()
                        .iter()
                        .take_while(|(_, name)| name.unwrap_string() != member)
                        .fold(0, |acc, (t, _)| acc + type_element_count(t));
                    found = true;
                    // parse chained designators
                    let (index_inc, depth_inc) =
                        match self.parse_designator(&s.members()[index].0)? {
                            (_, false) => (0, result.1),
                            (n, true) => n,
                        };
                    result.0 += index_inc;
                    result.1 += depth_inc;
                } else {
                    return Err(Error::new(
                        &t,
                        ErrorKind::Regular("Expect identifier as member designator"),
                    ));
                }
            } else {
                return Err(Error::new(
                    &t,
                    ErrorKind::Regular(
                        "Can only use member designator on type 'struct' and 'union' not 'array'",
                    ),
                ));
            }
        } else if let Some(t) = self.matches(vec![TokenKind::LeftBracket]) {
            // parse array-designator {[3] = value}
            if let NEWTypes::Array { of, .. } = type_decl {
                let mut designator_expr = self.var_assignment()?;
                let designator_constant =
                    designator_expr.get_literal_constant(&t, &self.env, "Array designator")?;

                result.0 = designator_constant as usize * type_element_count(of);

                self.consume(
                    TokenKind::RightBracket,
                    "Expect closing ']' after array designator",
                )?;

                found = true;
                // parse chained designators
                let (inc, new_type) = match self.parse_designator(of)? {
                    (_, false) => (0, result.1),
                    (n, true) => n,
                };
                result.0 += inc;
                result.1 = new_type;
            } else {
                return Err(Error::new(
                    &t,
                    ErrorKind::InvalidArrayDesignator(type_decl.clone()),
                ));
            }
        }
        Ok((result, found))
    }

    fn initializers(&mut self, type_decl: &NEWTypes) -> Option<Result<Vec<Expr>, Error>> {
        let token = match self.peek() {
            Ok(t) => t.clone(),
            Err(e) => return Some(Err(e)),
        };
        match (token.token.clone(), type_decl.clone()) {
            (TokenType::LeftBrace, _) => {
                self.tokens.next();
                Some(self.initializer_list(type_decl, token))
            }
            (TokenType::String(mut s), NEWTypes::Array { amount, of })
                if matches!(*of, NEWTypes::Primitive(Types::Char)) =>
            {
                // char s[] = "abc" identical to char s[] = {'a','b','c','\0'} (6.7.8)
                self.tokens.next();
                if amount < s.len() {
                    return Some(Err(Error::new(
                        &token,
                        ErrorKind::TooLong("Initializer-string", amount, s.len()),
                    )));
                }
                let mut diff = amount - s.len();
                while diff > 0 {
                    diff -= 1;
                    s.push('\0'); // append implicit NULL terminator to string
                }

                Some(Ok(s
                    .as_bytes()
                    .iter()
                    .map(|c| Expr::new_literal(*c as i64, Types::Char))
                    .collect()))
            }
            _ => None,
        }
    }
    fn initializer_list(&mut self, type_decl: &NEWTypes, token: Token) -> Result<Vec<Expr>, Error> {
        let element_types = match init_default(type_decl) {
            ElementType::Multiple(mut m) => match m.clone()[0].clone() {
                ElementType::Multiple(mut v) => {
                    v.remove(0);
                    m[0] = ElementType::Multiple(v);
                    m
                }
                _ => m,
            },
            ElementType::Single(s) => {
                return Err(Error::new(
                    &token,
                    ErrorKind::NonAggregateInitializer(type_decl.clone(), s),
                ))
            }
        };
        let mut elements =
            vec![Expr::new(ExprKind::Nop, ValueKind::Rvalue); type_element_count(type_decl)];
        let mut element_index = 0;
        let mut depth;
        let mut found_des;

        while !self.check(TokenKind::RightBrace) {
            depth = 0;
            ((element_index, depth), found_des) = match self.parse_designator(type_decl)? {
                (_, false) => ((element_index, depth), false),
                (result, true) => {
                    self.consume(TokenKind::Equal, "Expect '=' after array designator")?;
                    ((result), true)
                }
            };
            if let Some((actual, expected)) =
                init_overflow(type_decl, found_des, element_index + 1, elements.len())
            {
                return Err(Error::new(
                    &token,
                    ErrorKind::InitializerOverflow(expected, actual),
                ));
            }
            // this is really verbose but i have to check for a valid index beforehand
            match self.peek()?.token {
                TokenType::LeftBrace => {
                    for e in self
                        .initializers(&element_types[element_index].at(depth))
                        .unwrap()?
                    {
                        elements[element_index] = e;
                        element_index += 1;
                    }
                }
                TokenType::String(..)
                    if element_types[element_index].contains_char_arr().is_some() =>
                {
                    for e in self
                        .initializers(&element_types[element_index].contains_char_arr().unwrap())
                        .unwrap()?
                    {
                        elements[element_index] = e;
                        element_index += 1;
                    }
                }
                _ => {
                    elements[element_index] = self.var_assignment()?;
                    element_index += 1;
                }
            }
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

        Ok(elements)
    }
    fn parse_params(&mut self) -> Result<Vec<(NEWTypes, Token)>, Error> {
        let mut params = Vec::new();
        if self.matches(vec![TokenKind::RightParen]).is_some() {
            return Ok(params);
        }
        loop {
            let mut param_type = self.matches_specifier()?;
            let mut name = self.consume(TokenKind::Ident, "Expect identifier after type")?;

            param_type = self.parse_arr(param_type)?;
            if let NEWTypes::Array { of, .. } = param_type {
                param_type = NEWTypes::Pointer(of);
            }
            // insert parameters into symbol table
            let index = self.env.declare_symbol(
                &name,
                Symbols::Variable(SymbolInfo::new(param_type.clone())),
            )?;
            name.token.update_index(index);

            params.push((param_type, name));

            if self.matches(vec![TokenKind::Comma]).is_none() {
                break;
            }
        }
        self.consume(
            TokenKind::RightParen,
            "Expect ')' after function parameters",
        )?;
        Ok(params)
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

        // params can't be in same scope as function-name so
        // they get added after they have been parsed
        self.env.enter();
        let params = self.parse_params()?;

        self.env.get_mut_symbol(index).unwrap_func().params = params;

        self.compare_existing(&name, index, existing)?;

        Ok(DeclarationKind::FuncDecl(name))
    }
    fn function_definition(&mut self, name: Token) -> Result<Stmt, Error> {
        let index = name.token.get_index();
        self.env.get_mut_symbol(index).unwrap_func().kind = FunctionKind::Definition;
        let body = self.block()?;

        Ok(Stmt::Function(name, body))
    }
    pub fn expression(&mut self) -> Result<Expr, Error> {
        self.comma()
    }
    fn comma(&mut self) -> Result<Expr, Error> {
        let mut expr = self.var_assignment()?;

        while self.matches(vec![TokenKind::Comma]).is_some() {
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

        if let Some(t) = self.matches(vec![TokenKind::Equal]) {
            let value = self.var_assignment()?;
            return Ok(Expr::new(
                ExprKind::Assign {
                    l_expr: Box::new(expr),
                    token: t,
                    r_expr: Box::new(value),
                },
                ValueKind::Rvalue,
            ));
        } else if let Some(t) = self.matches(vec![
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

        while let Some(token) = self.matches(vec![TokenKind::Question]) {
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

        while let Some(token) = self.matches(vec![TokenKind::PipePipe]) {
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

        while let Some(token) = self.matches(vec![TokenKind::AmpAmp]) {
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

        while let Some(token) = self.matches(vec![TokenKind::Pipe]) {
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

        while let Some(token) = self.matches(vec![TokenKind::Xor]) {
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

        while let Some(token) = self.matches(vec![TokenKind::Amp]) {
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

        while let Some(token) = self.matches(vec![TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = token;
            let right = self.comparison()?;
            expr = Expr::new(
                ExprKind::Binary {
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

        while let Some(token) = self.matches(vec![
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::Less,
            TokenKind::LessEqual,
        ]) {
            let operator = token;
            let right = self.shift()?;
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
    fn shift(&mut self) -> Result<Expr, Error> {
        let mut expr = self.term()?;

        while let Some(token) = self.matches(vec![TokenKind::GreaterGreater, TokenKind::LessLess]) {
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

        while let Some(token) = self.matches(vec![TokenKind::Minus, TokenKind::Plus]) {
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

        while let Some(token) =
            self.matches(vec![TokenKind::Slash, TokenKind::Star, TokenKind::Mod])
        {
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
        if let Some(token) = self.matches(vec![
            TokenKind::Star,
            TokenKind::Amp,
            TokenKind::Bang,
            TokenKind::Tilde,
            TokenKind::Minus,
            TokenKind::PlusPlus,
            TokenKind::MinusMinus,
            TokenKind::LeftParen,
            TokenKind::Sizeof,
        ]) {
            return Ok(match token.token {
                // ++a or --a is equivalent to a += 1 or a -= 1
                TokenType::PlusPlus | TokenType::MinusMinus => {
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
                TokenType::LeftParen => match self.matches_specifier() {
                    Ok(type_decl) => self.typecast(token, type_decl)?,
                    Err(Error {
                        kind: ErrorKind::NotType(_) | ErrorKind::UndeclaredType(..),
                        ..
                    }) => {
                        self.insert_token(token);

                        return self.postfix();
                    }
                    Err(e) => return Err(e),
                },
                TokenType::Sizeof => {
                    // sizeof expr doesnt need parentheses but sizeof type does
                    if let Some(t) = self.matches(vec![TokenKind::LeftParen]) {
                        match self.matches_specifier() {
                            Ok(type_decl) => {
                                let type_decl = self.parse_arr(type_decl)?;
                                self.consume(
                                    TokenKind::RightParen,
                                    "Expect closing ')' after sizeof",
                                )?;
                                Expr::new(
                                    ExprKind::SizeofType { value: type_decl.size() },
                                    ValueKind::Rvalue,
                                )
                            }
                            Err(Error {
                                kind: ErrorKind::NotType(_) | ErrorKind::UndeclaredType(..),
                                ..
                            }) => {
                                self.insert_token(t);
                                let right = self.unary()?;
                                Expr::new(
                                    ExprKind::SizeofExpr { expr: Box::new(right), value: None },
                                    ValueKind::Rvalue,
                                )
                            }
                            Err(e) => return Err(e),
                        }
                    } else {
                        let right = self.unary()?;
                        Expr::new(
                            ExprKind::SizeofExpr { expr: Box::new(right), value: None },
                            ValueKind::Rvalue,
                        )
                    }
                }
                _ => {
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

        while let Some(token) = self.matches(vec![
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
                    if let Some(member) = self.matches(vec![TokenKind::Ident]) {
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
            if !type_decl.is_complete() {
                return Err(Error::new(
                    token,
                    ErrorKind::IncompleteMemberAccess(type_decl),
                ));
            }
        }
        Ok(())
    }
    fn call(&mut self, left_paren: Token, callee: Expr) -> Result<Expr, Error> {
        let mut args = Vec::new();
        if !self.check(TokenKind::RightParen) {
            loop {
                args.push(self.var_assignment()?);
                if self.matches(vec![TokenKind::Comma]).is_none() {
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
        if let Some(n) = self.matches(vec![TokenKind::Number]) {
            let n = n.unwrap_num();
            return Ok(Expr::new_literal(n, integer_type(n)));
        }
        if let Some(c) = self.matches(vec![TokenKind::CharLit]) {
            return Ok(Expr::new_literal(c.unwrap_char() as i64, Types::Char));
        }
        if let Some(mut s) = self.matches(vec![TokenKind::Ident]) {
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
        if let Some(s) = self.matches(vec![TokenKind::String]) {
            return Ok(Expr::new(ExprKind::String(s), ValueKind::Lvalue));
        }

        if self.matches(vec![TokenKind::LeftParen]).is_some() {
            let expr = self.expression()?;
            self.consume(TokenKind::RightParen, "missing closing ')'")?;
            return Ok(Expr::new(
                ExprKind::Grouping { expr: Box::new(expr.clone()) },
                expr.value_kind,
            ));
        }
        let t = self.peek()?;
        Err(Error::new(
            t,
            ErrorKind::ExpectedExpression(t.token.clone()),
        ))
    }
    fn consume(&mut self, token: TokenKind, msg: &'static str) -> Result<Token, Error> {
        match self.tokens.next() {
            Some(v) => {
                if TokenKind::from(&v.token) != token {
                    Err(Error::new(&v, ErrorKind::Regular(msg)))
                } else {
                    Ok(v)
                }
            }
            None => Err(Error::eof()),
        }
    }
    fn check(&mut self, expected: TokenKind) -> bool {
        if let Some(token) = self.tokens.peek() {
            return TokenKind::from(&token.token) == expected;
        }
        false
    }

    fn peek(&mut self) -> Result<&Token, Error> {
        match self.tokens.peek() {
            Some(t) => Ok(t),
            None => Err(Error::eof()),
        }
    }
    fn matches(&mut self, expected: Vec<TokenKind>) -> Option<Token> {
        match self.tokens.peek() {
            Some(v) => {
                if !expected.contains(&TokenKind::from(&v.token)) {
                    return None;
                }
            }
            None => return None,
        }
        self.tokens.next()
    }
    fn matches_type(&mut self) -> Result<NEWTypes, Error> {
        match self.peek() {
            Ok(v) => {
                if !v.is_type() && !matches!(v.token, TokenType::Ident(..)) {
                    return Err(Error::new(v, ErrorKind::NotType(v.token.clone())));
                }
                let v = v.clone();
                let type_decl = match v.token {
                    TokenType::Struct | TokenType::Union | TokenType::Enum => {
                        let token = self
                            .tokens
                            .next()
                            .expect("can unwrap because successfull peek");
                        self.parse_aggregate(&token)?
                    }
                    // typedefed type
                    TokenType::Ident(..) => {
                        if let Ok((Symbols::TypeDef(t), _)) = self.env.get_symbol(&v) {
                            self.tokens.next();
                            t
                        } else {
                            return Err(Error::new(&v, ErrorKind::NotType(v.token.clone())));
                        }
                    }
                    // otherwise parse primitive
                    _ => self
                        .tokens
                        .next()
                        .expect("can only be types because of previous check")
                        .into_type(),
                };

                Ok(type_decl)
            }
            Err(e) => Err(e),
        }
    }
    fn matches_specifier(&mut self) -> Result<NEWTypes, Error> {
        let t = self.matches_type()?;
        Ok(self.parse_ptr(t))
    }
    // hacky and slow way of inserting token back into iterator
    // TODO: remove this by using multipeek() when adding libraries
    fn insert_token(&mut self, token: Token) {
        let mut start = vec![token];
        while let Some(t) = self.tokens.next() {
            start.push(t);
        }
        self.tokens = start.into_iter().peekable();
    }
}

fn get_ident(expr: &Expr) -> Option<&Token> {
    // get ident from an expression passed to a member access so:
    // expr.member or expr->member
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

fn array_of(type_decl: NEWTypes, size: i64) -> NEWTypes {
    NEWTypes::Array {
        amount: size as usize,
        of: Box::new(type_decl),
    }
}

fn type_element_count(type_decl: &NEWTypes) -> usize {
    match type_decl {
        NEWTypes::Array { amount, of } => amount * type_element_count(of),
        NEWTypes::Struct(s) | NEWTypes::Union(s) => {
            let mut result = 0;
            for m in s.members().iter() {
                result += type_element_count(&m.0);
            }
            result
        }
        _ => 1,
    }
}
fn init_overflow(
    type_decl: &NEWTypes,
    found_designator: bool,
    element_index: usize,
    mut len: usize,
) -> Option<(usize, usize)> {
    // union intializer can only have single element if no designator used
    if let (NEWTypes::Union(s), false) = (type_decl, found_designator) {
        len = type_element_count(&s.members()[0].0);
    }

    if element_index > len {
        Some((element_index, len))
    } else {
        None
    }
}

fn arrow_sugar(left: Expr, member: Token, arrow_token: Token) -> Expr {
    // some_struct->member
    // equivalent to:
    // (*some_struct).member
    Expr::new(
        ExprKind::MemberAccess {
            token: arrow_token,
            member: member.clone(),
            expr: Box::new(Expr::new(
                ExprKind::Grouping {
                    expr: Box::new(Expr::new(
                        ExprKind::Unary {
                            token: Token::new(
                                TokenType::Star,
                                member.line_index,
                                member.column,
                                member.line_string,
                            ),
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

fn list_sugar_assign(
    token: Token,
    list: &mut Vec<Expr>,
    type_decl: NEWTypes,
    is_outer: bool,
    left: Expr,
) -> Vec<Expr> {
    // int a[3] = {1,2,3};
    // equivalent to:
    // int a[3];
    // a[0] = 1;
    // a[1] = 2;
    // a[2] = 3;
    if let NEWTypes::Array { amount, of } = type_decl.clone() {
        let mut result = Vec::new();
        for ((i, _), arr_i) in list
            .iter()
            .enumerate()
            .step_by(type_element_count(&of))
            .zip(0..amount)
        {
            for (offset, l_expr) in list_sugar_assign(
                token.clone(),
                &mut list[i..list.len()].to_vec(),
                *of.clone(),
                false,
                index_sugar(
                    token.clone(),
                    left.clone(),
                    Expr::new_literal(arr_i as i64, Types::Int),
                ),
            )
            .into_iter()
            .enumerate()
            {
                let value = if let ExprKind::Nop = list[i + offset].kind.clone() {
                    Expr::new_literal(0, Types::Int)
                } else {
                    list[i + offset].clone()
                };
                result.push(match is_outer {
                    true => Expr::new(
                        ExprKind::Assign {
                            l_expr: Box::new(l_expr),
                            token: token.clone(),
                            r_expr: Box::new(value),
                        },
                        ValueKind::Rvalue,
                    ),
                    false => l_expr,
                })
            }
        }
        result
    } else if let NEWTypes::Struct(s) | NEWTypes::Union(s) = type_decl.clone() {
        let mut result = Vec::new();
        let mut members = s.members().to_vec();

        if let NEWTypes::Union(_) = type_decl {
            remove_unused_members(&mut members, list);
        }

        for member_i in 0..members.len() {
            let i = members
                .iter()
                .take(member_i)
                .fold(0, |acc, (t, _)| acc + type_element_count(t));
            for (offset, l_expr) in list_sugar_assign(
                token.clone(),
                &mut list[i..list.len()].to_vec(),
                members[member_i].clone().0,
                false,
                Expr::new(
                    ExprKind::MemberAccess {
                        token: token.clone(),
                        member: members[member_i].clone().1,
                        expr: Box::new(left.clone()),
                    },
                    ValueKind::Lvalue,
                ),
            )
            .into_iter()
            .enumerate()
            {
                let value = if let ExprKind::Nop = list[i + offset].kind.clone() {
                    Expr::new_literal(0, Types::Int)
                } else {
                    list[i + offset].clone()
                };
                result.push(match is_outer {
                    true => Expr::new(
                        ExprKind::Assign {
                            l_expr: Box::new(l_expr),
                            token: token.clone(),
                            r_expr: Box::new(value),
                        },
                        ValueKind::Rvalue,
                    ),
                    false => l_expr,
                })
            }
        }
        result
    } else {
        vec![left]
    }
}
fn remove_unused_members(members: &mut Vec<(NEWTypes, Token)>, list: &mut Vec<Expr>) {
    // remove unused members so they don't overwrite existing ones
    let old_members = members.clone();
    let mut new_members = vec![];
    let mut new_list = vec![];
    let mut i = 0;

    for m in old_members.iter() {
        let type_len = type_element_count(&m.0);
        if !list[i..i + type_len]
            .iter()
            .all(|e| matches!(e.kind, ExprKind::Nop))
        {
            new_members.push(m.clone());
            for e in list[i..i + type_len].iter() {
                new_list.push(e.clone())
            }
        }
        i += type_len;
    }

    *list = new_list;
    *members = new_members;
}
fn index_sugar(token: Token, expr: Expr, index: Expr) -> Expr {
    // a[i] <=> *(a + i)
    Expr::new(
        ExprKind::Unary {
            token: Token::new(
                TokenType::Star,
                token.line_index,
                token.column,
                token.line_string.clone(),
            ),
            right: Box::new(Expr::new(
                ExprKind::Grouping {
                    expr: Box::new(Expr::new(
                        ExprKind::Binary {
                            left: Box::new(expr),
                            token: Token::new(
                                TokenType::Plus,
                                token.line_index,
                                token.column,
                                token.line_string,
                            ),
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

// TODO: this definitely needs a cleanup/rewrite
// creates a list of types for any given initializer list
mod initializer_list_types {
    use super::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum ElementType {
        Multiple(Vec<ElementType>),
        Single(NEWTypes),
    }
    impl ElementType {
        pub fn contains_char_arr(&self) -> Option<NEWTypes> {
            match self {
                Self::Multiple(m) => m.iter().find_map(|x| x.contains_char_arr()),
                Self::Single(t) => match t {
                    NEWTypes::Array { of, .. }
                        if matches!(**of, NEWTypes::Primitive(Types::Char)) =>
                    {
                        Some(t.clone())
                    }
                    _ => None,
                },
            }
        }
        pub fn at(&self, depth: usize) -> NEWTypes {
            match self {
                Self::Multiple(m) => {
                    if let ElementType::Single(s) = m[depth].clone() {
                        s
                    } else {
                        unreachable!()
                    }
                }
                Self::Single(t) => t.clone(),
            }
        }
        pub fn flatten(&self) -> Vec<ElementType> {
            match self {
                Self::Multiple(v) => {
                    let mut result = vec![];
                    for e in v {
                        if let ElementType::Multiple(..) = *e {
                            for s in e.flatten() {
                                result.push(s);
                            }
                        } else {
                            result.push(e.clone());
                        }
                    }
                    result
                }
                Self::Single(_) => vec![self.clone()],
            }
        }
    }

    // creates array that groups types when they are at the same index:
    // struct Some {
    //   char s[3];
    //   int age;
    // };
    // struct Some arr[2];
    // => [Multiple(Some-arr,Some,Char-arr,Char),Single(Char),Single(Char),Single(Int),
    // Multiple(Some-arr,Some,Char-arr,Char),Single(Char),Single(Char),Single(Int)]
    pub fn init_default(type_decl: &NEWTypes) -> ElementType {
        match type_decl {
            NEWTypes::Array { of, amount } => match init_default(of) {
                ElementType::Single(s) => {
                    let start = ElementType::Multiple(vec![
                        ElementType::Single(type_decl.clone()),
                        ElementType::Single(s.clone()),
                    ]);
                    let mut result = vec![start];
                    for _ in 1..*amount {
                        result.push(ElementType::Single(s.clone()));
                    }
                    ElementType::Multiple(result)
                }
                ElementType::Multiple(v) => {
                    let mut start = vec![ElementType::Single(type_decl.clone())];
                    let mut rest_start = vec![];
                    for e in v[0].flatten() {
                        start.push(e.clone());
                        rest_start.push(e);
                    }
                    let mut result = vec![ElementType::Multiple(start)];
                    let mut rest = vec![ElementType::Multiple(rest_start)];

                    for e in v.into_iter().skip(1) {
                        result.push(e.clone());
                        rest.push(e);
                    }
                    for _ in 1..*amount {
                        for e in rest.clone() {
                            result.push(e);
                        }
                    }
                    ElementType::Multiple(result)
                }
            },
            NEWTypes::Struct(s) | NEWTypes::Union(s) => {
                let mut start = vec![ElementType::Single(type_decl.clone())];
                let mut result = vec![];
                for (i, (t, _)) in s.members().iter().enumerate() {
                    match init_default(t) {
                        ElementType::Single(s) => {
                            if i == 0 {
                                start.push(ElementType::Single(s))
                            } else {
                                result.push(ElementType::Single(s))
                            }
                        }
                        ElementType::Multiple(v) => {
                            if i == 0 {
                                for e in v[0].flatten() {
                                    start.push(e);
                                }
                                for e in v.clone().into_iter().skip(1) {
                                    result.push(e);
                                }
                            } else {
                                for e in v.clone().into_iter() {
                                    result.push(e);
                                }
                            }
                        }
                    };
                }
                result.insert(0, ElementType::Multiple(start));
                ElementType::Multiple(result)
            }
            _ => ElementType::Single(type_decl.clone()),
        }
    }
    #[cfg(test)]
    mod tests {
        use super::*;

        // typedef struct {
        //   int x;
        //   int y;
        // } Point;

        // typedef struct {
        //   Point start;
        //   Point end;
        // } Line;

        // typedef struct {
        //   char name[5];
        //   int age;
        //   Line address;
        // } Person;
        #[allow(non_snake_case)]
        #[test]
        fn complex_struct() {
            let Point = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
            ]));
            let Line = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (Point.clone(), Token::default(TokenType::Comma)),
                (Point.clone(), Token::default(TokenType::Comma)),
            ]));
            let Person = NEWTypes::Struct(StructInfo::Anonymous(vec![
                (
                    NEWTypes::Array {
                        of: Box::new(NEWTypes::Primitive(Types::Char)),
                        amount: 5,
                    },
                    Token::default(TokenType::Comma),
                ),
                (
                    NEWTypes::Primitive(Types::Int),
                    Token::default(TokenType::Comma),
                ),
                (Line.clone(), Token::default(TokenType::Comma)),
            ]));

            let expected = ElementType::Multiple(vec![
                ElementType::Multiple(vec![
                    ElementType::Single(Person.clone()),
                    ElementType::Single(NEWTypes::Array {
                        of: Box::new(NEWTypes::Primitive(Types::Char)),
                        amount: 5,
                    }),
                    ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Char)),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ElementType::Multiple(vec![
                    ElementType::Single(Line.clone()),
                    ElementType::Single(Point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ElementType::Multiple(vec![
                    ElementType::Single(Point.clone()),
                    ElementType::Single(NEWTypes::Primitive(Types::Int)),
                ]),
                ElementType::Single(NEWTypes::Primitive(Types::Int)),
            ]);
            let actual = init_default(&Person);

            assert_eq!(actual, expected);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scanner::Scanner;

    macro_rules! token_default {
        ($token_type:expr) => {
            Token::new($token_type, 1, 1, "".to_string())
        };
    }

    fn assert_ast(input: &str, expected: &str) {
        let mut scanner = Scanner::new(input);
        let tokens = scanner.scan_token().unwrap();

        let mut parser = Parser::new(tokens);
        // using ternary_conditional as expression evaluator because assignment() and expression()
        // get folded and we don't test for assign or comma in these unit tests anyways
        let actual = parser.ternary_conditional().unwrap();

        assert_eq!(actual.kind.to_string(), expected);
    }
    #[test]
    fn unary_precedence() {
        let input = "-2++.some";
        let expected = "Unary: '-'\n\
            -MemberAccess: 'some'\n\
            --PostUnary: '++'\n\
            ---Literal: 2\n";

        assert_ast(input, expected);
    }

    #[test]
    fn creates_ast_for_expression() {
        let input = "32 + 1 * 2";
        let expected = "Binary: '+'\n\
            -Literal: 32\n\
            -Binary: '*'\n\
            --Literal: 1\n\
            --Literal: 2\n";

        assert_ast(input, expected);
    }
    #[test]
    fn nested_groupings() {
        let input = "(3 / (6 - 7) * 2) + 1";
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
            -Literal: 1\n";

        assert_ast(input, expected);
    }

    #[test]
    fn matches_works_on_enums_with_values() {
        let tokens = vec![
            token_default!(TokenType::Number(2)),
            token_default!(TokenType::Plus),
        ];
        let mut p = Parser::new(tokens);

        let result = p.matches(vec![TokenKind::Number, TokenKind::String]);
        let expected = Some(token_default!(TokenType::Number(2)));
        assert_eq!(result, expected);
    }

    #[test]
    fn multidimensional_array_size() {
        let input = NEWTypes::Array {
            amount: 2,
            of: Box::new(NEWTypes::Array {
                amount: 2,
                of: Box::new(NEWTypes::Primitive(Types::Int)),
            }),
        };
        let actual = type_element_count(&input);

        assert_eq!(actual, 4);
    }
}
