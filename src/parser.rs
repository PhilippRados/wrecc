use crate::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use initiliazer_list_types::*;
use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
    env: Environment<NEWTypes>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: tokens.into_iter().peekable(),
            env: Environment::new(None),
        }
    }
    pub fn parse(&mut self) -> Option<Vec<Stmt>> {
        let mut statements: Vec<Stmt> = Vec::new();
        let mut had_error = false;

        while self.tokens.peek() != None {
            match self.declaration() {
                Ok(v) => statements.push(v),
                Err(Error::Indicator) => (),
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
            Some(statements)
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
    fn declaration(&mut self) -> Result<Stmt, Error> {
        match self.matches_type() {
            Ok(t) => {
                if let Some(left) = self.matches(vec![TokenKind::LeftBracket]) {
                    return Err(Error::new(
                        &left,
                        "Brackets not allowed here; Put them after the Identifier",
                    ));
                }
                match (
                    t.clone(),
                    self.matches(vec![TokenKind::Semicolon]).is_some(),
                ) {
                    // dont't generate any statement when defining struct
                    (NEWTypes::Struct(..) | NEWTypes::Union(..), true) => Err(Error::Indicator),
                    (NEWTypes::Enum(..), true) => Ok(Stmt::TypeDef(t)),
                    _ => self.type_declaration(t),
                }
            }
            Err(e) => Err(e),
        }
    }
    fn statement(&mut self) -> Result<Stmt, Error> {
        if self.matches(vec![TokenKind::For]).is_some() {
            return self.for_statement();
        }
        if let Some(t) = self.matches(vec![TokenKind::Return]) {
            return self.return_statement(t);
        }
        if let Some(t) = self.matches(vec![TokenKind::If]) {
            return self.if_statement(t);
        }
        if self.matches(vec![TokenKind::While]).is_some() {
            return self.while_statement();
        }
        if self.matches(vec![TokenKind::LeftBrace]).is_some() {
            return Ok(Stmt::Block(self.block()?));
        }
        self.expression_statement()
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

        let mut init = None;
        if let Ok(token) = self.matches_type() {
            init = Some(self.type_declaration(token)?);
        } else if !self.check(TokenKind::Semicolon) {
            init = Some(self.expression_statement()?)
        } else {
            self.consume(TokenKind::Semicolon, "Expect ';' in for loop")?;
        }

        let mut cond = None;
        if self.matches(vec![TokenKind::Semicolon]) == None {
            cond = Some(self.expression()?);
            self.consume(TokenKind::Semicolon, "Expect ';' after for-condition")?;
        }

        let mut inc = None;
        if self.matches(vec![TokenKind::RightParen]) == None {
            inc = Some(self.expression()?);
            self.consume(TokenKind::RightParen, "Expect ')' after for increment")?;
        }

        // for loop is syntax sugar for while loop
        let mut body = self.statement()?;
        if inc != None {
            body = Stmt::Block(vec![body, Stmt::Expr(inc.unwrap())]);
        }
        if cond != None {
            body = Stmt::While(left_paren, cond.unwrap(), Box::new(body));
        } else {
            // if no condition then condition is true
            body = Stmt::While(
                left_paren,
                Expr::new(ExprKind::Number(1), ValueKind::Rvalue),
                Box::new(body),
            );
        }
        if init != None {
            body = Stmt::Block(vec![init.unwrap(), body]);
        }

        Ok(body)
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

        self.env = Environment::new(Some(Box::new(self.env.clone())));
        while let Some(token) = self.tokens.peek() {
            if TokenKind::from(&token.token) == TokenKind::RightBrace {
                break;
            }
            let s = match self.peek()?.is_type() {
                true => match self.declaration() {
                    Err(Error::Indicator) => continue,
                    Err(e) => return Err(e),
                    Ok(s) => s,
                },
                false => self.statement()?,
            };
            statements.push(s);
        }
        self.consume(TokenKind::RightBrace, "Expect '}' after Block")?;
        self.env = *self.env.enclosing.as_ref().unwrap().clone();
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
        match self.matches(vec![TokenKind::Else]) {
            Some(_) => else_branch = Some(self.statement()?),
            None => (),
        }
        Ok(Stmt::If(
            keyword,
            condition,
            Box::new(then_branch),
            Box::new(else_branch),
        ))
    }
    fn parse_arr(&mut self, type_decl: NEWTypes) -> Result<NEWTypes, Error> {
        if self.matches(vec![TokenKind::LeftBracket]).is_some() {
            let size = self.consume(
                TokenKind::Number,
                "Expect array-size following array-declaration",
            )?;
            self.consume(
                TokenKind::RightBracket,
                "Expect closing ']' after array initialization",
            )?;

            if size.unwrap_num() > 0 {
                Ok(array_of(self.parse_arr(type_decl)?, size.unwrap_num()))
            } else {
                Err(Error::new(&size, "Can't initialize array with size <= 0"))
            }
        } else {
            Ok(type_decl)
        }
    }
    fn parse_enum(&mut self, token: &Token) -> Result<Vec<(Token, i32)>, Error> {
        let mut members = Vec::new();
        let mut index = 0;
        if self.check(TokenKind::RightBrace) {
            return Err(Error::new(
                token,
                &format!("Can't have empty {}", token.token),
            ));
        }
        while self.matches(vec![TokenKind::RightBrace]).is_none() {
            let ident = self.consume(TokenKind::Ident, "Expect identifier in enum definition")?;
            if self.matches(vec![TokenKind::Equal]).is_some() {
                if let Some(n) = self.matches(vec![TokenKind::Number, TokenKind::CharLit]) {
                    index = match n.token {
                        TokenType::CharLit(c) => c as i32,
                        TokenType::Number(n) => n,
                        _ => {
                            return Err(Error::new(
                                &n,
                                "Can only initialize enums with integer constants",
                            ))
                        }
                    }
                }
            }
            members.push((ident, index));
            index += 1;
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
            return Err(Error::new(
                token,
                &format!("Can't have empty {}", token.token),
            ));
        }
        while self.matches(vec![TokenKind::RightBrace]).is_none() {
            let mut member_type = self.matches_type()?;
            let name = self.consume(TokenKind::Ident, "Expect identifier after type")?;
            member_type = self.parse_arr(member_type)?;

            if member_type.is_void() {
                return Err(Error::new(
                    &name,
                    &format!("{} member can't have type 'void'", token.token),
                ));
            }

            members.push((member_type, name));
            self.consume(TokenKind::Semicolon, "Expect ';' after member declaration")?;
        }
        Ok(members)
    }
    fn parse_aggregate(&mut self, token: &Token) -> Result<NEWTypes, Error> {
        let name = self.matches(vec![TokenKind::Ident]);
        let has_members = self.matches(vec![TokenKind::LeftBrace]);

        match (&name, has_members) {
            (Some(name), Some(_)) => {
                if self.env.current.customs.contains_key(&name.unwrap_string()) {
                    return Err(Error::new(
                        name,
                        &format!("Redefinition of '{}'", name.unwrap_string()),
                    ));
                }

                Ok(match token.token {
                    TokenType::Struct | TokenType::Union => {
                        self.env
                            .declare_aggregate(name.unwrap_string(), token.clone().token);

                        let members = self.parse_members(token)?;
                        if let Customs::Aggregate(struct_ref) = self.env.get_type(name)? {
                            struct_ref.update(members);

                            match token.token {
                                TokenType::Union => NEWTypes::Union(StructInfo::Named(
                                    name.unwrap_string(),
                                    struct_ref,
                                )),
                                TokenType::Struct => NEWTypes::Struct(StructInfo::Named(
                                    name.unwrap_string(),
                                    struct_ref,
                                )),
                                _ => unreachable!(),
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    TokenType::Enum => {
                        let members = self.parse_enum(token)?;
                        self.env.init_enum(name.unwrap_string(), members.clone());
                        NEWTypes::Enum(Some(name.unwrap_string()), members, true)
                    }
                    _ => unreachable!(),
                })
            }
            (Some(name), None) => {
                // lookup struct/union definition
                let custom_type = self.env.get_type(name)?;
                if token.token != *custom_type.get_kind() {
                    return Err(Error::new(
                        name,
                        &format!(
                            "Type '{}' already exists but not as {}",
                            name.unwrap_string(),
                            token.token
                        ),
                    ));
                }

                Ok(match token.token {
                    TokenType::Union => NEWTypes::Union(StructInfo::Named(
                        name.unwrap_string(),
                        custom_type.unwrap_aggr(),
                    )),
                    TokenType::Struct => NEWTypes::Struct(StructInfo::Named(
                        name.unwrap_string(),
                        custom_type.unwrap_aggr(),
                    )),
                    TokenType::Enum => {
                        NEWTypes::Enum(Some(name.unwrap_string()), custom_type.unwrap_enum(), false)
                    }
                    _ => unreachable!(),
                })
            }
            (None, Some(_)) => Ok(match token.token {
                TokenType::Union => {
                    NEWTypes::Union(StructInfo::Anonymous(self.parse_members(token)?))
                }
                TokenType::Struct => {
                    NEWTypes::Struct(StructInfo::Anonymous(self.parse_members(token)?))
                }
                TokenType::Enum => NEWTypes::Enum(None, self.parse_enum(token)?, true),
                _ => unreachable!(),
            }),
            (None, None) => Err(Error::new(
                token,
                &format!("Can't declare anonymous {} without members", token.token),
            )),
        }
    }

    fn type_declaration(&mut self, mut type_decl: NEWTypes) -> Result<Stmt, Error> {
        let name = self.consume(
            TokenKind::Ident,
            "Expect identifier following type-specifier",
        )?;

        if self.matches(vec![TokenKind::LeftParen]).is_some() {
            self.function(type_decl, name)
        } else {
            type_decl = self.parse_arr(type_decl)?;

            if self.matches(vec![TokenKind::Equal]).is_some() {
                self.var_initialization(name, type_decl)
            } else {
                // declaration
                self.consume(
                    TokenKind::Semicolon,
                    "Expect ';' after variable declaration",
                )?;
                Ok(Stmt::DeclareVar(type_decl, name, false))
            }
        }
    }
    fn var_initialization(&mut self, name: Token, type_decl: NEWTypes) -> Result<Stmt, Error> {
        match self.initializers(&type_decl) {
            Some(elements) => {
                let assign_sugar = list_sugar_assign(
                    name.clone(),
                    &mut elements?,
                    type_decl.clone(),
                    true,
                    Expr::new(ExprKind::Ident(name.clone()), ValueKind::Lvalue),
                );

                self.consume(TokenKind::Semicolon, "Expect ';' after variable definition")?;
                Ok(Stmt::InitList(type_decl, name, assign_sugar, false))
            }
            None => {
                let r_value = self.expression()?;

                self.consume(TokenKind::Semicolon, "Expect ';' after variable definition")?;
                Ok(Stmt::InitVar(type_decl, name, r_value, false))
            }
        }
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
                            &format!("No member '{}' in '{}'", member, type_decl),
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
                    return Err(Error::new(&t, "Expect identifier as member designator"));
                }
            } else {
                return Err(Error::new(
                    &t,
                    "Can only use member designator on type 'struct' and 'union' not 'array'",
                ));
            }
        } else if let Some(t) = self.matches(vec![TokenKind::LeftBracket]) {
            // parse array-designator {[3] = value}
            if let NEWTypes::Array { of, .. } = type_decl {
                if let Some(n) = self.matches(vec![TokenKind::Number]) {
                    let n = n.unwrap_num() as usize * type_element_count(&**of); // have to offset by type
                    result.0 = n;
                } else {
                    return Err(Error::new(&t, "Expect number as array designator"));
                }
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
                    &format!(
                        "Can only use array designator on type 'array' not '{}'",
                        type_decl
                    ),
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
                        &format!(
                            "Initializer-string is too long. Expected: {}, Actual: {}",
                            amount,
                            s.len()
                        ),
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
                    .map(|c| Expr::new(ExprKind::CharLit(*c as i8), ValueKind::Rvalue))
                    .collect()))
            }
            _ => None,
        }
    }
    fn initializer_list(&mut self, type_decl: &NEWTypes, token: Token) -> Result<Vec<Expr>, Error> {
        let element_types = match init_default(type_decl) {
            ElementType::Multiple(m) => m,
            ElementType::Single(s) => {
                return Err(Error::new(
                    &token,
                    &format!(
                        "Can't initialize non-aggregate type '{}' with '{}'",
                        type_decl, s
                    ),
                ))
            }
        };
        let mut elements =
            vec![Expr::new(ExprKind::Nop, ValueKind::Rvalue); type_element_count(type_decl)];
        let mut element_index = 0;
        let mut depth;
        let mut found_des;
        let max_depth = element_types.iter().map(|e| e.len()).max().unwrap_or(1);

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
                    &format!(
                        "Initializer overflow. Expected size: {}, Actual size: {}",
                        expected, actual
                    ),
                ));
            }
            // this is really verbose but i have to check for a valid index beforehand
            match self.peek()?.token {
                TokenType::LeftBrace => {
                    for e in self
                        .initializers(&element_types[element_index].at(depth + 1, max_depth))
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
                    elements[element_index] = self.expression()?;
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
            let mut param_type = self.matches_type()?;
            let name = self.consume(TokenKind::Ident, "Expect identifier after type")?;

            param_type = self.parse_arr(param_type)?;
            if let NEWTypes::Array { of, .. } = param_type {
                param_type = NEWTypes::Pointer(of);
            }

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
    fn function(&mut self, return_type: NEWTypes, name: Token) -> Result<Stmt, Error> {
        if matches!(return_type, NEWTypes::Array { .. }) {
            return Err(Error::new(&name, "function can't return array-type"));
        }
        let params = self.parse_params()?;

        if self.matches(vec![TokenKind::Semicolon]).is_some() {
            Ok(Stmt::FunctionDeclaration(return_type, name, params))
        } else {
            self.consume(TokenKind::LeftBrace, "Expect '{' before function body.")?;
            let body = self.block()?;

            Ok(Stmt::Function(return_type, name, params, body))
        }
    }

    fn expression(&mut self) -> Result<Expr, Error> {
        self.var_assignment()
    }
    fn var_assignment(&mut self) -> Result<Expr, Error> {
        let expr = self.or()?;

        if let Some(t) = self.matches(vec![TokenKind::Equal]) {
            let value = self.expression()?;
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
            let value = self.expression()?;

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
        ]) {
            let right = self.unary()?;
            return Ok(match token.token {
                // ++a or --a is equivalent to a += 1 or a -= 1
                TokenType::PlusPlus | TokenType::MinusMinus => Expr::new(
                    ExprKind::CompoundAssign {
                        l_expr: Box::new(right),
                        token,
                        r_expr: Box::new(Expr::new(ExprKind::Number(1), ValueKind::Rvalue)),
                    },
                    ValueKind::Rvalue,
                ),
                _ => Expr::new(
                    ExprKind::Unary {
                        right: Box::new(right),
                        token: token.clone(),
                        is_global: false,
                    },
                    match token.token {
                        TokenType::Star => ValueKind::Lvalue,
                        _ => ValueKind::Rvalue,
                    },
                ),
            });
        }
        self.postfix()
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
                TokenType::Dot => {
                    // some_struct.member or some_union.member
                    if let Some(member) = self.matches(vec![TokenKind::Ident]) {
                        expr = Expr::new(
                            ExprKind::MemberAccess {
                                token,
                                member,
                                expr: Box::new(expr),
                            },
                            ValueKind::Lvalue,
                        );
                    } else {
                        return Err(Error::new(
                            &token,
                            "A member access must be followed by an identifer",
                        ));
                    }
                }
                TokenType::Arrow => {
                    // some_struct->member
                    if let Some(ident) = self.matches(vec![TokenKind::Ident]) {
                        expr = arrow_sugar(expr, ident, token);
                    } else {
                        return Err(Error::new(
                            &token,
                            "A member access must be followed by an identifer",
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
                args.push(self.expression()?);
                if self.matches(vec![TokenKind::Comma]) == None {
                    break;
                }
            }
        }
        self.consume(TokenKind::RightParen, "Expect ')' after function call")?;
        Ok(Expr::new(
            ExprKind::Call {
                left_paren,
                callee: Box::new(callee),
                args,
            },
            ValueKind::Rvalue,
        ))
    }
    fn primary(&mut self) -> Result<Expr, Error> {
        if let Some(n) = self.matches(vec![TokenKind::Number]) {
            return Ok(Expr::new(
                ExprKind::Number(n.unwrap_num()),
                ValueKind::Rvalue,
            ));
        }
        if let Some(c) = self.matches(vec![TokenKind::CharLit]) {
            return Ok(Expr::new(
                ExprKind::CharLit(c.unwrap_char()),
                ValueKind::Rvalue,
            ));
        }
        if let Some(s) = self.matches(vec![TokenKind::Ident]) {
            return Ok(Expr::new(ExprKind::Ident(s), ValueKind::Lvalue));
        }
        if let Some(s) = self.matches(vec![TokenKind::String]) {
            return Ok(Expr::new(ExprKind::String(s), ValueKind::Rvalue));
        }

        if self.matches(vec![TokenKind::LeftParen]).is_some() {
            let expr = self.expression()?;
            self.consume(TokenKind::RightParen, "missing closing ')'")?;
            return Ok(Expr::new(
                ExprKind::Grouping {
                    expr: Box::new(expr.clone()),
                },
                expr.value_kind,
            ));
        }
        let t = self.peek()?;
        Err(Error::new(
            t,
            &format!("Expected expression found: {}", t.token),
        ))
    }
    fn consume(&mut self, token: TokenKind, msg: &str) -> Result<Token, Error> {
        match self.tokens.next() {
            Some(v) => {
                if TokenKind::from(&v.token) != token {
                    Err(Error::new(&v, msg))
                } else {
                    Ok(v)
                }
            }
            None => Err(Error::Regular(ErrorData {
                line_index: -1,
                line_string: "".to_string(),
                column: -1,
                msg: msg.to_string(),
            })),
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
            None => Err(Error::Regular(ErrorData {
                line_index: -1,
                line_string: "".to_string(),
                column: -1,
                msg: "Expected expression found end of file".to_string(),
            })),
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
                if !v.is_type() {
                    return Err(Error::new(
                        v,
                        &format!("Expected type-declaration, found {}", v.token),
                    ));
                }
                let v = v.clone();
                let mut type_decl = match v.token {
                    TokenType::Struct | TokenType::Union | TokenType::Enum => {
                        let token = self
                            .tokens
                            .next()
                            .expect("can unwrap because successfull peek");
                        self.parse_aggregate(&token)?
                    }
                    // otherwise parse primitive
                    _ => self
                        .tokens
                        .next()
                        .expect("can only be types because of previous check")
                        .into_type(),
                };

                while self.matches(vec![TokenKind::Star]).is_some() {
                    type_decl.pointer_to();
                }
                match type_decl {
                    NEWTypes::Struct(ref s) | NEWTypes::Union(ref s) if !s.is_complete() => {
                        return Err(Error::new(
                            &v,
                            &format!("'{}' contains incomplete type", type_decl),
                        ));
                    }
                    _ => (),
                }
                Ok(type_decl)
            }
            Err(e) => Err(e),
        }
    }
}

fn array_of(type_decl: NEWTypes, size: i32) -> NEWTypes {
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
                            is_global: false,
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
                    Expr::new(ExprKind::Number(arr_i as i32), ValueKind::Rvalue),
                ),
            )
            .into_iter()
            .enumerate()
            {
                let value = if let ExprKind::Nop = list[i + offset].kind.clone() {
                    Expr::new(ExprKind::Number(0), ValueKind::Rvalue)
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
                    Expr::new(ExprKind::Number(0), ValueKind::Rvalue)
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
            is_global: false,
        },
        ValueKind::Lvalue,
    )
}

// creates a list of types for any given initializer list
mod initiliazer_list_types {
    use super::*;

    #[derive(Clone, Debug)]
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
        pub fn len(&self) -> usize {
            match self {
                Self::Single(_) => 1,
                Self::Multiple(v) => v.len(),
            }
        }
        pub fn at(&self, depth: usize, max_depth: usize) -> NEWTypes {
            let depth = depth - (max_depth - self.len());
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
                    ElementType::Multiple(result.into_iter().collect())
                }
                ElementType::Multiple(v) => {
                    let mut start = vec![ElementType::Single(type_decl.clone())];
                    for e in v[0].flatten() {
                        start.push(e)
                    }
                    let mut result = vec![ElementType::Multiple(start)];

                    for e in v.into_iter().skip(1) {
                        result.push(e);
                    }
                    let result = result.iter().cloned().cycle().take(result.len() * amount);
                    ElementType::Multiple(result.into_iter().collect())
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
                result.insert(0, ElementType::Multiple(start.into_iter().collect()));
                ElementType::Multiple(result.into_iter().collect())
            }
            _ => ElementType::Single(type_decl.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    macro_rules! token_default {
        ($token_type:expr) => {
            Token::new($token_type, 1, 1, "".to_string())
        };
    }
    macro_rules! tok_vec {
        ($($token_type:expr),+) => {{
            let mut v:Vec<Token> = Vec::new();
            $(v.push(token_default!($token_type));)+
            v
        }}
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

    #[test]
    fn creates_ast_for_expression() {
        let tokens = tok_vec![
            TokenType::Number(32),
            TokenType::Plus,
            TokenType::Number(1),
            TokenType::Star,
            TokenType::Number(2)
        ];
        let mut p = Parser::new(tokens);

        let result = p.expression();
        let expected = Expr::new(
            ExprKind::Binary {
                left: Box::new(Expr::new(ExprKind::Number(32), ValueKind::Rvalue)),
                token: token_default!(TokenType::Plus),
                right: Box::new(Expr::new(
                    ExprKind::Binary {
                        left: Box::new(Expr::new(ExprKind::Number(1), ValueKind::Rvalue)),
                        token: token_default!(TokenType::Star),
                        right: Box::new(Expr::new(ExprKind::Number(2), ValueKind::Rvalue)),
                    },
                    ValueKind::Rvalue,
                )),
            },
            ValueKind::Rvalue,
        );
        assert_eq!(result.unwrap(), expected);
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
    fn nested_groupings() {
        let tokens = tok_vec![
            TokenType::LeftParen,
            TokenType::Number(3),
            TokenType::Slash,
            TokenType::LeftParen,
            TokenType::Number(6),
            TokenType::Minus,
            TokenType::Number(7),
            TokenType::RightParen,
            TokenType::Star,
            TokenType::Number(2),
            TokenType::RightParen,
            TokenType::Plus,
            TokenType::Number(1)
        ];
        let mut p = Parser::new(tokens);

        let result = p.expression();
        let expected = Expr::new(
            ExprKind::Binary {
                left: Box::new(Expr::new(
                    ExprKind::Grouping {
                        expr: Box::new(Expr::new(
                            ExprKind::Binary {
                                left: Box::new(Expr::new(
                                    ExprKind::Binary {
                                        left: Box::new(Expr::new(
                                            ExprKind::Number(3),
                                            ValueKind::Rvalue,
                                        )),
                                        token: token_default!(TokenType::Slash),
                                        right: Box::new(Expr::new(
                                            ExprKind::Grouping {
                                                expr: Box::new(Expr::new(
                                                    ExprKind::Binary {
                                                        left: Box::new(Expr::new(
                                                            ExprKind::Number(6),
                                                            ValueKind::Rvalue,
                                                        )),
                                                        token: token_default!(TokenType::Minus),
                                                        right: Box::new(Expr::new(
                                                            ExprKind::Number(7),
                                                            ValueKind::Rvalue,
                                                        )),
                                                    },
                                                    ValueKind::Rvalue,
                                                )),
                                            },
                                            ValueKind::Rvalue,
                                        )),
                                    },
                                    ValueKind::Rvalue,
                                )),
                                token: token_default!(TokenType::Star),
                                right: Box::new(Expr::new(ExprKind::Number(2), ValueKind::Rvalue)),
                            },
                            ValueKind::Rvalue,
                        )),
                    },
                    ValueKind::Rvalue,
                )),
                token: token_default!(TokenType::Plus),
                right: Box::new(Expr::new(ExprKind::Number(1), ValueKind::Rvalue)),
            },
            ValueKind::Rvalue,
        );

        assert_eq!(result.unwrap(), expected);
    }
}
