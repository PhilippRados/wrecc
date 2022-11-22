use crate::common::{error::*, expr::*, stmt::*, token::*, types::*};
use std::iter::Peekable;
use std::vec::IntoIter;

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens: tokens.into_iter().peekable(),
        }
    }
    pub fn parse(&mut self) -> Option<Vec<Stmt>> {
        let mut statements: Vec<Stmt> = Vec::new();
        let mut had_error = false;

        while self.tokens.peek() != None {
            match self.declaration() {
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
                    | TokenType::Int => return,
                    _ => (),
                }
            }
            prev = self.tokens.next();
        }
    }
    fn declaration(&mut self) -> Result<Stmt, Error> {
        if let Some(t) = self.matches_type() {
            return self.type_declaration(t);
        }
        self.statement()
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
        if let Some(t) = self.matches(vec![TokenKind::LeftBrace]) {
            return Ok(Stmt::Block(t, self.block()?));
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
        if let Some(token) = self.matches_type() {
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
            body = Stmt::Block(left_paren.clone(), vec![body, Stmt::Expr(inc.unwrap())]);
        }
        if cond != None {
            body = Stmt::While(left_paren.clone(), cond.unwrap(), Box::new(body));
        } else {
            // if no condition then condition is true
            body = Stmt::While(
                left_paren.clone(),
                Expr::new(ExprKind::Number(1), ValueKind::Rvalue),
                Box::new(body),
            );
        }
        if init != None {
            body = Stmt::Block(left_paren, vec![init.unwrap(), body]);
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

        while let Some(token) = self.tokens.peek() {
            if TokenKind::from(&token.token) == TokenKind::RightBrace {
                break;
            }
            statements.push(self.declaration()?);
        }
        self.consume(TokenKind::RightBrace, "Expect '}' after Block")?;
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
    fn maybe_parse_arr(&mut self, type_decl: &mut NEWTypes) -> Result<(), Error> {
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
                type_decl.to_array(size.unwrap_num() as usize);
            } else {
                return Err(Error::new(&size, "Can't initialize array with size <= 0"));
            }
        }
        Ok(())
    }
    fn type_declaration(&mut self, mut type_decl: NEWTypes) -> Result<Stmt, Error> {
        let name = self.consume(
            TokenKind::Ident,
            "Expect identifier following type-specifier",
        )?;

        if self.matches(vec![TokenKind::LeftParen]).is_some() {
            // function
            self.function(type_decl, name)
        } else {
            // variable
            self.maybe_parse_arr(&mut type_decl)?;

            if self.matches(vec![TokenKind::Equal]).is_some() {
                let value = self.expression()?;
                self.consume(TokenKind::Semicolon, "Expect ';' after variable definition")?;
                Ok(Stmt::InitVar(type_decl, name, value))
            } else {
                self.consume(
                    TokenKind::Semicolon,
                    "Expect ';' after variable declaration",
                )?;
                Ok(Stmt::DeclareVar(type_decl, name))
            }
        }
    }
    fn function(&mut self, return_type: NEWTypes, name: Token) -> Result<Stmt, Error> {
        if matches!(return_type, NEWTypes::Array { .. }) {
            return Err(Error::new(&name, "function can't return array-type"));
        }
        let mut params = Vec::new();

        if !self.check(TokenKind::RightParen) {
            loop {
                let param_type = match self.matches_type() {
                    Some(type_decl) => type_decl,
                    None => {
                        let actual = self.tokens.peek().expect("Expected Type");
                        return Err(Error::new(
                            actual,
                            &format!("Expected type found {}", actual.token),
                        ));
                    }
                };
                params.push((
                    param_type,
                    self.consume(TokenKind::Ident, "Expect identifier after type")?,
                ));
                if self.matches(vec![TokenKind::Comma]) == None {
                    break;
                }
            }
        }
        self.consume(
            TokenKind::RightParen,
            "Expect ')' after function parameters",
        )?;

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
            if let ValueKind::Lvalue = expr.value_kind.clone() {
                return Ok(Expr::new(
                    ExprKind::Assign {
                        l_expr: Box::new(expr),
                        token: t,
                        r_expr: Box::new(value),
                    },
                    ValueKind::Rvalue,
                ));
            } else {
                return Err(Error::new(
                    &t,
                    &format!("cant assign to {}, can only assign to lvalues", expr.kind),
                ));
            }
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
        let mut expr = self.equality()?;

        while let Some(token) = self.matches(vec![TokenKind::AmpAmp]) {
            let right = self.equality()?;
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
        let mut expr = self.term()?;

        while let Some(token) = self.matches(vec![
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::Less,
            TokenKind::LessEqual,
        ]) {
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

        while let Some(token) = self.matches(vec![TokenKind::Slash, TokenKind::Star]) {
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
            TokenKind::Minus,
        ]) {
            let right = self.unary()?;
            return Ok(Expr::new(
                ExprKind::Unary {
                    right: Box::new(right),
                    token: token.clone(),
                },
                match token.token {
                    TokenType::Star => ValueKind::Lvalue,
                    TokenType::Bang | TokenType::Minus | TokenType::Amp => ValueKind::Rvalue,
                    _ => unreachable!(),
                },
            ));
        }
        self.call()
    }
    fn call(&mut self) -> Result<Expr, Error> {
        let mut expr = self.primary()?;

        while let Some(t) = self.matches(vec![TokenKind::LeftParen]) {
            expr = self.evaluate_args(t, expr)?;
        }
        Ok(expr)
    }
    fn evaluate_args(&mut self, left_paren: Token, callee: Expr) -> Result<Expr, Error> {
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
        //TODO: avoid repition
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
        match self.tokens.peek() {
            Some(t) => Err(Error::new(
                t,
                &format!("Expected expression found: {}", t.token),
            )),
            None => Err(Error {
                line_index: -1,
                line_string: "".to_string(),
                column: -1,
                msg: "Expected expression found end of file".to_string(),
            }),
        }
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
            None => Err(Error {
                line_index: -1,
                line_string: "".to_string(),
                column: -1,
                msg: msg.to_string(),
            }),
        }
    }
    fn check(&mut self, expected: TokenKind) -> bool {
        if let Some(token) = self.tokens.peek() {
            return TokenKind::from(&token.token) == expected;
        }
        false
    }

    // TODO: dont need vec when only matching single enum
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
    fn matches_type(&mut self) -> Option<NEWTypes> {
        match self.tokens.peek() {
            Some(v) => {
                if !v.is_type() {
                    return None;
                }
            }
            None => return None,
        }
        let mut type_decl = self
            .tokens
            .next()
            .expect("can only be types because of previous check")
            .into_type();

        while self.matches(vec![TokenKind::Star]).is_some() {
            type_decl.pointer_to();
        }
        Some(type_decl)
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
