use crate::interpreter::Stmt;
use crate::scanner::Error;
use crate::token::TokenKind;
use crate::token::TokenType;
use crate::token::Tokens;
use std::iter::Peekable;

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Binary {
        left: Box<Expr>,
        token: Tokens,
        right: Box<Expr>,
    },
    Unary {
        token: Tokens,
        right: Box<Expr>,
    },
    Grouping {
        expr: Box<Expr>,
    },
    Assign {
        name: String,
        expr: Box<Expr>,
    },
    Number(i32),
    String(String),
    Ident(String),
}

pub struct Parser {
    tokens: Peekable<std::vec::IntoIter<Tokens>>,
}

impl Parser {
    pub fn new(tokens: Vec<Tokens>) -> Self {
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
                    | TokenType::Print
                    | TokenType::While
                    | TokenType::For
                    | TokenType::Int => return,
                    _ => (),
                }
            }
            prev = Some(v.clone());
            self.tokens.next();
        }
    }
    fn declaration(&mut self) -> Result<Stmt, Error> {
        if let Some(_) = self.matches(vec![TokenKind::Int]) {
            return self.int_declaration();
        }
        self.statement()
    }
    fn statement(&mut self) -> Result<Stmt, Error> {
        if let Some(_) = self.matches(vec![TokenKind::Print]) {
            return self.print_statement();
        }
        if let Some(_) = self.matches(vec![TokenKind::LeftBrace]) {
            return Ok(Stmt::Block(self.block()?));
        }
        self.expression_statement()
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
    fn print_statement(&mut self) -> Result<Stmt, Error> {
        let value = self.expression()?;
        self.consume(TokenKind::Semicolon, "Expect ';' after value.")?;
        Ok(Stmt::Print(value))
    }
    fn int_declaration(&mut self) -> Result<Stmt, Error> {
        let name = self
            .consume(
                TokenKind::Ident,
                "Expect identifier following int declaration",
            )?
            .unwrap_string();

        if let Some(_) = self.matches(vec![TokenKind::Equal]) {
            let value = self.expression()?;
            self.consume(TokenKind::Semicolon, "Expect ';' after expression")?;
            Ok(Stmt::InitVar(name, value))
        } else {
            self.consume(TokenKind::Semicolon, "Expect ';' after int declaration")?;
            Ok(Stmt::DeclareVar(name))
        }
    }

    fn expression(&mut self) -> Result<Expr, Error> {
        self.int_assignment()
    }
    fn int_assignment(&mut self) -> Result<Expr, Error> {
        let expr = self.equality()?;

        if let Some(_) = self.matches(vec![TokenKind::Equal]) {
            let value = self.expression()?;
            match expr {
                Expr::Ident(name) => {
                    return Ok(Expr::Assign {
                        name,
                        expr: Box::new(value),
                    });
                }
                _ => {
                    let t = self.tokens.peek().unwrap();
                    return Err(Error::new(t, &format!("cant assign to {:?}", t)));
                }
            }
        }
        Ok(expr)
    }
    fn equality(&mut self) -> Result<Expr, Error> {
        let mut expr = self.comparison()?;

        while let Some(token) = self.matches(vec![TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = token;
            let right = self.comparison()?;
            expr = Expr::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            }
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
            expr = Expr::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn term(&mut self) -> Result<Expr, Error> {
        let mut expr = self.factor()?;

        while let Some(token) = self.matches(vec![TokenKind::Minus, TokenKind::Plus]) {
            let operator = token;
            let right = self.factor()?;
            expr = Expr::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn factor(&mut self) -> Result<Expr, Error> {
        let mut expr = self.unary()?;

        while let Some(token) = self.matches(vec![TokenKind::Slash, TokenKind::Star]) {
            let operator = token;
            let right = self.unary()?;
            expr = Expr::Binary {
                left: Box::new(expr),
                token: operator,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }
    fn unary(&mut self) -> Result<Expr, Error> {
        if let Some(token) = self.matches(vec![TokenKind::Bang, TokenKind::Minus]) {
            let operator = token;
            let right = self.unary()?;
            return Ok(Expr::Unary {
                token: operator,
                right: Box::new(right),
            });
        }
        self.primary()
    }
    fn primary(&mut self) -> Result<Expr, Error> {
        //TODO: avoid repition
        if let Some(n) = self.matches(vec![TokenKind::Number]) {
            return Ok(Expr::Number(n.unwrap_num()));
        }
        if let Some(s) = self.matches(vec![TokenKind::String]) {
            return Ok(Expr::String(s.unwrap_string()));
        }
        if let Some(s) = self.matches(vec![TokenKind::Ident]) {
            return Ok(Expr::Ident(s.unwrap_string()));
        }

        if let Some(_) = self.matches(vec![TokenKind::LeftParen]) {
            let expr = self.expression()?;
            self.consume(TokenKind::RightParen, "missing closing ')'")?;
            return Ok(Expr::Grouping {
                expr: Box::new(expr),
            });
        }
        match self.tokens.peek() {
            Some(t) => {
                return Err(Error::new(
                    t,
                    &format!("Expected expression found: {}", t.token),
                ));
            }
            None => {
                return Err(Error {
                    line_index: -1,
                    line_string: "".to_string(),
                    column: -1,
                    msg: "Expected expression found end of file".to_string(),
                })
            }
        };
    }
    fn consume(&mut self, token: TokenKind, msg: &str) -> Result<Tokens, Error> {
        match self.tokens.next() {
            Some(v) => {
                if TokenKind::from(&v.token) != token {
                    return Err(Error::new(&v, msg));
                } else {
                    return Ok(v);
                }
            }
            None => {
                return Err(Error {
                    line_index: -1,
                    line_string: "".to_string(),
                    column: -1,
                    msg: msg.to_string(),
                })
            }
        }
    }

    // TODO: dont need vec when only matching single enum
    fn matches(&mut self, expected: Vec<TokenKind>) -> Option<Tokens> {
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
}

#[cfg(test)]
mod tests {
    //TODO: clean up tests
    use super::*;
    macro_rules! token_default {
        ($token_type:expr) => {
            Tokens::new($token_type, 1, 1, "".to_string())
        };
    }
    macro_rules! tok_vec {
        ($($token_type:expr),+) => {{
            let mut v:Vec<Tokens> = Vec::new();
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
        let expected = Expr::Binary {
            left: Box::new(Expr::Number(32)),
            token: token_default!(TokenType::Plus),
            right: Box::new(Expr::Binary {
                left: Box::new(Expr::Number(1)),
                token: token_default!(TokenType::Star),
                right: Box::new(Expr::Number(2)),
            }),
        };
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
        let expected = Expr::Binary {
            left: Box::new(Expr::Grouping {
                expr: Box::new(Expr::Binary {
                    left: Box::new(Expr::Binary {
                        left: Box::new(Expr::Number(3)),
                        token: token_default!(TokenType::Slash),
                        right: Box::new(Expr::Grouping {
                            expr: Box::new(Expr::Binary {
                                left: Box::new(Expr::Number(6)),
                                token: token_default!(TokenType::Minus),
                                right: Box::new(Expr::Number(7)),
                            }),
                        }),
                    }),
                    token: token_default!(TokenType::Star),
                    right: Box::new(Expr::Number(2)),
                }),
            }),
            token: token_default!(TokenType::Plus),
            right: Box::new(Expr::Number(1)),
        };

        assert_eq!(result.unwrap(), expected);
    }
}
