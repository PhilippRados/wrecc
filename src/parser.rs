use crate::interpreter::Stmt;
use crate::scanner::Error;
use crate::scanner::TokenType;
use crate::scanner::Tokens;
use std::iter::Peekable;

macro_rules! if_match_return {
    ($self:ident,$var:expr,$default:expr) => {
        let variant = $var($default);
        match $self.matches(vec![variant]) {
            Some(t) => match t.token {
                TokenType::Number(n) => return Ok(Expr::Number(n)),
                TokenType::String(s) => return Ok(Expr::String(s.clone())),
                _ => unreachable!(),
            },
            None => (),
        }
    };
}

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
        expression: Box<Expr>,
    },
    Number(i32),
    String(String),
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
            match self.statement() {
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
    fn statement(&mut self) -> Result<Stmt, Error> {
        match self.tokens.next() {
            Some(t) => match t.token {
                TokenType::Print => self.print_statement(),
                // TokenType::Int => self.var_declaration(),
                _ => panic!("only expression not allowed {:?}", t), //self.expression_statement(),
            },
            None => unreachable!(),
        }
    }
    fn print_statement(&mut self) -> Result<Stmt, Error> {
        let value = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(Stmt::Print(value))
    }
    // fn var_declaration(&mut self) -> Result<Stmt, Error> {
    // let value = self.expression()?;
    // self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
    // Ok(Stmt::Print(value))
    // }

    fn expression(&mut self) -> Result<Expr, Error> {
        self.equality()
    }
    fn equality(&mut self) -> Result<Expr, Error> {
        let mut expr = self.comparison()?;

        match self.matches(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
            Some(token) => {
                let operator = token;
                let right = self.equality()?;
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        Ok(expr)
    }
    fn comparison(&mut self) -> Result<Expr, Error> {
        let mut expr = self.term()?;

        match self.matches(vec![
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            Some(token) => {
                let operator = token;
                let right = self.term()?;
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        Ok(expr)
    }
    fn term(&mut self) -> Result<Expr, Error> {
        let mut expr = self.factor()?;

        match self.matches(vec![TokenType::Minus, TokenType::Plus]) {
            Some(token) => {
                let operator = token;
                let right = self.factor()?;
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        Ok(expr)
    }
    fn factor(&mut self) -> Result<Expr, Error> {
        let mut expr = self.unary()?;

        match self.matches(vec![TokenType::Slash, TokenType::Star]) {
            Some(token) => {
                let operator = token;
                let right = self.unary()?;
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        Ok(expr)
    }
    fn unary(&mut self) -> Result<Expr, Error> {
        match self.matches(vec![TokenType::Bang, TokenType::Minus]) {
            Some(token) => {
                let operator = token;
                let right = self.unary()?;
                return Ok(Expr::Unary {
                    token: operator,
                    right: Box::new(right),
                });
            }
            None => (),
        }
        self.primary()
    }
    fn primary(&mut self) -> Result<Expr, Error> {
        if_match_return!(self, TokenType::Number, 0);
        if_match_return!(self, TokenType::String, "".to_string());

        match self.matches(vec![TokenType::LeftParen]) {
            Some(t) => {
                let expr = self.expression()?;
                self.consume(TokenType::RightParen, "missing closing ')'")?;
                return Ok(Expr::Grouping {
                    expression: Box::new(expr),
                });
            }
            None => (),
        }
        match self.tokens.peek() {
            Some(t) => {
                return Err(Error::new(
                    t,
                    &format!("Expected expression found: {:?}", t.token),
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
    fn consume(&mut self, token: TokenType, msg: &str) -> Result<(), Error> {
        match self.tokens.next() {
            Some(v) => {
                if v.token != token {
                    return Err(Error::new(&v, msg));
                } else {
                    return Ok(());
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

    fn matches(&mut self, expected: Vec<TokenType>) -> Option<Tokens> {
        match self.tokens.peek() {
            Some(v) => {
                if !expected.contains(&v.token) {
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

        let result = p.matches(vec![
            TokenType::Number(0),
            TokenType::String("".to_string()),
        ]);
        let expected = Some(token_default!(TokenType::Number(2)));
        assert_eq!(result, expected);
    }
}
