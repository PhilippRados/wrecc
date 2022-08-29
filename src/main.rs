use std::fs;
use std::iter::Peekable;

mod scanner;
use scanner::Tokens;
use scanner::*;

fn sys_error(msg: &str, exit_code: i32) {
    eprintln!("rucc: {msg}");
    std::process::exit(exit_code);
}

#[derive(Debug, PartialEq)]
enum Expr {
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

struct Parser {
    tokens: Peekable<std::vec::IntoIter<scanner::Tokens>>,
}

impl Parser {
    fn new(tokens: Vec<Tokens>) -> Self {
        Parser {
            tokens: tokens.into_iter().peekable(),
        }
    }
    fn expression(&mut self) -> Expr {
        self.equality()
    }
    fn equality(&mut self) -> Expr {
        let mut expr = self.comparison();

        match self.matches(vec![Tokens::BangEqual, Tokens::EqualEqual]) {
            Some(token) => {
                let operator = token;
                let right = self.equality();
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        expr
    }
    fn comparison(&mut self) -> Expr {
        let mut expr = self.term();

        match self.matches(vec![
            Tokens::Greater,
            Tokens::GreaterEqual,
            Tokens::Less,
            Tokens::LessEqual,
        ]) {
            Some(token) => {
                let operator = token;
                let right = self.term();
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        expr
    }
    fn term(&mut self) -> Expr {
        let mut expr = self.factor();

        match self.matches(vec![Tokens::Minus, Tokens::Plus]) {
            Some(token) => {
                let operator = token;
                let right = self.factor();
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        expr
    }
    fn factor(&mut self) -> Expr {
        let mut expr = self.unary();

        match self.matches(vec![Tokens::Slash, Tokens::Star]) {
            Some(token) => {
                let operator = token;
                let right = self.unary();
                expr = Expr::Binary {
                    left: Box::new(expr),
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        expr
    }
    fn unary(&mut self) -> Expr {
        match self.matches(vec![Tokens::Bang, Tokens::Minus]) {
            Some(token) => {
                let operator = token;
                let right = self.unary();
                return Expr::Unary {
                    token: operator,
                    right: Box::new(right),
                };
            }
            None => (),
        }
        self.primary()
    }
    fn primary(&mut self) -> Expr {
        match self.tokens.next() {
            Some(v) => match v {
                Tokens::Number(v) => return Expr::Number(v),
                Tokens::String(v) => return Expr::String(v),
                _ => (),
            },
            None => (),
        }
        if let Some(_) = self.matches(vec![Tokens::LeftParen]) {
            let expr = self.expression();
            match self.matches(vec![Tokens::RightParen]) {
                Some(_) => (),
                None => eprintln!("missing closing ')'"),
            }
            return Expr::Grouping {
                expression: Box::new(expr),
            };
        }
        unreachable!()
    }

    fn matches(&mut self, expected: Vec<scanner::Tokens>) -> Option<scanner::Tokens> {
        match self.tokens.peek() {
            Some(v) => {
                if !expected.contains(v) {
                    return None;
                }
            }
            None => return None,
        }
        self.tokens.next()
    }
}

fn main() {
    let mut had_error = false;
    let args: Vec<String> = std::env::args().collect();
    let mut file: Option<&str> = None;
    match args.len() {
        2 => file = Some(&args[1]),
        _ => sys_error("usage: rucc <file>", 2),
    }
    let source = fs::read_to_string(file.unwrap()).expect("couldn't find file: {file}");

    let mut tokens: Option<Vec<Tokens>> = None;
    let mut scanner = Scanner::new(source.chars().peekable());
    match scanner.scan_token() {
        Ok(v) => tokens = Some(v),
        Err(e) => {
            for err in e {
                err.print_error("");
            }
            had_error = true;
        }
    }
    if !had_error {
        let mut parser = Parser::new(tokens.unwrap());
        let ast = parser.expression();
        dbg!(ast);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn creates_ast() {
        let tokens = vec![
            Tokens::Number(32),
            Tokens::Plus,
            Tokens::Number(1),
            Tokens::Star,
            Tokens::Number(2),
        ];
        let mut p = Parser::new(tokens);
        let result = p.expression();
        let expected = Expr::Binary {
            left: Box::new(Expr::Number(32)),
            token: Tokens::Plus,
            right: Box::new(Expr::Binary {
                left: Box::new(Expr::Number(1)),
                token: Tokens::Star,
                right: Box::new(Expr::Number(2)),
            }),
        };
        assert_eq!(result, expected);
    }
}
