use std::fs;
use std::iter::Peekable;

mod scanner;
use scanner::Tokens;
use scanner::*;

fn sys_error(msg: &str, exit_code: i32) {
    eprintln!("rucc: {msg}");
    std::process::exit(exit_code);
}

#[derive(Debug, PartialEq, Clone)]
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
    tokens: Peekable<std::vec::IntoIter<Tokens>>,
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

        match self.matches(vec![TokenType::BangEqual, TokenType::EqualEqual]) {
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
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
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

        match self.matches(vec![TokenType::Minus, TokenType::Plus]) {
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

        match self.matches(vec![TokenType::Slash, TokenType::Star]) {
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
        match self.matches(vec![TokenType::Bang, TokenType::Minus]) {
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
        if let Some(token) = self.tokens.next() {
            match token.token {
                TokenType::Number(v) => return Expr::Number(v),
                TokenType::String(v) => return Expr::String(v),
                TokenType::LeftParen => {
                    let expr = self.expression();
                    match self.matches(vec![TokenType::RightParen]) {
                        Some(_) => (),
                        None => panic!("missing closing ')'"),
                    }
                    return Expr::Grouping {
                        expression: Box::new(expr),
                    };
                }
                _ => panic!("Expected expression found: {:?}", token.line_string),
            }
        }
        unreachable!()
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

fn execute(ast: Expr) -> i32 {
    match ast {
        Expr::Binary {
            left: l,
            token: t,
            right: r,
        } => evaluate_binary(*l, t, *r),
        Expr::Unary { token: t, right: r } => evaluate_unary(t, *r),
        Expr::Grouping { expression: e } => evaluate_grouping(*e),
        Expr::Number(v) => return v,
        // Expr::String(v) => return v,
        _ => panic!("cant interpret this token"),
    }
}
fn evaluate_binary(left: Expr, token: Tokens, right: Expr) -> i32 {
    let left = execute(left);
    let right = execute(right);

    match token.token {
        TokenType::Plus => left + right,
        TokenType::Minus => left - right,
        TokenType::Star => left * right,
        TokenType::Slash => left / right,
        _ => panic!("invalid binary operator"),
    }
}
fn evaluate_unary(token: Tokens, right: Expr) -> i32 {
    let right = execute(right);
    match token.token {
        TokenType::Bang => !right,
        TokenType::Minus => -right,
        _ => panic!("invalid unary token"),
    }
}
fn evaluate_grouping(expr: Expr) -> i32 {
    execute(expr)
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
    let mut scanner = Scanner::new(&source);
    match scanner.scan_token() {
        Ok(v) => tokens = Some(v),
        Err(e) => {
            for err in e {
                err.print_error();
            }
            had_error = true;
        }
    }

    if had_error {
        return;
    }
    let mut parser = Parser::new(tokens.unwrap());
    let ast = parser.expression();

    if had_error {
        return;
    }
    println!("{}", execute(ast));
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
    fn creates_ast() {
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
        assert_eq!(result, expected);
    }
}
