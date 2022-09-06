use crate::parser::Expr;
use crate::scanner::TokenType;
use crate::scanner::Tokens;

pub enum Stmt {
    Print(Expr),
    Expr(Expr),
}

impl Stmt {
    fn visit(&mut self) {
        match self {
            Stmt::Print(expr) => visit_print_stmt(expr),
            // Stmt::Int_declaration(ident) =>
            Stmt::Expr(expr) => {
                execute(expr.clone());
                ()
            }
        }
    }
}
fn visit_print_stmt(expr: &Expr) {
    let value = execute(expr.clone());
    println!("{}", value);
}

pub fn interpret(statements: Vec<Stmt>) {
    for mut s in statements {
        s.visit();
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
