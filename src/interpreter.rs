use crate::parser::Expr;
use crate::scanner::TokenType;
use crate::scanner::Tokens;
use std::collections::HashMap;

pub enum Stmt {
    Print(Expr),
    Expr(Expr),
    IntVar(String),
    AssignVar(String, Expr),
}

pub struct Interpreter {
    env: HashMap<String, i32>,
}
impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: HashMap::new(),
        }
    }
    fn visit_print_stmt(&self, expr: Expr) {
        let value = self.execute(expr.clone());
        println!("{}", value);
    }
    fn create_var(&mut self, var_name: String) {
        self.env.insert(var_name, -1);
    }
    fn assign_var(&mut self, var_name: String, expr: Expr) {
        if self.env.get(&var_name) == None {
            panic!("can't find variable {}", var_name);
        }
        self.env.insert(var_name, self.execute(expr));
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) {
        for s in statements {
            self.visit(s);
        }
    }
    fn visit(&mut self, statement: Stmt) {
        match statement {
            Stmt::Print(expr) => self.visit_print_stmt(expr),
            Stmt::IntVar(name) => self.create_var(name.clone()),
            Stmt::AssignVar(name, expr) => self.assign_var(name.clone(), expr),
            Stmt::Expr(expr) => {
                self.execute(expr.clone());
                ()
            }
        }
    }

    fn execute(&self, ast: Expr) -> i32 {
        match ast {
            Expr::Binary {
                left: l,
                token: t,
                right: r,
            } => self.evaluate_binary(*l, t, *r),
            Expr::Unary { token: t, right: r } => self.evaluate_unary(t, *r),
            Expr::Grouping { expression: e } => self.evaluate_grouping(*e),
            Expr::Number(v) => return v,
            Expr::Variable(v) => return *self.env.get(&v).unwrap(),
            _ => panic!("cant interpret this token"),
        }
    }
    fn evaluate_binary(&self, left: Expr, token: Tokens, right: Expr) -> i32 {
        let left = self.execute(left);
        let right = self.execute(right);

        match token.token {
            TokenType::Plus => left + right,
            TokenType::Minus => left - right,
            TokenType::Star => left * right,
            TokenType::Slash => left / right,
            _ => panic!("invalid binary operator"),
        }
    }
    fn evaluate_unary(&self, token: Tokens, right: Expr) -> i32 {
        let right = self.execute(right);
        match token.token {
            TokenType::Bang => !right,
            TokenType::Minus => -right,
            _ => panic!("invalid unary token"),
        }
    }
    fn evaluate_grouping(&self, expr: Expr) -> i32 {
        self.execute(expr)
    }
}
