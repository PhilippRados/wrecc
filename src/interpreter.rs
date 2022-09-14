use crate::parser::Expr;
use crate::token::TokenType;
use crate::token::Tokens;
use std::collections::HashMap;

pub enum Stmt {
    Print(Expr),
    Expr(Expr),
    DeclareVar(String),
    InitVar(String, Expr),
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
    fn visit_print_stmt(&mut self, expr: Expr) {
        let value = self.execute(expr.clone());
        println!("{}", value);
    }
    fn create_var(&mut self, var_name: String) {
        self.env.insert(var_name, -1);
    }
    fn assign_var(&mut self, var_name: String, expr: Expr) -> i32 {
        if self.env.get(&var_name) == None {
            panic!("can't find variable {}", var_name);
        }
        let value = self.execute(expr);
        self.env.insert(var_name, value);
        value
    }
    fn init_var(&mut self, var_name: String, expr: Expr) {
        let value = self.execute(expr);
        self.env.insert(var_name, value);
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) {
        for s in statements {
            self.visit(s);
        }
    }
    fn visit(&mut self, statement: Stmt) {
        match statement {
            Stmt::Print(expr) => self.visit_print_stmt(expr),
            Stmt::DeclareVar(name) => self.create_var(name.clone()),
            Stmt::InitVar(name, expr) => self.init_var(name.clone(), expr),
            // Stmt::AssignVar(name, expr) => self.assign_var(name.clone(), expr),
            Stmt::Expr(expr) => {
                self.execute(expr.clone());
                ()
            }
        }
    }

    fn execute(&mut self, ast: Expr) -> i32 {
        match ast {
            Expr::Binary {
                left: l,
                token: t,
                right: r,
            } => self.evaluate_binary(*l, t, *r),
            Expr::Unary { token: t, right: r } => self.evaluate_unary(t, *r),
            Expr::Grouping { expr: e } => self.evaluate_grouping(*e),
            Expr::Number(v) => return v,
            Expr::Ident(v) => return *self.env.get(&v).unwrap(),
            Expr::Assign { name, expr } => self.assign_var(name, *expr),
            _ => panic!("cant interpret this expression"),
        }
    }
    fn evaluate_binary(&mut self, left: Expr, token: Tokens, right: Expr) -> i32 {
        let left = self.execute(left);
        let right = self.execute(right);

        match token.token {
            TokenType::Plus => left + right,
            TokenType::Minus => left - right,
            TokenType::Star => left * right,
            TokenType::Slash => left / right,
            TokenType::EqualEqual => {
                if left == right {
                    1
                } else {
                    0
                }
            }
            TokenType::BangEqual => {
                if left != right {
                    1
                } else {
                    0
                }
            }
            TokenType::Greater => {
                if left > right {
                    1
                } else {
                    0
                }
            }
            TokenType::GreaterEqual => {
                if left >= right {
                    1
                } else {
                    0
                }
            }

            TokenType::Less => {
                if left < right {
                    1
                } else {
                    0
                }
            }
            TokenType::LessEqual => {
                if left <= right {
                    1
                } else {
                    0
                }
            }
            _ => panic!("invalid binary operator {}", token.token),
        }
    }
    fn evaluate_unary(&mut self, token: Tokens, right: Expr) -> i32 {
        let right = self.execute(right);
        match token.token {
            TokenType::Bang => !right,
            TokenType::Minus => -right,
            _ => panic!("invalid unary token {}", token.token),
        }
    }
    fn evaluate_grouping(&mut self, expr: Expr) -> i32 {
        self.execute(expr)
    }
}
