use crate::parser::Expr;
use crate::token::TokenType;
use crate::token::Tokens;
use std::collections::HashMap;

pub enum Stmt {
    Print(Expr),
    Expr(Expr),
    DeclareVar(String),
    InitVar(String, Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Box<Option<Stmt>>),
}

#[derive(Clone)]
struct Environment {
    current: HashMap<String, i32>,
    enclosing: Option<Box<Environment>>,
}
impl Environment {
    pub fn new(enclosing: Option<Box<Environment>>) -> Self {
        Environment {
            current: HashMap::new(),
            enclosing,
        }
    }
    fn create_var(&mut self, var_name: String) {
        self.current.insert(var_name, -1);
    }
    fn get_var(&self, name: String) -> i32 {
        match self.current.get(&name) {
            Some(v) => *v,
            None => match &self.enclosing {
                Some(env) => (**env).get_var(name),
                None => panic!("undeclared var {}", name),
            },
        }
    }
    fn assign_var(&mut self, name: String, value: i32) -> i32 {
        match self.current.contains_key(&name) {
            true => {
                self.current.insert(name, value);
                return value;
            }
            false => match &mut self.enclosing {
                Some(env) => (*env).assign_var(name, value),
                None => panic!("undeclared var {}", name),
            },
        }
    }
    fn init_var(&mut self, var_name: String, value: i32) {
        self.current.insert(var_name, value);
    }
}

pub struct Interpreter {
    env: Environment,
}
impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(None),
        }
    }
    fn visit_print_stmt(&mut self, expr: Expr) {
        let value = self.execute(expr.clone());
        println!("{}", value);
    }
    fn if_statement(&mut self, cond: Expr, then_branch: Stmt, else_branch: Option<Stmt>) {
        if self.execute(cond) == 1 {
            self.visit(then_branch);
        } else if let Some(_) = else_branch {
            self.visit(else_branch.unwrap());
        }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) {
        for s in statements {
            self.visit(s);
        }
    }
    fn visit(&mut self, statement: Stmt) {
        match statement {
            Stmt::Print(expr) => self.visit_print_stmt(expr),
            Stmt::DeclareVar(name) => self.env.create_var(name.clone()),
            Stmt::InitVar(name, expr) => {
                let value = self.execute(expr);
                self.env.init_var(name.clone(), value)
            }
            Stmt::Expr(expr) => {
                self.execute(expr.clone());
                ()
            }
            Stmt::Block(statements) => {
                self.execute_block(
                    statements,
                    Environment::new(Some(Box::new(self.env.clone()))),
                );
                ()
            }
            Stmt::If(cond, then_branch, else_branch) => {
                self.if_statement(cond, *then_branch, *else_branch)
            }
        }
    }

    fn execute_block(&mut self, statements: Vec<Stmt>, env: Environment) {
        self.env = env;
        self.interpret(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env = *(self.env.enclosing.as_ref().unwrap().clone());
    }

    fn execute(&mut self, ast: Expr) -> i32 {
        match ast {
            Expr::Binary { left, token, right } => self.evaluate_binary(*left, token, *right),
            Expr::Unary { token, right } => self.evaluate_unary(token, *right),
            Expr::Grouping { expr } => self.evaluate_grouping(*expr),
            Expr::Number(v) => return v,
            Expr::Ident(v) => return self.env.get_var(v),
            Expr::Assign { name, expr } => {
                let value = self.execute(*expr);
                self.env.assign_var(name, value)
            }
            Expr::Logical { left, token, right } => self.evaluate_logical(*left, token, *right),
            _ => panic!("cant interpret this expression"),
        }
    }
    fn evaluate_logical(&mut self, left: Expr, token: Tokens, right: Expr) -> i32 {
        let left = self.execute(left);

        match token.token {
            TokenType::PipePipe => {
                if left != 0 {
                    return left;
                }
            }
            TokenType::AmpAmp => {
                if left == 0 {
                    return left;
                }
            }
            _ => unreachable!(),
        }
        self.execute(right)
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
