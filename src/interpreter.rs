use crate::environment::*;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Expr),
    Expr(Expr),
    DeclareVar(String),
    InitVar(String, Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Expr, Box<Stmt>),
    Function(String, Vec<String>, Vec<Stmt>),
}
pub struct Interpreter {
    pub env: Environment,
    pub global: Environment,
}
impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            env: Environment::new(None),
            global: Environment::new(None),
        }
    }
    fn print_statement(&mut self, expr: &Expr) {
        let value = self.execute(expr);
        println!("{}", value);
    }
    fn if_statement(&mut self, cond: &Expr, then_branch: &Stmt, else_branch: &Option<Stmt>) {
        if self.execute(cond) != 0 {
            self.visit(then_branch);
        } else if let Some(stmt) = else_branch {
            self.visit(stmt);
        }
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) {
        while self.execute(cond) != 0 {
            self.visit(body);
        }
    }

    pub fn interpret(&mut self, statements: &Vec<Stmt>) {
        for s in statements {
            self.visit(s);
        }
    }
    fn visit(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Print(expr) => self.print_statement(expr),
            Stmt::DeclareVar(name) => self.env.declare_var(name),
            Stmt::InitVar(name, expr) => {
                let value = self.execute(expr);
                self.env.init_var(name, value)
            }
            Stmt::Expr(expr) => {
                self.execute(expr);
            }
            Stmt::Block(statements) => {
                self.execute_block(
                    statements,
                    Environment::new(Some(Box::new(self.env.clone()))),
                );
            }
            Stmt::If(cond, then_branch, else_branch) => {
                self.if_statement(cond, then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(cond, body),
            Stmt::Function(name, params, body) => self.function_definition(name, params, body),
        }
    }
    fn function_definition(&mut self, name: &str, params: &Vec<String>, body: &Vec<Stmt>) {
        if let Some(_) = self.env.enclosing {
            eprintln!(
                "Error: at '{}' can only define functions in global scope",
                name
            );
            std::process::exit(-1);
        } else {
            self.global.current.funcs.insert(
                name.to_string(),
                Function::new(params.clone(), body.clone()),
            );
        }
    }

    pub fn execute_block(&mut self, statements: &Vec<Stmt>, env: Environment) {
        self.env = env;
        self.interpret(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env = *self.env.enclosing.as_ref().unwrap().clone(); // TODO: remove as_ref and clone
    }

    fn execute(&mut self, ast: &Expr) -> i32 {
        match ast {
            Expr::Binary { left, token, right } => self.evaluate_binary(left, token, right),
            Expr::Unary { token, right } => self.evaluate_unary(token, right),
            Expr::Grouping { expr } => self.evaluate_grouping(expr),
            Expr::Number(v) => return *v,
            Expr::Ident(v) => return self.env.get_var(v),
            Expr::Assign { name, expr } => {
                let value = self.execute(expr);
                self.env.assign_var(name, value)
            }
            Expr::Logical { left, token, right } => self.evaluate_logical(left, token, right),
            Expr::Call { callee, args } => self.evaluate_call(callee, args),
            _ => panic!("cant interpret this expression"),
        }
    }
    fn evaluate_call(&mut self, callee: &Expr, args: &Vec<Expr>) -> i32 {
        let callee = match callee {
            Expr::Ident(func_name) => func_name,
            _ => panic!("function name has to be identifier"),
        };

        let mut arg_list = Vec::new();
        for arg in args {
            arg_list.push(self.execute(arg));
        }

        match self.global.current.funcs.get(callee) {
            Some(function) => {
                function.clone().call(self, arg_list);
                0
            }
            None => panic!("no function '{}' exists", callee),
        }
    }
    fn evaluate_logical(&mut self, left: &Box<Expr>, token: &Token, right: &Box<Expr>) -> i32 {
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
    fn evaluate_binary(&mut self, left: &Box<Expr>, token: &Token, right: &Box<Expr>) -> i32 {
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
    fn evaluate_unary(&mut self, token: &Token, right: &Box<Expr>) -> i32 {
        let right = self.execute(right);
        match token.token {
            TokenType::Bang => !right,
            TokenType::Minus => -right,
            _ => panic!("invalid unary token {}", token.token),
        }
    }
    fn evaluate_grouping(&mut self, expr: &Box<Expr>) -> i32 {
        self.execute(expr)
    }
}
