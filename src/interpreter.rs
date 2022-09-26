use crate::environment::*;
use crate::error::Error;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Expr),
    Expr(Expr),
    DeclareVar(Token),
    InitVar(Token, Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Expr, Box<Stmt>),
    Function(Token, Vec<Token>, Vec<Stmt>),
    Return(Token, Option<Expr>),
}
pub enum ReturnValue {
    Some(i32),
    None,
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
    fn if_statement(
        &mut self,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Stmt>,
    ) -> Result<(), ReturnValue> {
        if self.execute(cond) != 0 {
            self.visit(then_branch)?;
        } else if let Some(stmt) = else_branch {
            self.visit(stmt)?;
        }
        Ok(())
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), ReturnValue> {
        while self.execute(cond) != 0 {
            self.visit(body)?;
        }
        Ok(())
    }

    pub fn interpret(&mut self, statements: &Vec<Stmt>) -> Result<(), ReturnValue> {
        for s in statements {
            self.visit(s)?;
        }
        Ok(())
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), ReturnValue> {
        match statement {
            Stmt::Print(expr) => Ok(self.print_statement(expr)),
            Stmt::DeclareVar(name) => Ok(self.env.declare_var(name)),
            Stmt::InitVar(name, expr) => {
                let value = self.execute(expr);
                Ok(self.env.init_var(name, value))
            }
            Stmt::Expr(expr) => {
                self.execute(expr);
                Ok(())
            }
            Stmt::Block(statements) => self.execute_block(
                statements,
                Environment::new(Some(Box::new(self.env.clone()))),
            ),
            Stmt::If(cond, then_branch, else_branch) => {
                self.if_statement(cond, then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(cond, body),
            Stmt::Function(name, params, body) => Ok(self.function_definition(name, params, body)),
            Stmt::Return(keyword, value) => Err(self.return_statement(keyword, value)),
        }
    }
    fn return_statement(&mut self, keyword: &Token, value: &Option<Expr>) -> ReturnValue {
        if self.env.enclosing == None {
            Error::new(keyword, "can't define return in global scope").print_exit();
        }
        match value {
            Some(v) => ReturnValue::Some(self.execute(v)),
            None => ReturnValue::None,
        }
    }
    fn function_definition(&mut self, name: &Token, params: &Vec<Token>, body: &Vec<Stmt>) {
        if self.env.enclosing == None {
            // current scope is global
            self.global.current.funcs.insert(
                name.unwrap_string(),
                Function::new(params.clone(), body.clone()),
            );
        } else {
            Error::new(name, "can only define functions in global scope").print_exit();
        }
    }

    pub fn execute_block(
        &mut self,
        statements: &Vec<Stmt>,
        env: Environment,
    ) -> Result<(), ReturnValue> {
        self.env = env;
        let result = self.interpret(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env = *self.env.enclosing.as_ref().unwrap().clone(); // TODO: remove as_ref and clone
        result
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
            Expr::Call {
                left_paren,
                callee,
                args,
            } => self.evaluate_call(left_paren, callee, args),
            _ => panic!("cant interpret this expression"),
        }
    }
    fn evaluate_call(&mut self, left_paren: &Token, callee: &Expr, args: &Vec<Expr>) -> i32 {
        let func_name = match callee {
            Expr::Ident(func_name) => func_name,
            _ => {
                Error::new(left_paren, "function-name has to be identifier").print_exit();
                unreachable!()
            }
        };

        let mut arg_list = Vec::new();
        for arg in args {
            arg_list.push(self.execute(arg));
        }

        match self.global.current.funcs.get(&func_name.unwrap_string()) {
            Some(function) => {
                if function.arity() == arg_list.len() {
                    function.clone().call(self, arg_list)
                } else {
                    Error::new(
                        left_paren,
                        &format!(
                            "Error: at '{}': expected {} argument(s) found {}",
                            func_name.unwrap_string(),
                            function.arity(),
                            arg_list.len()
                        ),
                    )
                    .print_exit();

                    unreachable!();
                }
            }
            None => {
                Error::new(
                    left_paren,
                    &format!("no function {} exists", func_name.unwrap_string()),
                )
                .print_exit();
                unreachable!();
            }
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
            _ => {
                Error::new(token, "invalid binary operator").print_exit();
                unreachable!()
            }
        }
    }
    fn evaluate_unary(&mut self, token: &Token, right: &Box<Expr>) -> i32 {
        let right = self.execute(right);
        match token.token {
            TokenType::Bang => !right,
            TokenType::Minus => -right,
            _ => {
                Error::new(token, "invalid unary operator").print_exit();
                unreachable!()
            }
        }
    }
    fn evaluate_grouping(&mut self, expr: &Box<Expr>) -> i32 {
        self.execute(expr)
    }
}
