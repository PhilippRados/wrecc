use crate::environment::*;
use crate::error::Error;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;
use crate::types::Types;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Token, Expr),
    Expr(Expr),
    DeclareVar(Token, Token),
    InitVar(Token, Token, Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Expr, Box<Stmt>),
    Function(Token, Token, Vec<(Token, Token)>, Vec<Stmt>),
    Return(Token, Option<Expr>),
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
    fn print_statement(&mut self, token: &Token, expr: &Expr) {
        let value = self.execute(expr);
        match value {
            Types::Int(n) => println!("{n}"),
            Types::Char(c) => {
                if c < 0 {
                    Error::new(token, "cant print negative char").print_exit();
                } else {
                    println!("{}", c as u8 as char);
                }
            }
            Types::Void => Error::new(token, "Can't print void expression").print_exit(),
        }
    }
    fn if_statement(
        &mut self,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Stmt>,
    ) -> Result<(), Option<Types>> {
        if self.execute(cond).unwrap_num() != 0 {
            self.visit(then_branch)?;
        } else if let Some(stmt) = else_branch {
            self.visit(stmt)?;
        }
        Ok(())
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), Option<Types>> {
        while self.execute(cond).unwrap_num() != 0 {
            self.visit(body)?;
        }
        Ok(())
    }

    pub fn interpret(&mut self, statements: &Vec<Stmt>) -> Result<(), Option<Types>> {
        for s in statements {
            self.visit(s)?;
        }
        Ok(())
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), Option<Types>> {
        match statement {
            Stmt::Print(token, expr) => Ok(self.print_statement(token, expr)),
            Stmt::DeclareVar(type_decl, name) => Ok(self.env.declare_var(name)),
            Stmt::InitVar(type_decl, name, expr) => {
                let value = self.execute(expr);
                Ok(self.env.init_var(type_decl, name, value))
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
            Stmt::Function(return_type, name, params, body) => {
                Ok(self.function_definition(name, params, body))
            }
            Stmt::Return(keyword, value) => Err(self.return_statement(keyword, value)),
        }
    }
    fn return_statement(&mut self, keyword: &Token, value: &Option<Expr>) -> Option<Types> {
        if self.env.enclosing == None {
            Error::new(keyword, "can't define return in global scope").print_exit();
        }
        match value {
            Some(v) => Some(self.execute(v)),
            None => None,
        }
    }
    fn function_definition(
        &mut self,
        name: &Token,
        params: &Vec<(Token, Token)>,
        body: &Vec<Stmt>,
    ) {
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
    ) -> Result<(), Option<Types>> {
        self.env = env;
        let result = self.interpret(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env = *self.env.enclosing.as_ref().unwrap().clone(); // TODO: remove as_ref and clone
        result
    }

    fn execute(&mut self, ast: &Expr) -> Types {
        match ast {
            Expr::Binary { left, token, right } => {
                Types::Int(self.evaluate_binary(left, token, right))
            }
            Expr::Unary { token, right } => Types::Int(self.evaluate_unary(token, right)),
            Expr::Grouping { expr } => self.evaluate_grouping(expr),
            Expr::Number(v) => return Types::Int(*v),
            Expr::CharLit(c) => return Types::Char(*c),
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
        }
    }
    fn evaluate_call(&mut self, left_paren: &Token, callee: &Expr, args: &Vec<Expr>) -> Types {
        let func_name = match callee {
            Expr::Ident(func_name) => func_name,
            _ => Error::new(left_paren, "function-name has to be identifier").print_exit(),
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
                    .print_exit()
                }
            }
            None => Error::new(
                left_paren,
                &format!("no function {} exists", func_name.unwrap_string()),
            )
            .print_exit(),
        }
    }
    fn evaluate_logical(&mut self, left: &Box<Expr>, token: &Token, right: &Box<Expr>) -> Types {
        let left = self.execute(left);

        match token.token {
            TokenType::PipePipe => {
                if left.unwrap_num() != 0 {
                    return left;
                }
            }
            TokenType::AmpAmp => {
                if left.unwrap_num() == 0 {
                    return left;
                }
            }
            _ => unreachable!(),
        }
        self.execute(right)
    }
    fn evaluate_binary(&mut self, left: &Box<Expr>, token: &Token, right: &Box<Expr>) -> i32 {
        let left = self.execute(left).unwrap_num();
        let right = self.execute(right).unwrap_num();

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
            _ => Error::new(token, "invalid binary operator").print_exit(),
        }
    }
    fn evaluate_unary(&mut self, token: &Token, right: &Box<Expr>) -> i32 {
        let right = self.execute(right).unwrap_num();
        match token.token {
            TokenType::Bang => {
                if right == 0 {
                    1
                } else {
                    0
                }
            }
            TokenType::Minus => -right,
            _ => Error::new(token, "invalid unary operator").print_exit(),
        }
    }
    fn evaluate_grouping(&mut self, expr: &Box<Expr>) -> Types {
        self.execute(expr)
    }
}
