use crate::environment::*;
use crate::error::Error;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;
use crate::types::TypeValues;
use crate::types::Types;

#[derive(PartialEq, Clone)]
pub enum Stmt {
    Print(Token, Expr),
    Expr(Expr),
    DeclareVar(Types, Token),
    InitVar(Types, Token, Expr),
    Block(Vec<Stmt>),
    If(Token, Expr, Box<Stmt>, Box<Option<Stmt>>),
    While(Expr, Box<Stmt>),
    Function(Types, Token, Vec<(Types, Token)>, Vec<Stmt>),
    Return(Token, Option<Expr>),
}
// pub struct Interpreter {
//     pub env: Environment<TypeValues>,
//     pub global: Environment<TypeValues>,
// }
// impl Interpreter {
//     pub fn new() -> Self {
//         Interpreter {
//             env: Environment::new(None),
//             global: Environment::new(None),
//         }
//     }
//     fn print_statement(&mut self, token: &Token, expr: &Expr) {
//         let value = self.execute(expr);
//         match value {
//             TypeValues::Int(n) => println!("{n}"),
//             TypeValues::Char(c) => {
//                 if c < 0 {
//                     Error::new(token, "cant print negative char").print_exit();
//                 } else {
//                     println!("{}", c as u8 as char);
//                 }
//             }
//             TypeValues::Void => unreachable!("typechecker"),
//         }
//     }
//     fn if_statement(
//         &mut self,
//         cond: &Expr,
//         then_branch: &Stmt,
//         else_branch: &Option<Stmt>,
//     ) -> Result<(), Option<TypeValues>> {
//         if self.execute(cond).unwrap_as_int() != 0 {
//             self.visit(then_branch)?;
//         } else if let Some(stmt) = else_branch {
//             self.visit(stmt)?;
//         }
//         Ok(())
//     }
//     fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), Option<TypeValues>> {
//         while self.execute(cond).unwrap_as_int() != 0 {
//             self.visit(body)?;
//         }
//         Ok(())
//     }

//     pub fn interpret(&mut self, statements: &Vec<Stmt>) -> Result<(), Option<TypeValues>> {
//         for s in statements {
//             self.visit(s)?;
//         }
//         Ok(())
//     }
//     fn visit(&mut self, statement: &Stmt) -> Result<(), Option<TypeValues>> {
//         match statement {
//             Stmt::Print(token, expr) => Ok(self.print_statement(token, expr)),
//             Stmt::DeclareVar(type_decl, name) => Ok(self
//                 .env
//                 .declare_var(TypeValues::from(type_decl, -1), name.unwrap_string())),
//             Stmt::InitVar(type_decl, name, expr) => {
//                 let value = self.execute(expr);
//                 self.env
//                     .init_var(
//                         name.unwrap_string(),
//                         match type_decl {
//                             Types::Int => TypeValues::Int(value.unwrap_as_int()),
//                             Types::Char => TypeValues::Char(value.unwrap_as_int() as i8),
//                             Types::Void => unreachable!("typechecker"),
//                         },
//                     )
//                     .unwrap();
//                 Ok(())
//             }
//             Stmt::Expr(expr) => {
//                 self.execute(expr);
//                 Ok(())
//             }
//             Stmt::Block(statements) => self.execute_block(
//                 statements,
//                 Environment::new(Some(Box::new(self.env.clone()))),
//             ),
//             Stmt::If(_, cond, then_branch, else_branch) => {
//                 self.if_statement(cond, then_branch, else_branch)
//             }
//             Stmt::While(cond, body) => self.while_statement(cond, body),
//             Stmt::Function(return_type, name, params, body) => {
//                 Ok(self.function_definition(return_type, name, params, body))
//             }
//             Stmt::Return(_, expr) => Err(self.return_statement(expr)),
//         }
//     }
//     fn return_statement(&mut self, value: &Option<Expr>) -> Option<TypeValues> {
//         value.as_ref().map(|v| self.execute(v))
//     }
//     fn function_definition(
//         &mut self,
//         return_type: &Types,
//         name: &Token,
//         params: &[(Types, Token)],
//         body: &[Stmt],
//     ) {
//         self.global.current.funcs.insert(
//             name.unwrap_string(),
//             Function::new(*return_type, params.to_owned(), body.to_owned()),
//         );
//     }

//     pub fn execute_block(
//         &mut self,
//         statements: &Vec<Stmt>,
//         env: Environment<TypeValues>,
//     ) -> Result<(), Option<TypeValues>> {
//         self.env = env;
//         let result = self.interpret(statements);

//         // this means assignment to vars inside block which were declared outside
//         // of the block are still apparent after block
//         self.env = *self.env.enclosing.as_ref().unwrap().clone(); // TODO: remove as_ref and clone
//         result
//     }

//     pub fn execute(&mut self, ast: &Expr) -> TypeValues {
//         match ast {
//             Expr::Binary { left, token, right } => {
//                 TypeValues::Int(self.evaluate_binary(left, token, right))
//             }
//             Expr::Unary { token, right } => TypeValues::Int(self.evaluate_unary(token, right)),
//             Expr::Grouping { expr } => self.evaluate_grouping(expr),
//             Expr::Number(v) => TypeValues::Int(*v),
//             Expr::CharLit(c) => TypeValues::Char(*c),
//             Expr::Ident(v) => self.env.get_var(v).expect("type-checker should catch this"),
//             Expr::Assign { name, expr } => {
//                 let value = self.execute(expr);
//                 self.env
//                     .assign_var(name, value)
//                     .expect("type-checker should catch this")
//             }
//             Expr::Logical { left, token, right } => self.evaluate_logical(left, token, right),
//             Expr::Call {
//                 left_paren: _,
//                 callee,
//                 args,
//             } => self.evaluate_call(callee, args),
//         }
//     }
//     fn evaluate_call(&mut self, callee: &Expr, args: &Vec<Expr>) -> TypeValues {
//         let func_name = match callee {
//             Expr::Ident(func_name) => func_name,
//             _ => unreachable!("typechecker"),
//         };

//         let mut arg_list = Vec::new();
//         for arg in args {
//             arg_list.push(self.execute(arg));
//         }

//         self.global
//             .current
//             .funcs
//             .get(&func_name.unwrap_string())
//             .unwrap()
//             .clone()
//             .call(self, arg_list)
//     }
//     fn evaluate_logical(&mut self, left: &Expr, token: &Token, right: &Expr) -> TypeValues {
//         let left = self.execute(left);

//         match token.token {
//             TokenType::PipePipe => {
//                 if left.unwrap_as_int() != 0 {
//                     return left;
//                 }
//             }
//             TokenType::AmpAmp => {
//                 if left.unwrap_as_int() == 0 {
//                     return left;
//                 }
//             }
//             _ => unreachable!(),
//         }
//         self.execute(right)
//     }
//     fn evaluate_binary(&mut self, left: &Expr, token: &Token, right: &Expr) -> i32 {
//         let left = self.execute(left).unwrap_as_int();
//         let right = self.execute(right).unwrap_as_int();

//         match token.token {
//             TokenType::Plus => left + right,
//             TokenType::Minus => left - right,
//             TokenType::Star => left * right,
//             TokenType::Slash => left / right,
//             TokenType::EqualEqual => {
//                 if left == right {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             TokenType::BangEqual => {
//                 if left != right {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             TokenType::Greater => {
//                 if left > right {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             TokenType::GreaterEqual => {
//                 if left >= right {
//                     1
//                 } else {
//                     0
//                 }
//             }

//             TokenType::Less => {
//                 if left < right {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             TokenType::LessEqual => {
//                 if left <= right {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             _ => Error::new(token, "invalid binary operator").print_exit(),
//         }
//     }
//     fn evaluate_unary(&mut self, token: &Token, right: &Expr) -> i32 {
//         let right = self.execute(right).unwrap_as_int();
//         match token.token {
//             TokenType::Bang => {
//                 if right == 0 {
//                     1
//                 } else {
//                     0
//                 }
//             }
//             TokenType::Minus => -right,
//             _ => Error::new(token, "invalid unary operator").print_exit(),
//         }
//     }
//     fn evaluate_grouping(&mut self, expr: &Expr) -> TypeValues {
//         self.execute(expr)
//     }
// }
