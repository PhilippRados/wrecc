// use crate::environment::*;
use crate::error::Error;
use crate::interpreter::Stmt;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;
// use crate::types::TypeValues;
// use crate::types::Types;
use std::fmt::Write;
use std::fs::File;
use std::io::Write as _;

enum RegisterIndex {
    R8,
    R9,
    R10,
    R11,
}
impl RegisterIndex {
    fn index(&self) -> usize {
        match self {
            RegisterIndex::R8 => 0,
            RegisterIndex::R9 => 1,
            RegisterIndex::R10 => 2,
            RegisterIndex::R11 => 3,
        }
    }
}
impl From<usize> for RegisterIndex {
    fn from(index: usize) -> Self {
        match index {
            0 => RegisterIndex::R8,
            1 => RegisterIndex::R9,
            2 => RegisterIndex::R10,
            3 => RegisterIndex::R11,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
struct Register {
    in_use: bool,
    name: &'static str,
}
impl Register {
    fn free(&mut self) {
        self.in_use = false;
    }
}
struct ScratchRegisters {
    registers: [Register; 4],
}
impl ScratchRegisters {
    fn scratch_alloc(&mut self) -> RegisterIndex {
        for (i, r) in self.registers.iter_mut().enumerate() {
            if !r.in_use {
                r.in_use = true;
                return RegisterIndex::from(i);
            }
        }
        panic!("no free regesiter");
    }
    fn get_mut(&mut self, reg: &RegisterIndex) -> &mut Register {
        &mut self.registers[reg.index()]
    }
    fn get(&self, reg: &RegisterIndex) -> &Register {
        &self.registers[reg.index()]
    }
    fn new() -> Self {
        ScratchRegisters {
            registers: [
                Register {
                    in_use: false,
                    name: "%r8",
                },
                Register {
                    in_use: false,
                    name: "%r9",
                },
                Register {
                    in_use: false,
                    name: "%r10",
                },
                Register {
                    in_use: false,
                    name: "%r11",
                },
            ],
        }
    }
}
pub struct Compiler {
    registers: ScratchRegisters,
    output: String,
}
impl Compiler {
    pub fn new() -> Self {
        Compiler {
            output: String::new(),
            registers: ScratchRegisters::new(),
        }
    }
    fn print_statement(&mut self, expr: &Expr) -> Result<(), std::fmt::Error> {
        let reg = self.execute(expr)?;
        self.cg_printint(reg)
    }
    fn cg_printint(&mut self, reg: RegisterIndex) -> Result<(), std::fmt::Error> {
        let reg = self.registers.get_mut(&reg);

        writeln!(self.output, "\tmovq {}, %rdi\n\tcall _printint\n", reg.name)?;
        reg.free();
        Ok(())
    }
    // fn if_statement(
    //     &mut self,
    //     cond: &Expr,
    //     then_branch: &Stmt,
    //     else_branch: &Option<Stmt>,
    // ) -> Result<(), Option<TypeValues>> {
    //     if self.execute(cond).unwrap_as_int() != 0 {
    //         self.visit(then_branch)?;
    //     } else if let Some(stmt) = else_branch {
    //         self.visit(stmt)?;
    //     }
    //     Ok(())
    // }
    // fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), Option<TypeValues>> {
    //     while self.execute(cond).unwrap_as_int() != 0 {
    //         self.visit(body)?;
    //     }
    //     Ok(())
    // }
    fn preamble() -> &'static str {
        ".text\n\
         .cstring\n\
        lC0:\n\
          .string \"%d\\n\"\n\
          .text\n\
          .globl _main\n\
        \n\
        _printint:\n\
          \tpushq   %rbp\n\
          \tmovq    %rsp, %rbp\n\
        \n\
          \tsubq    $16, %rsp\n\
          \tmovq    %rdi, -4(%rbp)\n\
          \tmovq    -4(%rbp), %rax\n\
          \tmovq    %rax, %rsi\n\
          \tleaq	lC0(%rip), %rax\n\
          \tmovq	%rax, %rdi\n\
        \n\
          \tmovl    $0, %eax\n\
          \tcall    _printf\n\
          \tnop\n\
          \tleave\n\
          \tret\n\
        \n\
        _main:\n\
          \tpushq %rbp\n\
          \tmovq  %rsp,%rbp\n"
    }

    fn postamble() -> &'static str {
        "\tmovl    $0, %eax\n\
         \tpopq    %rbp\n\
         \tret"
    }

    pub fn compile(&mut self, statements: &Vec<Stmt>) {
        for s in statements {
            if let Err(e) = self.visit(s) {
                eprintln!("{:?}", e);
                return;
            }
        }
        let mut output = File::create("/Users/philipprados/documents/coding/Rust/rucc/generated.s")
            .expect("create failed");

        self.output.insert_str(0, Compiler::preamble());
        self.output.push_str(Compiler::postamble());

        output
            .write_all(self.output.as_bytes())
            .expect("write faield");
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), std::fmt::Error> {
        match statement {
            Stmt::Print(_, expr) => self.print_statement(expr),
            Stmt::Expr(expr) => {
                self.execute(expr)?;
                Ok(())
            }
            _ => unimplemented!(),
        }
    }
    //         Stmt::DeclareVar(type_decl, name) => Ok(self
    //             .env
    //             .declare_var(TypeValues::from(type_decl, -1), name.unwrap_string())),
    //         Stmt::InitVar(type_decl, name, expr) => {
    //             let value = self.execute(expr);
    //             self.env
    //                 .init_var(
    //                     name.unwrap_string(),
    //                     match type_decl {
    //                         Types::Int => TypeValues::Int(value.unwrap_as_int()),
    //                         Types::Char => TypeValues::Char(value.unwrap_as_int() as i8),
    //                         Types::Void => unreachable!("typechecker"),
    //                     },
    //                 )
    //                 .unwrap();
    //             Ok(())
    //         }
    //         Stmt::Block(statements) => self.execute_block(
    //             statements,
    //             Environment::new(Some(Box::new(self.env.clone()))),
    //         ),
    //         Stmt::If(_, cond, then_branch, else_branch) => {
    //             self.if_statement(cond, then_branch, else_branch)
    //         }
    //         Stmt::While(cond, body) => self.while_statement(cond, body),
    //         Stmt::Function(return_type, name, params, body) => {
    //             Ok(self.function_definition(return_type, name, params, body))
    //         }
    //         Stmt::Return(_, expr) => Err(self.return_statement(expr)),
    //     }
    // }
    // fn return_statement(&mut self, value: &Option<Expr>) -> Option<TypeValues> {
    //     value.as_ref().map(|v| self.execute(v))
    // }
    // fn function_definition(
    //     &mut self,
    //     return_type: &Types,
    //     name: &Token,
    //     params: &[(Types, Token)],
    //     body: &[Stmt],
    // ) {
    //     self.global.current.funcs.insert(
    //         name.unwrap_string(),
    //         Function::new(*return_type, params.to_owned(), body.to_owned()),
    //     );
    // }

    // pub fn execute_block(
    //     &mut self,
    //     statements: &Vec<Stmt>,
    //     env: Environment<TypeValues>,
    // ) -> Result<(), Option<TypeValues>> {
    //     self.env = env;
    //     let result = self.interpret(statements);

    //     // this means assignment to vars inside block which were declared outside
    //     // of the block are still apparent after block
    //     self.env = *self.env.enclosing.as_ref().unwrap().clone(); // TODO: remove as_ref and clone
    //     result
    // }

    fn cg_literal(&mut self, num: i32) -> Result<RegisterIndex, std::fmt::Error> {
        let reg = self.registers.scratch_alloc();

        writeln!(
            self.output,
            "\tmovq ${num}, {}",
            self.registers.get_mut(&reg).name
        )?;
        Ok(reg)
    }
    pub fn execute(&mut self, ast: &Expr) -> Result<RegisterIndex, std::fmt::Error> {
        match ast {
            Expr::Binary { left, token, right } => {
               self.evaluate_binary(left, token, right)
            }
            Expr::Number(v) => self.cg_literal(*v),
            Expr::Grouping { expr } => self.execute(expr),
            // Expr::Unary { token, right } => self.cg_unary(token, right),
            _ => panic!("Not implemented")
            // Expr::CharLit(c) => TypeValues::Char(*c),
            // Expr::Ident(v) => self.env.get_var(v).expect("type-checker should catch this"),
            // Expr::Assign { name, expr } => {
            //     let value = self.execute(expr);
            //     self.env
            //         .assign_var(name, value)
            //         .expect("type-checker should catch this")
            // }
            // Expr::Logical { left, token, right } => self.evaluate_logical(left, token, right),
            // Expr::Call {
            //     left_paren: _,
            //     callee,
            //     args,
            // } => self.evaluate_call(callee, args),
        }
    }
    // fn evaluate_call(&mut self, callee: &Expr, args: &Vec<Expr>) -> TypeValues {
    //     let func_name = match callee {
    //         Expr::Ident(func_name) => func_name,
    //         _ => unreachable!("typechecker"),
    //     };

    //     let mut arg_list = Vec::new();
    //     for arg in args {
    //         arg_list.push(self.execute(arg));
    //     }

    //     self.global
    //         .current
    //         .funcs
    //         .get(&func_name.unwrap_string())
    //         .unwrap()
    //         .clone()
    //         .call(self, arg_list)
    // }
    // fn evaluate_logical(&mut self, left: &Expr, token: &Token, right: &Expr) -> TypeValues {
    //     let left = self.execute(left);

    //     match token.token {
    //         TokenType::PipePipe => {
    //             if left.unwrap_as_int() != 0 {
    //                 return left;
    //             }
    //         }
    //         TokenType::AmpAmp => {
    //             if left.unwrap_as_int() == 0 {
    //                 return left;
    //             }
    //         }
    //         _ => unreachable!(),
    //     }
    //     self.execute(right)
    // }

    fn cg_add(
        &mut self,
        left: RegisterIndex,
        right: RegisterIndex,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_name = self.registers.get(&left).name;
        let right_name = self.registers.get(&right).name;

        writeln!(self.output, "\taddq {}, {}\n", left_name, right_name)?;

        self.registers.get_mut(&left).free();
        Ok(right)
    }
    fn cg_sub(
        &mut self,
        left: RegisterIndex,
        right: RegisterIndex,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_name = self.registers.get(&left).name;
        let right_name = self.registers.get(&right).name;

        writeln!(self.output, "\tsubq {}, {}\n", right_name, left_name)?;

        self.registers.get_mut(&right).free();
        Ok(left)
    }

    fn cg_mult(
        &mut self,
        left: RegisterIndex,
        right: RegisterIndex,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_name = self.registers.get(&left).name;
        let right_name = self.registers.get(&right).name;

        writeln!(self.output, "\timulq {}, {}\n", left_name, right_name)?;

        self.registers.get_mut(&left).free();
        Ok(right)
    }

    fn cg_div(
        &mut self,
        left: RegisterIndex,
        right: RegisterIndex,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_name = self.registers.get(&left).name;
        let right_name = self.registers.get(&right).name;

        writeln!(self.output, "\tmovq {}, %rax", left_name)?;
        writeln!(self.output, "\tcqo\n\tidivq {}", right_name)?; // rax / rcx => rax
        writeln!(self.output, "\tmovq %rax, {}", right_name)?; // move rax(int result) into right reg (remainder in rdx)

        self.registers.get_mut(&left).free();
        Ok(right)
    }

    fn cg_comparison(
        &mut self,
        operator: &str,
        left: RegisterIndex,
        right: RegisterIndex,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_name = self.registers.get(&left).name;
        let right_name = self.registers.get(&right).name;

        writeln!(self.output, "\tcmpq {}, {}", right_name, left_name)?;
        // write ZF to %al based on operator and zero extend %right_register with value of %al
        writeln!(
            self.output,
            "\t{operator} %al\n\tmovzbq %al, {}",
            right_name
        )?;

        self.registers.get_mut(&left).free();
        Ok(right)
    }

    // returns register-index that holds result
    fn evaluate_binary(
        &mut self,
        left: &Expr,
        token: &Token,
        right: &Expr,
    ) -> Result<RegisterIndex, std::fmt::Error> {
        let left_reg = self.execute(left)?;
        let right_reg = self.execute(right)?;

        match token.token {
            TokenType::Plus => self.cg_add(left_reg, right_reg),
            TokenType::Minus => self.cg_sub(left_reg, right_reg),
            TokenType::Star => self.cg_mult(left_reg, right_reg),
            TokenType::Slash => self.cg_div(left_reg, right_reg),
            TokenType::EqualEqual => self.cg_comparison("sete", left_reg, right_reg),
            TokenType::BangEqual => self.cg_comparison("setne", left_reg, right_reg),
            TokenType::Greater => self.cg_comparison("setg", left_reg, right_reg),
            TokenType::GreaterEqual => self.cg_comparison("setge", left_reg, right_reg),
            TokenType::Less => self.cg_comparison("setl", left_reg, right_reg),
            TokenType::LessEqual => self.cg_comparison("setle", left_reg, right_reg),
            _ => Error::new(token, "invalid binary operator").print_exit(),
        }
    }
    // fn evaluate_unary(&mut self, token: &Token, right: &Expr) -> i32 {
    //     let right = self.execute(right).unwrap_as_int();
    //     match token.token {
    //         TokenType::Bang => {
    //             if right == 0 {
    //                 1
    //             } else {
    //                 0
    //             }
    //         }
    //         TokenType::Minus => -right,
    //         _ => Error::new(token, "invalid unary operator").print_exit(),
    //     }
    // }
    // fn evaluate_grouping(&mut self, expr: &Expr) -> TypeValues {
    //     self.execute(expr)
    // }
}