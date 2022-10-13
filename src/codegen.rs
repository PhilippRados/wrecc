use crate::environment::CgEnv;
use crate::environment::Environment;
use crate::environment::Function;
use crate::error::Error;
use crate::interpreter::Stmt;
use crate::parser::Expr;
use crate::token::Token;
use crate::token::TokenType;
use crate::types::Types;
use std::fmt::Write;
use std::fs::File;
use std::io::Write as _;

enum Register {
    Scratch(ScratchIndex),
    Stack(StackRegister),
    Arg(usize),
    Void,
}
impl Register {
    fn free(&mut self, scratch_regs: &mut ScratchRegisters) {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(_) => (),
            Register::Arg(_) => (),
            Register::Scratch(index) => scratch_regs.get_mut(index).free(),
        }
    }
    fn name(&self, scratch_regs: &ScratchRegisters) -> String {
        match self {
            Register::Void => unimplemented!(),
            Register::Stack(reg) => reg.name(),
            Register::Scratch(index) => scratch_regs.get(index).name.to_string(),
            Register::Arg(index) => self.get_arg_reg(*index).to_string(),
        }
    }
    // argument registers from 1st to last
    fn get_arg_reg(&self, index: usize) -> &str {
        match index {
            0 => "%edi",
            1 => "%esi",
            2 => "%edx",
            3 => "%ecx",
            4 => "%r8d",
            5 => "%r9d",
            _ => unreachable!(),
        }
    }
}
#[derive(PartialEq, Clone)]
pub struct StackRegister {
    bp_offset: usize,
}
impl StackRegister {
    pub fn new(bp_offset: usize) -> Self {
        StackRegister { bp_offset }
    }
    fn name(&self) -> String {
        format!("-{}(%rbp)", self.bp_offset)
    }
}

#[derive(Clone)]
pub enum ScratchIndex {
    R8,
    R9,
    R10,
    R11,
}
impl ScratchIndex {
    fn index(&self) -> usize {
        match self {
            ScratchIndex::R8 => 0,
            ScratchIndex::R9 => 1,
            ScratchIndex::R10 => 2,
            ScratchIndex::R11 => 3,
        }
    }
}
impl From<usize> for ScratchIndex {
    fn from(index: usize) -> Self {
        match index {
            0 => ScratchIndex::R8,
            1 => ScratchIndex::R9,
            2 => ScratchIndex::R10,
            3 => ScratchIndex::R11,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
struct ScratchRegister {
    in_use: bool,
    name: &'static str,
}
impl ScratchRegister {
    fn free(&mut self) {
        self.in_use = false;
    }
}
struct ScratchRegisters {
    registers: [ScratchRegister; 4],
}
impl ScratchRegisters {
    fn scratch_alloc(&mut self) -> ScratchIndex {
        for (i, r) in self.registers.iter_mut().enumerate() {
            if !r.in_use {
                r.in_use = true;
                return ScratchIndex::from(i);
            }
        }
        panic!("no free regesiter");
    }
    fn get_mut(&mut self, reg: &ScratchIndex) -> &mut ScratchRegister {
        &mut self.registers[reg.index()]
    }
    fn get(&self, reg: &ScratchIndex) -> &ScratchRegister {
        &self.registers[reg.index()]
    }
    fn new() -> Self {
        ScratchRegisters {
            registers: [
                ScratchRegister {
                    in_use: false,
                    name: "%r8d",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r9d",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r10d",
                },
                ScratchRegister {
                    in_use: false,
                    name: "%r11d",
                },
            ],
        }
    }
}
pub struct Compiler {
    registers: ScratchRegisters,
    output: String,
    env: CgEnv,
    global_env: Environment<StackRegister>,
    sp_index: usize,
    decl_size: usize,
}
impl Compiler {
    pub fn new() -> Self {
        let mut global_env = Environment::new(None);
        global_env.current.funcs.insert(
            "printint".to_string(),
            Function::new(Types::Void, vec![], vec![]),
        );
        Compiler {
            output: String::new(),
            registers: ScratchRegisters::new(),
            sp_index: 0,
            decl_size: 0,
            env: CgEnv::new(),
            global_env,
        }
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
        "\t.text\n\
         \t.cstring\n\
        lC0:\n\
          \t.string \"%d\\n\"\n\
          \t.text\n\
        \n\
        _printint:\n\
          \tpushq   %rbp\n\
          \tmovq    %rsp, %rbp\n\
        \n\
          \tsubq    $16, %rsp\n\
          \tmovl    %edi, -4(%rbp)\n\
          \tmovl    -4(%rbp), %eax\n\
          \tmovl    %eax, %esi\n\
          \tleaq	lC0(%rip), %rax\n\
          \tmovq	%rax, %rdi\n\
          \taddq    $16, %rsp\n\
        \n\
          \tmovl    $0, %eax\n\
          \tcall    _printf\n\
          \tnop\n\
          \tleave\n\
          \tret\n"
    }

    fn cg_stmts(&mut self, statements: &Vec<Stmt>) -> Result<(), std::fmt::Error> {
        for s in statements {
            if let Err(e) = self.visit(s) {
                return Err(e);
            }
        }
        Ok(())
    }
    pub fn compile(&mut self, statements: &Vec<Stmt>) {
        if let Err(e) = self.cg_stmts(statements) {
            eprintln!("{:?}", e);
            return;
        }
        let mut output = File::create("/Users/philipprados/documents/coding/Rust/rucc/generated.s")
            .expect("create failed");

        self.output.insert_str(0, Compiler::preamble());

        output
            .write_all(self.output.as_bytes())
            .expect("write failed");
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), std::fmt::Error> {
        match statement {
            Stmt::Expr(expr) => {
                self.execute(expr)?;
                Ok(())
            }
            Stmt::DeclareVar(type_decl, name) => self.declare_var(type_decl, name.unwrap_string()),
            Stmt::InitVar(type_decl, name, expr) => {
                let value_reg = self.execute(expr)?;
                self.init_var(type_decl, name.unwrap_string(), value_reg)
            }
            Stmt::Block(statements) => self.block(
                statements,
                Environment::new(Some(Box::new(self.env.env.clone()))),
            ),
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(return_type, name, params, body)
            }
            // Stmt::Return(_, expr) => self.return_statement(expr), // jump to function postamble
            _ => unimplemented!(),
        }
    }
    //         Stmt::If(_, cond, then_branch, else_branch) => {
    //             self.if_statement(cond, then_branch, else_branch)
    //         }
    //         Stmt::While(cond, body) => self.while_statement(cond, body),
    //     }
    // }
    // fn return_statement(&mut self, value: &Option<Expr>) -> Option<TypeValues> {
    //     value.as_ref().map(|v| self.execute(v))
    // }
    fn increment_sp(&mut self) -> Result<(), std::fmt::Error> {
        if self.decl_size > self.sp_index {
            self.sp_index += 16;
            writeln!(self.output, "\tsubq    $16, %rsp")?;
        }
        Ok(())
    }

    // resets stack-pointer back to base-pointer
    fn reset_sp(&mut self) -> Result<(), std::fmt::Error> {
        // TODO: use cg_add in future when literals are in Registers
        writeln!(self.output, "\taddq    ${}, %rsp", self.sp_index)?;
        Ok(())
    }
    fn declare_var(&mut self, type_decl: &Types, name: String) -> Result<(), std::fmt::Error> {
        self.decl_size += type_decl.size();
        self.increment_sp()?;
        self.env.declare_var(type_decl, name);
        Ok(())
    }
    fn init_var(
        &mut self,
        type_decl: &Types,
        name: String,
        mut value_reg: Register,
    ) -> Result<(), std::fmt::Error> {
        self.declare_var(type_decl, name.clone())?;
        writeln!(
            self.output,
            "\tmovl    {}, {}",
            value_reg.name(&self.registers),
            self.env.get_var(name).name() // since var-declaration set everything up we just need declared register
        )?;
        value_reg.free(&mut self.registers);
        Ok(())
    }
    fn function_definition(
        &mut self,
        return_type: &Types,
        name: &Token,
        params: &[(Types, Token)],
        body: &Vec<Stmt>,
    ) -> Result<(), std::fmt::Error> {
        self.global_env
            .declare_func(*return_type, name.unwrap_string());
        self.cg_func_preamble(name.unwrap_string(), params)?;
        self.cg_stmts(body)?;
        self.cg_func_postamble(&name.unwrap_string())?;
        Ok(())
    }
    fn cg_func_preamble(
        &mut self,
        name: String,
        params: &[(Types, Token)],
    ) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "\n\t.text\n\t.globl _{}", name)?;
        writeln!(self.output, "_{}:", name)?; // generate function label
        writeln!(self.output, "\tpushq   %rbp\n\tmovq    %rsp, %rbp")?; // setup base pointer and stackpointer

        // initialize parameters
        for (i, (type_decl, param_name)) in params.iter().enumerate() {
            self.init_var(type_decl, param_name.unwrap_string(), Register::Arg(i))?;
        }
        Ok(())
    }
    fn cg_func_postamble(&mut self, name: &str) -> Result<(), std::fmt::Error> {
        self.reset_sp()?;
        writeln!(self.output, "{}_epilogue:", name)?;
        match name {
            "main" => writeln!(self.output, "\tmovl    $0, %eax")?,
            _ => writeln!(self.output, "\tnop")?,
        }
        writeln!(self.output, "\tpopq    %rbp\n\tret")?;
        self.env.reset_bp_offset(); // reset bp offset for next function
        Ok(())
    }

    pub fn block(
        &mut self,
        statements: &Vec<Stmt>,
        env: Environment<StackRegister>,
    ) -> Result<(), std::fmt::Error> {
        self.env.env = env;
        let result = self.cg_stmts(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env.env = *self.env.env.enclosing.as_ref().unwrap().clone();
        result
    }

    fn cg_literal_num(&mut self, num: i32) -> Result<Register, std::fmt::Error> {
        let scratch_index = self.registers.scratch_alloc();
        let reg = Register::Scratch(scratch_index);

        writeln!(
            self.output,
            "\tmovl    ${num}, {}",
            reg.name(&self.registers)
        )?;
        Ok(reg)
    }
    pub fn execute(&mut self, ast: &Expr) -> Result<Register, std::fmt::Error> {
        match ast {
            Expr::Binary { left, token, right } => self.cg_binary(left, token, right),
            Expr::Number(v) => self.cg_literal_num(*v),
            Expr::Grouping { expr } => self.execute(expr),
            Expr::Unary { token, right } => self.cg_unary(token, right),
            // Expr::Logical { left, token, right } => self.evaluate_logical(left, token, right),
            Expr::Assign { name, expr } => self.cg_assign(name.unwrap_string(), expr),
            Expr::Ident(name) => self.cg_ident(name.unwrap_string()),
            // Expr::CharLit(c) => TypeValues::Char(*c),
            Expr::Call {
                left_paren: _,
                callee,
                args,
            } => self.cg_call(callee, args),
            _ => unimplemented!("{:?}", ast),
        }
    }
    fn cg_assign(&mut self, name: String, expr: &Expr) -> Result<Register, std::fmt::Error> {
        let mut value_reg = self.execute(expr)?;
        let new_reg = self.env.get_var(name.clone()); // since stack pos is the same we don't have to change env

        // can't move from mem to mem so make temp scratch-register
        if matches!(value_reg, Register::Stack(_)) {
            let temp_scratch = Register::Scratch(self.registers.scratch_alloc());

            writeln!(
                self.output,
                "\tmovl    {}, {}",
                value_reg.name(&self.registers),
                temp_scratch.name(&self.registers),
            )?;
            value_reg = temp_scratch;
        }
        writeln!(
            self.output,
            "\tmovl    {}, {}",
            value_reg.name(&self.registers),
            new_reg.name(),
        )?;
        value_reg.free(&mut self.registers);
        Ok(Register::Stack(new_reg))
    }
    fn cg_ident(&mut self, name: String) -> Result<Register, std::fmt::Error> {
        let stack_reg = self.env.get_var(name);
        let dest_reg_index = self.registers.scratch_alloc();
        let reg = Register::Scratch(dest_reg_index);

        writeln!(
            self.output,
            "\tmovl    {}, {}",
            stack_reg.name(),
            reg.name(&self.registers)
        )?;
        Ok(reg)
    }
    fn cg_call(&mut self, callee: &Expr, args: &Vec<Expr>) -> Result<Register, std::fmt::Error> {
        let func_name = match callee {
            Expr::Ident(func_name) => func_name.unwrap_string(),
            _ => unreachable!("typechecker"),
        };
        // TODO: implement args by pushing on stack
        assert!(args.len() <= 6, "function cant have more than 6 args");

        // moving the arguments into their designated registers
        for (i, expr) in args.iter().enumerate() {
            let mut reg = self.execute(&expr)?;
            writeln!(
                self.output,
                "\tmovl    {}, {}",
                reg.name(&self.registers),
                Register::Arg(i).name(&self.registers),
            )?;
            reg.free(&mut self.registers);
        }

        writeln!(self.output, "\tcall    _{}", func_name)?;
        if self.env.get_func(func_name, &self.global_env) != Types::Void {
            let reg_index = self.registers.scratch_alloc();
            let return_reg = Register::Scratch(reg_index);
            writeln!(
                self.output,
                "\tmovl    %eax, {}",
                return_reg.name(&self.registers)
            )?;
            Ok(return_reg)
        } else {
            Ok(Register::Void)
        }
    }
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
    fn cg_unary(&mut self, token: &Token, right: &Expr) -> Result<Register, std::fmt::Error> {
        let reg = self.execute(right)?;
        match token.token {
            TokenType::Bang => {
                writeln!(self.output, "\tcmpl $0, {}", reg.name(&self.registers))?; // compares reg-value with 0
                writeln!(
                    self.output,
                    "\tsete %al\n\tmovzbl %al, {}",
                    reg.name(&self.registers)
                )?;
                // sets %al to 1 if comparison true and to 0 when false and then copies %al to current reg
            }
            TokenType::Minus => writeln!(self.output, "\tnegl {}", reg.name(&self.registers))?,
            _ => Error::new(token, "invalid unary operator").print_exit(),
        }
        Ok(reg)
    }

    fn cg_add(&mut self, mut left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\taddl {}, {}\n",
            left.name(&self.registers),
            right.name(&self.registers)
        )?;

        left.free(&mut self.registers);
        Ok(right)
    }
    fn cg_sub(&mut self, left: Register, mut right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tsubl {}, {}\n",
            right.name(&self.registers),
            left.name(&self.registers)
        )?;

        right.free(&mut self.registers);
        Ok(left)
    }

    fn cg_mult(
        &mut self,
        mut left: Register,
        right: Register,
    ) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\timull {}, {}\n",
            left.name(&self.registers),
            right.name(&self.registers)
        )?;

        left.free(&mut self.registers);
        Ok(right)
    }

    fn cg_div(&mut self, mut left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(self.output, "\tmovl {}, %eax", left.name(&self.registers))?;
        writeln!(
            self.output,
            "\tcqo\n\tidivl {}",
            right.name(&self.registers)
        )?; // rax / rcx => rax
        writeln!(self.output, "\tmovl %eax, {}", right.name(&self.registers))?; // move rax(int result) into right reg (remainder in rdx)

        left.free(&mut self.registers);
        Ok(right)
    }

    fn cg_comparison(
        &mut self,
        operator: &str,
        mut left: Register,
        right: Register,
    ) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tcmpl {}, {}",
            right.name(&self.registers),
            left.name(&self.registers)
        )?;
        // write ZF to %al based on operator and zero extend %right_register with value of %al
        writeln!(
            self.output,
            "\t{operator} %al\n\tmovzbl %al, {}",
            right.name(&self.registers)
        )?;

        left.free(&mut self.registers);
        Ok(right)
    }

    // returns register-index that holds result
    fn cg_binary(
        &mut self,
        left: &Expr,
        token: &Token,
        right: &Expr,
    ) -> Result<Register, std::fmt::Error> {
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
}
