use crate::codegen::{environment::*, register::*};
use crate::common::{error::*, expr::*, stmt::*, token::*, types::*};
use std::collections::HashMap;
use std::fmt::Write;
use std::fs::File;
use std::io::Write as _;

pub struct Compiler {
    scratch: ScratchRegisters,
    output: String,
    env: Environment,
    global_env: Environment,
    function_name: Option<String>,
    label_index: usize,
    func_stack_size: HashMap<String, usize>, // typechecker passes info about how many stack allocation there are in a function
    pub current_bp_offset: usize,            // offset from base-pointer where variable stays
}
impl Compiler {
    pub fn new(func_stack_size: HashMap<String, usize>) -> Self {
        let mut global_env = Environment::new(None);
        global_env.declare_func("printint".to_string(), Types::Void);
        Compiler {
            output: String::new(),
            scratch: ScratchRegisters::new(),
            current_bp_offset: 0,
            label_index: 0,
            env: Environment::new(None),
            function_name: None,
            func_stack_size,
            global_env,
        }
    }
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
                Environment::new(Some(Box::new(self.env.clone()))),
            ),
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(return_type, name.unwrap_string(), params, body)
            }
            Stmt::Return(_, expr) => self.return_statement(expr), // jump to function postamble
            Stmt::If(_, cond, then_branch, else_branch) => {
                self.if_statement(cond, then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(cond, body),
            _ => unimplemented!(),
        }
    }
    fn create_label(&mut self) -> usize {
        let result = self.label_index;
        self.label_index += 1;
        result
    }

    fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), std::fmt::Error> {
        let start_label = self.create_label();
        let end_label = self.create_label();

        writeln!(self.output, "\tjmp    L{}\nL{}:", end_label, start_label)?;
        self.visit(body)?;

        writeln!(self.output, "L{}:", end_label)?;
        let cond_reg = self.execute(cond)?;
        writeln!(
            self.output,
            "\tcmpl    $0, {}\n\tjne      L{}",
            cond_reg.name(&self.scratch),
            start_label
        )?;

        Ok(())
    }

    fn if_statement(
        &mut self,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Stmt>,
    ) -> Result<(), std::fmt::Error> {
        let cond_reg = self.execute(cond)?;
        let done_label = self.create_label();
        let mut else_label = done_label;

        writeln!(
            self.output,
            "\tcmpl    $0, {}",
            cond_reg.name(&self.scratch)
        )?;
        cond_reg.free(&mut self.scratch);

        if !else_branch.is_none() {
            else_label = self.create_label();
        }
        writeln!(self.output, "\tje    L{}", else_label)?;
        self.visit(then_branch)?;

        if let Some(else_branch) = else_branch {
            writeln!(self.output, "\tjmp    L{}", done_label)?;
            writeln!(self.output, "L{}:", else_label)?;
            self.visit(else_branch)?;
        }
        writeln!(self.output, "L{}:", done_label)?;
        Ok(())
    }
    fn return_statement(&mut self, value: &Option<Expr>) -> Result<(), std::fmt::Error> {
        let function_epilogue = format!(
            "{}_epilogue",
            self.function_name
                .as_ref()
                .expect("typechecker catches nested function-declarations")
                .clone()
        );
        match value {
            Some(expr) => {
                let return_value = self.execute(expr)?;
                writeln!(
                    self.output,
                    "\tmovl    {}, %eax\n\tjmp    {}",
                    return_value.name(&self.scratch),
                    function_epilogue
                )?;
                return_value.free(&mut self.scratch);
                Ok(())
            }
            None => writeln!(self.output, "\tjmp    {}", function_epilogue),
        }
    }

    fn declare_var(&mut self, type_decl: &Types, name: String) -> Result<(), std::fmt::Error> {
        self.current_bp_offset += type_decl.size();

        self.env.declare_var(name, self.current_bp_offset);
        Ok(())
    }
    fn init_var(
        &mut self,
        type_decl: &Types,
        name: String,
        value_reg: Register,
    ) -> Result<(), std::fmt::Error> {
        self.declare_var(type_decl, name.clone())?;

        writeln!(
            self.output,
            "\tmovl    {}, {}",
            value_reg.name(&self.scratch),
            self.env.get_var(name).name() // since var-declaration set everything up we just need declared register
        )?;
        value_reg.free(&mut self.scratch);

        Ok(())
    }
    fn function_definition(
        &mut self,
        return_type: &Types,
        name: String,
        params: &[(Types, Token)],
        body: &Vec<Stmt>,
    ) -> Result<(), std::fmt::Error> {
        self.global_env.declare_func(name.clone(), *return_type);

        self.function_name = Some(name.clone()); // save function name for return label jump

        // generate function code
        self.cg_func_preamble(&name, params)?;
        self.visit(&Stmt::Block(body.clone()))?;
        self.cg_func_postamble(&name)?;

        self.current_bp_offset = 0;
        self.function_name = None;

        Ok(())
    }
    fn align_stack(&mut self, name: &str) {
        let size = self.func_stack_size[name];
        if size < 16 && size > 0 {
            // self.func_stack_size[name] += 16;
            *self.func_stack_size.entry(name.to_owned()).or_default() += 16 - size;
        } else {
            *self.func_stack_size.entry(name.to_owned()).or_default() += 16 - (size % 16);
        }
    }
    fn allocate_stack(&mut self, name: &str) -> Result<(), std::fmt::Error> {
        // stack has to be 16byte aligned
        self.align_stack(name);

        if self.func_stack_size[name] > 0 {
            writeln!(
                self.output,
                "\tsubq    ${},%rsp",
                self.func_stack_size[name]
            )?;
        }
        Ok(())
    }
    fn dealloc_stack(&mut self, name: &str) -> Result<(), std::fmt::Error> {
        if self.func_stack_size[name] > 0 {
            writeln!(
                self.output,
                "\taddq    ${},%rsp",
                self.func_stack_size[name]
            )?;
        }
        Ok(())
    }
    fn cg_func_preamble(
        &mut self,
        name: &str,
        params: &[(Types, Token)],
    ) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "\n\t.text\n\t.globl _{}", name)?;
        writeln!(self.output, "_{}:", name)?; // generate function label
        writeln!(self.output, "\tpushq   %rbp\n\tmovq    %rsp, %rbp")?; // setup base pointer and stackpointer

        // allocate stack-space for local vars
        self.allocate_stack(name)?;

        // initialize parameters
        for (i, (type_decl, param_name)) in params.iter().enumerate() {
            self.init_var(type_decl, param_name.unwrap_string(), Register::Arg(i))?;
        }
        Ok(())
    }
    fn cg_func_postamble(&mut self, name: &str) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "{}_epilogue:", name)?;
        self.dealloc_stack(name)?;

        match name {
            "main" => writeln!(self.output, "\tmovl    $0, %eax")?, // if main return 0 success code
            _ => writeln!(self.output, "\tnop")?,
        }
        writeln!(self.output, "\tpopq    %rbp\n\tret")?;
        Ok(())
    }

    pub fn block(
        &mut self,
        statements: &Vec<Stmt>,
        env: Environment,
    ) -> Result<(), std::fmt::Error> {
        self.env = env;
        let result = self.cg_stmts(statements);

        // this means assignment to vars inside block which were declared outside
        // of the block are still apparent after block
        self.env = *self.env.enclosing.as_ref().unwrap().clone();
        result
    }

    fn cg_literal_num(&mut self, num: i32) -> Result<Register, std::fmt::Error> {
        let scratch_index = self.scratch.scratch_alloc();
        let reg = Register::Scratch(scratch_index);

        writeln!(self.output, "\tmovl    ${num}, {}", reg.name(&self.scratch))?;
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
            let temp_scratch = Register::Scratch(self.scratch.scratch_alloc());

            writeln!(
                self.output,
                "\tmovl    {}, {}",
                value_reg.name(&self.scratch),
                temp_scratch.name(&self.scratch),
            )?;
            value_reg = temp_scratch;
        }
        writeln!(
            self.output,
            "\tmovl    {}, {}",
            value_reg.name(&self.scratch),
            new_reg.name(),
        )?;
        value_reg.free(&mut self.scratch);
        Ok(Register::Stack(new_reg))
    }
    fn cg_ident(&mut self, name: String) -> Result<Register, std::fmt::Error> {
        // TODO: directly return stack-reg
        let stack_reg = self.env.get_var(name);
        let dest_reg_index = self.scratch.scratch_alloc();
        let reg = Register::Scratch(dest_reg_index);

        writeln!(
            self.output,
            "\tmovl    {}, {}",
            stack_reg.name(),
            reg.name(&self.scratch)
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
            let reg = self.execute(&expr)?;
            writeln!(
                self.output,
                "\tmovl    {}, {}",
                reg.name(&self.scratch),
                Register::Arg(i).name(&self.scratch),
            )?;
            reg.free(&mut self.scratch);
        }

        // push registers that are in use currently onto stack so they won't be overwritten during function
        let pushed_regs: Vec<&ScratchRegister> =
            self.scratch.registers.iter().filter(|r| r.in_use).collect();

        for reg in pushed_regs.iter().by_ref() {
            writeln!(self.output, "\tpushq   {}", reg.name_64)?;
        }

        // have to 16byte align stack depending on amount of pushs before
        if pushed_regs.len() > 0 && pushed_regs.len() % 2 != 0 {
            writeln!(self.output, "\tsubq    $8,%rsp")?;
        }
        writeln!(self.output, "\tcall    _{}", func_name)?;

        // undo the stack alignment from before call
        if pushed_regs.len() > 0 && pushed_regs.len() % 2 != 0 {
            writeln!(self.output, "\taddq    $8,%rsp")?;
        }

        // pop registers from before function call back to scratch registers
        for reg in pushed_regs.iter().rev().by_ref() {
            writeln!(self.output, "\tpopq   {}", reg.name_64)?;
        }

        if self.global_env.get_func(func_name) != Types::Void {
            let reg_index = self.scratch.scratch_alloc();
            let return_reg = Register::Scratch(reg_index);
            writeln!(
                self.output,
                "\tmovl    %eax, {}",
                return_reg.name(&self.scratch)
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
                writeln!(self.output, "\tcmpl $0, {}", reg.name(&self.scratch))?; // compares reg-value with 0
                writeln!(
                    self.output,
                    "\tsete %al\n\tmovzbl %al, {}",
                    reg.name(&self.scratch)
                )?;
                // sets %al to 1 if comparison true and to 0 when false and then copies %al to current reg
            }
            TokenType::Minus => writeln!(self.output, "\tnegl {}", reg.name(&self.scratch))?,
            _ => Error::new(token, "invalid unary operator").print_exit(),
        }
        Ok(reg)
    }

    fn cg_add(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\taddl {}, {}\n",
            left.name(&self.scratch),
            right.name(&self.scratch)
        )?;

        left.free(&mut self.scratch);
        Ok(right)
    }
    fn cg_sub(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tsubl {}, {}\n",
            right.name(&self.scratch),
            left.name(&self.scratch)
        )?;

        right.free(&mut self.scratch);
        Ok(left)
    }

    fn cg_mult(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\timull {}, {}\n",
            left.name(&self.scratch),
            right.name(&self.scratch)
        )?;

        left.free(&mut self.scratch);
        Ok(right)
    }

    fn cg_div(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(self.output, "\tmovl {}, %eax", left.name(&self.scratch))?;
        writeln!(self.output, "\tcqo\n\tidivl {}", right.name(&self.scratch))?; // rax / rcx => rax
        writeln!(self.output, "\tmovl %eax, {}", right.name(&self.scratch))?; // move rax(int result) into right reg (remainder in rdx)

        left.free(&mut self.scratch);
        Ok(right)
    }

    fn cg_comparison(
        &mut self,
        operator: &str,
        left: Register,
        right: Register,
    ) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tcmpl {}, {}",
            right.name(&self.scratch),
            left.name(&self.scratch)
        )?;
        // write ZF to %al based on operator and zero extend %right_register with value of %al
        writeln!(
            self.output,
            "\t{operator} %al\n\tmovzbl %al, {}",
            right.name(&self.scratch)
        )?;

        left.free(&mut self.scratch);
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
