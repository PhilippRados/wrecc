use crate::codegen::register::*;
use crate::common::{environment::*, expr::*, stmt::*, token::*, types::*};
use crate::typechecker::{align_by, create_label};
use std::collections::{HashMap, VecDeque};
use std::fmt::Write;
use std::fs::File;
use std::io::Write as _;
use std::rc::Rc;

// converts a register into a scratch-register if it matches the pattern
macro_rules! convert_reg {
    ($self:ident,$reg:ident,$($pattern:pat_param)|+) => {
        match $reg {
            $($pattern)|+ => $self.scratch_temp($reg)?,
            _ => $reg
        }
    };
}

pub struct Compiler {
    scratch: ScratchRegisters,
    output: String,
    env: Vec<Symbols>,
    function_name: Option<String>,

    // index of current label
    label_index: usize,

    // map containing Strings and their corresponding label-index
    const_labels: HashMap<String, usize>,

    // which args have to be pushed on stack before entering next function
    // so that they don't get overwritten
    saved_args: Vec<Register>,

    // offset from base-pointer where variable stays
    current_bp_offset: usize,

    // loop labels saved so that break and continue jump to them
    jump_labels: Vec<(usize, usize)>,

    // switch information, about cases and defaults
    switches: VecDeque<(Vec<i64>, bool)>,

    // case-labels get defined in each switch and then the cases and defaults
    // pop them in order of appearance
    case_labels: VecDeque<usize>,
}
impl Compiler {
    pub fn new(
        const_labels: HashMap<String, usize>,
        env: Vec<Symbols>,
        switches: Vec<(Vec<i64>, bool)>,
    ) -> Self {
        Compiler {
            env,
            switches: switches.into(),
            const_labels,
            output: String::new(),
            scratch: ScratchRegisters::new(),
            current_bp_offset: 0,
            label_index: 0,
            function_name: None,
            saved_args: Vec::new(),
            jump_labels: Vec::new(),
            case_labels: VecDeque::new(),
        }
    }

    pub fn compile(&mut self, statements: &Vec<Stmt>) {
        if let Err(e) = self.cg_const_labels() {
            eprintln!("{:?}", e);
            return;
        }
        if let Err(e) = self.cg_stmts(statements) {
            eprintln!("{:?}", e);
            return;
        }
        let mut output = File::create("/Users/philipprados/documents/coding/Rust/rucc/generated.s")
            .expect("create failed");

        output
            .write_all(self.output.as_bytes())
            .expect("write failed");
    }
    fn cg_const_labels(&mut self) -> Result<(), std::fmt::Error> {
        for (data, label_index) in self.const_labels.iter().by_ref() {
            writeln!(self.output, "LS{}:\n\t.string \"{}\"", label_index, data)?;
        }
        Ok(())
    }
    fn cg_stmts(&mut self, statements: &Vec<Stmt>) -> Result<(), std::fmt::Error> {
        for s in statements {
            self.visit(s)?
        }
        Ok(())
    }
    fn visit(&mut self, statement: &Stmt) -> Result<(), std::fmt::Error> {
        match statement {
            Stmt::Expr(expr) => {
                self.execute_expr(expr)?.free(); // result isn't used
                Ok(())
            }
            Stmt::DeclareVar(type_decl, name) => self.declare_var(type_decl, name),
            Stmt::InitVar(type_decl, name, expr) => {
                let value_reg = self.execute_expr(expr)?;
                self.init_var(type_decl, name, value_reg)
            }
            Stmt::InitList(type_decl, name, exprs) => self.init_list(type_decl, name, exprs),
            Stmt::Block(statements) => self.block(statements),
            Stmt::Function(_, name, params, body) => self.function_definition(name, params, body),
            Stmt::Return(_, expr) => self.return_statement(expr),
            Stmt::If(_, cond, then_branch, else_branch) => {
                self.if_statement(cond, then_branch, else_branch)
            }
            Stmt::While(_, cond, body) => self.while_statement(cond, body),
            Stmt::Do(_, body, cond) => self.do_statement(body, cond),
            Stmt::For(_, init, cond, inc, body) => self.for_statement(init, cond, inc, body),
            Stmt::Break(..) => self.jump_statement(self.jump_labels.last().expect("typechecker").0),
            Stmt::Continue(..) => {
                self.jump_statement(self.jump_labels.last().expect("typechecker").1)
            }
            Stmt::Switch(_, cond, body) => self.switch_statement(cond, body),
            Stmt::Case(_, _, body) | Stmt::Default(_, body) => self.case_statement(body),
        }
    }
    fn switch_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), std::fmt::Error> {
        let (cases, has_default) = self.switches.pop_front().unwrap();

        let mut jump_labels: Vec<usize> = (0..cases.len())
            .map(|_| create_label(&mut self.label_index))
            .collect();

        let cond_reg = self.execute_expr(cond)?;

        for (case_value, label) in cases.iter().zip(jump_labels.clone()) {
            writeln!(
                self.output,
                "\tcmp{}    ${}, {}\n\tje      L{}",
                cond_reg.get_type().suffix(),
                case_value,
                cond_reg.name(),
                label
            )?;
        }
        cond_reg.free();

        let default_label = if has_default {
            let label = create_label(&mut self.label_index);
            jump_labels.push(label);
            Some(label)
        } else {
            None
        };
        if let Some(label) = default_label {
            writeln!(self.output, "\tjmp     L{}", label)?;
        }

        let break_label = create_label(&mut self.label_index);

        self.jump_labels.push((break_label, 0));
        self.case_labels.append(&mut jump_labels.into());

        self.visit(body)?;

        writeln!(self.output, "L{}:", break_label)?;

        self.jump_labels.pop();

        Ok(())
    }
    fn case_statement(&mut self, body: &Stmt) -> Result<(), std::fmt::Error> {
        let label = self.case_labels.pop_front().unwrap();

        writeln!(self.output, "L{}:", label)?;

        self.visit(body)?;

        Ok(())
    }
    fn do_statement(&mut self, body: &Stmt, cond: &Expr) -> Result<(), std::fmt::Error> {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        writeln!(self.output, "L{}:", body_label)?;
        self.visit(body)?;

        writeln!(self.output, "L{}:", cond_label)?;
        let mut cond_reg = self.execute_expr(cond)?;
        cond_reg = self.convert_to_rval(cond_reg)?;

        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tjne      L{}",
            cond_reg.get_type().suffix(),
            cond_reg.name(),
            body_label
        )?;
        cond_reg.free();

        writeln!(self.output, "L{}:", end_label)?;

        self.jump_labels.pop();

        Ok(())
    }

    fn jump_statement(&mut self, label: usize) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "\tjmp     L{}", label)
    }
    fn init_list(
        &mut self,
        type_decl: &NEWTypes,
        name: &Token,
        exprs: &[Expr],
    ) -> Result<(), std::fmt::Error> {
        match self.env.get(name.token.get_index()).unwrap().is_global() {
            true => {
                writeln!(self.output, "\n\t.data\n_{}:", name.unwrap_string())?;

                self.env
                    .get_mut(name.token.get_index())
                    .unwrap()
                    .unwrap_var_mut()
                    .set_reg(Register::Label(LabelRegister::Var(
                        name.unwrap_string(),
                        type_decl.clone(),
                    )));
            }
            false => {
                self.declare_var(type_decl, name)?;
            }
        }
        let is_global = self.env.get(name.token.get_index()).unwrap().is_global();
        for e in exprs.iter() {
            match (is_global, &e.kind) {
                // init-list is assignment syntax sugar
                (true, ExprKind::Assign { r_expr, .. }) => {
                    let r_value = self.execute_expr(r_expr)?;
                    writeln!(
                        self.output,
                        "\t.{} {}",
                        r_value.get_type().complete_suffix(),
                        r_value.base_name()
                    )?;
                    r_value.free()
                }
                (false, _) => self.execute_expr(e)?.free(),
                _ => unreachable!(),
            };
        }
        Ok(())
    }

    fn for_statement(
        &mut self,
        init: &Option<Box<Stmt>>,
        cond: &Option<Expr>,
        inc: &Option<Expr>,
        body: &Stmt,
    ) -> Result<(), std::fmt::Error> {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);

        let inc_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, inc_label));
        if let Some(init) = init {
            self.visit(init)?;
        }
        writeln!(self.output, "\tjmp    L{}\nL{}:", cond_label, body_label)?;
        self.visit(body)?;

        writeln!(self.output, "L{}:", inc_label)?;

        if let Some(inc) = inc {
            self.execute_expr(inc)?.free();
        }

        writeln!(self.output, "L{}:", cond_label)?;

        match cond {
            Some(cond) => {
                let mut cond_reg = self.execute_expr(cond)?;
                cond_reg = self.convert_to_rval(cond_reg)?;

                writeln!(
                    self.output,
                    "\tcmp{}    $0, {}\n\tjne      L{}",
                    cond_reg.get_type().suffix(),
                    cond_reg.name(),
                    body_label
                )?;
                cond_reg.free();
            }
            None => writeln!(self.output, "\tjmp    L{}", body_label)?,
        }

        writeln!(self.output, "L{}:", end_label)?;

        self.jump_labels.pop();

        Ok(())
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) -> Result<(), std::fmt::Error> {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        writeln!(self.output, "\tjmp    L{}\nL{}:", cond_label, body_label)?;
        self.visit(body)?;

        writeln!(self.output, "L{}:", cond_label)?;

        let mut cond_reg = self.execute_expr(cond)?;
        cond_reg = self.convert_to_rval(cond_reg)?;

        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tjne      L{}",
            cond_reg.get_type().suffix(),
            cond_reg.name(),
            body_label
        )?;
        cond_reg.free();

        // don't know before wether loop contains break statement
        // could be checked by typechecker
        writeln!(self.output, "L{}:", end_label)?;

        self.jump_labels.pop();

        Ok(())
    }

    fn if_statement(
        &mut self,
        cond: &Expr,
        then_branch: &Stmt,
        else_branch: &Option<Stmt>,
    ) -> Result<(), std::fmt::Error> {
        let mut cond_reg = self.execute_expr(cond)?;
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let mut else_label = done_label;

        writeln!(
            self.output,
            "\tcmp{}    $0, {}",
            cond_reg.get_type().suffix(),
            cond_reg.name()
        )?;
        cond_reg.free();

        if !else_branch.is_none() {
            else_label = create_label(&mut self.label_index);
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
                let return_value = self.execute_expr(expr)?;
                writeln!(
                    self.output,
                    "\tmov{}    {}, {}\n\tjmp    {}",
                    return_value.get_type().suffix(),
                    return_value.name(),
                    return_value.get_type().return_reg(),
                    function_epilogue
                )?;
                return_value.free();
                Ok(())
            }
            None => writeln!(self.output, "\tjmp    {}", function_epilogue),
        }
    }
    fn declare_var(&mut self, type_decl: &NEWTypes, name: &Token) -> Result<(), std::fmt::Error> {
        let reg = match self.env.get(name.token.get_index()).unwrap().is_global() {
            true => {
                writeln!(
                    self.output,
                    "\n\t.data\n_{}:\n\t.zero {}",
                    name.unwrap_string(),
                    type_decl.size()
                )?;
                Register::Label(LabelRegister::Var(name.unwrap_string(), type_decl.clone()))
            }
            false => {
                self.current_bp_offset += type_decl.size();
                self.current_bp_offset = align(self.current_bp_offset, type_decl);

                Register::Stack(StackRegister::new(
                    self.current_bp_offset,
                    type_decl.clone(),
                ))
            }
        };
        self.env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_var_mut()
            .set_reg(reg);
        Ok(())
    }
    fn init_var(
        &mut self,
        type_decl: &NEWTypes,
        var_name: &Token,
        value_reg: Register,
    ) -> Result<(), std::fmt::Error> {
        let name = var_name.unwrap_string();

        match self
            .env
            .get(var_name.token.get_index())
            .unwrap()
            .is_global()
        {
            true => {
                writeln!(
                    self.output,
                    "\n\t.data\n_{}:\n\t.{} {}",
                    name,
                    type_decl.complete_suffix(),
                    value_reg.base_name()
                )?;

                self.env
                    .get_mut(var_name.token.get_index())
                    .unwrap()
                    .unwrap_var_mut()
                    .set_reg(Register::Label(LabelRegister::Var(name, type_decl.clone())));
            }
            false => {
                self.declare_var(type_decl, var_name)?;

                self.cg_assign(
                    self.env
                        .get(var_name.token.get_index())
                        .unwrap()
                        .unwrap_var()
                        .get_reg(),
                    value_reg,
                )?
                .free();
            }
        }

        Ok(())
    }
    fn function_definition(
        &mut self,
        name: &Token,
        params: &[(NEWTypes, Token)],
        body: &Vec<Stmt>,
    ) -> Result<(), std::fmt::Error> {
        // save function name for return label jump
        self.function_name = Some(name.unwrap_string());

        // generate function code
        self.cg_func_preamble(name, params)?;
        self.cg_stmts(body)?;
        self.cg_func_postamble(name)?;

        self.current_bp_offset = 0;
        self.function_name = None;

        Ok(())
    }
    fn allocate_stack(&mut self, name: &Token) -> Result<(), std::fmt::Error> {
        let stack_size = self
            .env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_func()
            .get_stack_size();
        if stack_size > 0 {
            writeln!(self.output, "\tsubq    ${},%rsp", stack_size)?;
        }
        Ok(())
    }
    fn dealloc_stack(&mut self, name: &Token) -> Result<(), std::fmt::Error> {
        let stack_size = self
            .env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_func()
            .get_stack_size();
        if stack_size > 0 {
            writeln!(self.output, "\taddq    ${},%rsp", stack_size)?;
        }
        Ok(())
    }
    fn cg_func_preamble(
        &mut self,
        name: &Token,
        params: &[(NEWTypes, Token)],
    ) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "\n\t.text\n\t.globl _{}", name.unwrap_string())?;
        writeln!(self.output, "_{}:", name.unwrap_string())?; // generate function label
        writeln!(self.output, "\tpushq   %rbp\n\tmovq    %rsp, %rbp")?; // setup base pointer and stackpointer

        // allocate stack-space for local vars
        self.allocate_stack(name)?;

        // initialize parameters
        for (i, (type_decl, param_name)) in params.iter().enumerate() {
            self.init_var(type_decl, param_name, Register::Arg(i, type_decl.clone()))?;
        }
        Ok(())
    }
    fn cg_func_postamble(&mut self, name: &Token) -> Result<(), std::fmt::Error> {
        writeln!(self.output, "{}_epilogue:", name.unwrap_string())?;
        self.dealloc_stack(name)?;

        writeln!(self.output, "\tpopq    %rbp\n\tret")?;
        Ok(())
    }

    pub fn block(&mut self, statements: &Vec<Stmt>) -> Result<(), std::fmt::Error> {
        self.cg_stmts(statements)
    }

    fn cg_literal(&mut self, num: usize, t: Types) -> Result<Register, std::fmt::Error> {
        Ok(Register::Literal(
            num,
            NEWTypes::Primitive(match t {
                Types::Char => Types::Char,
                _ if i32::try_from(num).is_ok() => Types::Int,
                _ => Types::Long,
            }),
        ))
    }
    pub fn execute_expr(&mut self, ast: &Expr) -> Result<Register, std::fmt::Error> {
        match &ast.kind {
            ExprKind::Binary { left, token, right } => {
                let left_reg = self.execute_expr(left)?;
                let right_reg = self.execute_expr(right)?;

                self.cg_binary(left_reg, &token.token, right_reg)
            }
            ExprKind::Number(v) => self.cg_literal(*v as usize, Types::Int),
            ExprKind::CharLit(c) => self.cg_literal(*c as usize, Types::Char),
            ExprKind::Grouping { expr } => self.execute_expr(expr),
            ExprKind::Unary {
                token,
                right,
                is_global,
            } => self.cg_unary(token, right, *is_global, ast.type_decl.clone().unwrap()),
            ExprKind::Logical { left, token, right } => self.cg_logical(left, token, right),
            ExprKind::Assign { l_expr, r_expr, .. } => {
                let left_reg = self.execute_expr(l_expr)?;
                let right_reg = self.execute_expr(r_expr)?;

                self.cg_assign(left_reg, right_reg)
            }
            ExprKind::CompoundAssign {
                l_expr,
                r_expr,
                token,
            } => self.cg_comp_assign(l_expr, token, r_expr),
            ExprKind::Ident(name) => Ok(self
                .env
                .get(name.token.get_index())
                .unwrap()
                .unwrap_var()
                .get_reg()),
            ExprKind::Call { callee, args, .. } => {
                self.cg_call(callee, args, ast.type_decl.clone().unwrap())
            }
            ExprKind::Cast {
                expr, direction, ..
            } => match direction.clone().expect("typechecker should fill this") {
                CastDirection::Up => self.cg_cast_up(expr, ast.type_decl.clone().unwrap()),
                CastDirection::Down => self.cg_cast_down(expr, ast.type_decl.clone().unwrap()),
                CastDirection::Equal => self.execute_expr(expr),
            },
            ExprKind::ScaleUp { expr, by } => self.cg_scale_up(expr, by),
            ExprKind::ScaleDown { expr, shift_amount } => self.cg_scale_down(expr, shift_amount),
            ExprKind::String(token) => self.cg_string(token.unwrap_string()),
            ExprKind::PostUnary {
                token,
                left,
                by_amount,
            } => self.cg_postunary(token, left, by_amount),
            ExprKind::MemberAccess { expr, member, .. } => {
                let expr = self.execute_expr(expr)?;
                self.cg_member_access(expr, member, true)
            }
            ExprKind::Ternary {
                cond,
                true_expr,
                false_expr,
                ..
            } => self.cg_ternary(cond, true_expr, false_expr),
            ExprKind::Nop => unreachable!("only used in parser"),
        }
    }

    fn cg_ternary(
        &mut self,
        cond: &Expr,
        true_expr: &Expr,
        false_expr: &Expr,
    ) -> Result<Register, std::fmt::Error> {
        let mut cond_reg = self.execute_expr(cond)?;
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let else_label = create_label(&mut self.label_index);

        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tje      L{}",
            cond_reg.get_type().suffix(),
            cond_reg.name(),
            else_label
        )?;
        cond_reg.free();

        let result = Register::Scratch(
            self.scratch.scratch_alloc(),
            true_expr.clone().type_decl.unwrap(),
            ValueKind::Rvalue,
        );
        let true_reg = self.execute_expr(true_expr)?;

        // copy both expressions into result register
        writeln!(
            self.output,
            "\tmov{}    {}, {}",
            true_reg.get_type().suffix(),
            true_reg.name(),
            result.name()
        )?;
        true_reg.free();

        writeln!(self.output, "\tjmp     L{}", done_label)?;
        writeln!(self.output, "L{}:", else_label)?;

        let false_reg = self.execute_expr(false_expr)?;

        writeln!(
            self.output,
            "\tmov{}   {}, {}",
            false_reg.get_type().suffix(),
            false_reg.name(),
            result.name()
        )?;
        false_reg.free();

        writeln!(self.output, "L{}:", done_label)?;

        Ok(result)
    }
    fn cg_member_access(
        &mut self,
        reg: Register,
        member: &Token,
        free: bool,
    ) -> Result<Register, std::fmt::Error> {
        let member = member.unwrap_string();

        if let NEWTypes::Struct(s) = reg.get_type() {
            let offset = s
                .members()
                .iter()
                .take_while(|(_, name)| name.unwrap_string() != member)
                .fold(0, |acc, (t, _)| acc + t.size());
            let members_iter = s.members();
            let (member_type, _) = members_iter
                .iter()
                .find(|(_, name)| name.unwrap_string() == member)
                .unwrap();

            let address = self.cg_address_at(reg, false, free)?;
            let mut result = if offset != 0 {
                self.cg_add(
                    Register::Literal(offset, NEWTypes::Primitive(Types::Int)),
                    address,
                )?
            } else {
                address
            };
            result.set_type(member_type.clone());
            result.set_value_kind(ValueKind::Lvalue);
            Ok(result)
        } else if let NEWTypes::Union(s) = reg.get_type() {
            let members_iter = s.members();
            let (member_type, _) = members_iter
                .iter()
                .find(|(_, name)| name.unwrap_string() == member)
                .unwrap();

            let mut result = self.cg_address_at(reg, false, free)?;

            result.set_type(member_type.clone());
            result.set_value_kind(ValueKind::Lvalue);
            Ok(result)
        } else {
            unreachable!("{:?}", reg.get_type())
        }
    }
    fn cg_comp_assign(
        &mut self,
        l_expr: &Expr,
        token: &Token,
        r_expr: &Expr,
    ) -> Result<Register, std::fmt::Error> {
        let l_reg = self.execute_expr(l_expr)?;
        let r_reg = self.execute_expr(r_expr)?;

        let mut temp_scratch = Register::Scratch(
            self.scratch.scratch_alloc(),
            l_reg.get_type(),
            ValueKind::Rvalue,
        );
        // have to do integer-promotion in codegen
        if temp_scratch.get_type().size() < Types::Int.size()
            && (matches!(l_reg, Register::Scratch(..) | Register::Stack(..)))
        {
            temp_scratch.set_type(NEWTypes::Primitive(Types::Int));
            writeln!(
                self.output,
                "movs{}{}   {}, {}",
                l_reg.get_type().suffix(),
                temp_scratch.get_type().suffix(),
                l_reg.name(),
                temp_scratch.name()
            )?;
        } else {
            writeln!(
                self.output,
                "\tmov{}    {}, {}",
                temp_scratch.get_type().suffix(),
                l_reg.name(),
                temp_scratch.name(),
            )?;
        }
        let mut bin_reg = self.cg_binary(temp_scratch, &token.comp_to_binary(), r_reg)?;

        // we can do this because typechecker would catch any type-errors
        bin_reg.set_type(l_reg.get_type());
        let result = self.cg_assign(l_reg, bin_reg)?;

        Ok(result)
    }
    fn cg_postunary(
        &mut self,
        token: &Token,
        expr: &Expr,
        by_amount: &usize,
    ) -> Result<Register, std::fmt::Error> {
        let reg = self.execute_expr(expr)?;
        let mut return_reg = Register::Scratch(
            self.scratch.scratch_alloc(),
            reg.get_type(),
            ValueKind::Rvalue,
        );

        // assign value to return-register before binary operation
        // have to do integer-promotion in codegen
        if return_reg.get_type().size() < Types::Int.size() {
            return_reg.set_type(NEWTypes::Primitive(Types::Int));
            writeln!(
                self.output,
                "movs{}{}   {}, {}",
                reg.get_type().suffix(),
                return_reg.get_type().suffix(),
                reg.name(),
                return_reg.name()
            )?;
        } else {
            writeln!(
                self.output,
                "\tmov{}    {}, {}",
                return_reg.get_type().suffix(),
                reg.name(),
                return_reg.name(),
            )?;
        }

        match token.token {
            TokenType::PlusPlus => writeln!(
                self.output,
                "\tadd{}  ${},{}",
                reg.get_type().suffix(),
                by_amount,
                reg.name()
            )?,
            TokenType::MinusMinus => writeln!(
                self.output,
                "\tsub{}  ${},{}",
                reg.get_type().suffix(),
                by_amount,
                reg.name()
            )?,
            _ => unreachable!(),
        };
        reg.free();

        Ok(return_reg)
    }
    fn cg_string(&mut self, name: String) -> Result<Register, std::fmt::Error> {
        Ok(Register::Label(LabelRegister::String(
            self.const_labels[&name],
        )))
    }
    fn cg_scale_down(
        &mut self,
        expr: &Expr,
        by_amount: &usize,
    ) -> Result<Register, std::fmt::Error> {
        let mut value_reg = self.execute_expr(expr)?;
        value_reg = convert_reg!(self, value_reg, Register::Literal(..));

        writeln!(
            self.output,
            "sar{}   ${}, {}", // right shift number, equivalent to division (works bc type-size is 2^n)
            value_reg.get_type().suffix(),
            by_amount,
            value_reg.name()
        )?;

        Ok(value_reg)
    }
    fn cg_scale_up(&mut self, expr: &Expr, by_amount: &usize) -> Result<Register, std::fmt::Error> {
        let mut value_reg = self.execute_expr(expr)?;
        value_reg = convert_reg!(self, value_reg, Register::Literal(..) | Register::Stack(..));

        writeln!(
            self.output,
            "imul{}   ${}, {}",
            value_reg.get_type().suffix(),
            by_amount,
            value_reg.name()
        )?;

        Ok(value_reg)
    }
    fn cg_cast_down(
        &mut self,
        expr: &Expr,
        new_type: NEWTypes,
    ) -> Result<Register, std::fmt::Error> {
        let mut value_reg = self.execute_expr(expr)?;
        value_reg.set_type(new_type);

        Ok(value_reg)
    }
    fn cg_cast_up(&mut self, expr: &Expr, new_type: NEWTypes) -> Result<Register, std::fmt::Error> {
        let mut value_reg = self.execute_expr(expr)?;

        if matches!(value_reg, Register::Scratch(..) | Register::Stack(..)) {
            let dest_reg = Register::Scratch(
                self.scratch.scratch_alloc(),
                new_type.clone(),
                ValueKind::Rvalue,
            );

            writeln!(
                self.output,
                "movs{}{}   {}, {}", //sign extend smaller type
                expr.type_decl.clone().unwrap().suffix(),
                new_type.suffix(),
                value_reg.name(),
                dest_reg.name()
            )?;
            value_reg.free();
            Ok(dest_reg)
        } else {
            value_reg.set_type(new_type);
            Ok(value_reg)
        }
    }
    fn cg_assign(
        &mut self,
        l_value: Register,
        mut r_value: Register,
    ) -> Result<Register, std::fmt::Error> {
        if let NEWTypes::Struct(s) = l_value.get_type() {
            // when assigning structs have to assign each member
            for m in s.members().iter() {
                let member_token = Token::default(TokenType::Ident(m.1.unwrap_string(), 0));
                let member_lvalue = self.cg_member_access(l_value.clone(), &member_token, false)?;
                let member_rvalue = self.cg_member_access(r_value.clone(), &member_token, false)?;

                self.cg_assign(member_lvalue, member_rvalue)?.free();
            }
            r_value.free();
            Ok(l_value)
        } else {
            // can't move from mem to mem so make temp scratch-register
            r_value = convert_reg!(self, r_value, Register::Stack(..) | Register::Label(..));
            r_value = self.convert_to_rval(r_value)?;

            writeln!(
                self.output,
                "\tmov{}    {}, {}",
                r_value.get_type().suffix(),
                r_value.name(),
                l_value.name(),
            )?;
            r_value.free();
            Ok(l_value)
        }
    }
    fn cg_call(
        &mut self,
        callee: &Expr,
        args: &Vec<Expr>,
        return_type: NEWTypes,
    ) -> Result<Register, std::fmt::Error> {
        let func_name = match &callee.kind {
            ExprKind::Ident(func_name) => func_name.unwrap_string(),
            _ => unreachable!("typechecker"),
        };
        // TODO: implement args by pushing on stack
        assert!(args.len() <= 6, "function cant have more than 6 args");

        let callee_saved_regs = self.registers_in_use();
        self.spill_regs(&callee_saved_regs)?;

        // moving the arguments into their designated registers
        for (i, expr) in args.iter().enumerate().rev() {
            let reg = self.execute_expr(expr)?;

            let arg = Register::Arg(i, expr.type_decl.clone().unwrap());
            writeln!(
                self.output,
                "\tmov{}    {}, {}",
                expr.type_decl.clone().unwrap().suffix(),
                reg.name(),
                arg.name(),
            )?;
            reg.free();

            self.saved_args.push(arg);
        }

        writeln!(self.output, "\tcall    _{}", func_name)?;

        self.unspill_regs(&callee_saved_regs, args.len())?;

        if !return_type.is_void() {
            let reg_index = self.scratch.scratch_alloc();
            let return_reg = Register::Scratch(reg_index, return_type.clone(), ValueKind::Rvalue);
            writeln!(
                self.output,
                "\tmov{}    {}, {}",
                return_type.suffix(),
                return_type.return_reg(),
                return_reg.name()
            )?;
            Ok(return_reg)
        } else {
            Ok(Register::Void)
        }
    }
    fn registers_in_use(&self) -> Vec<Register> {
        let mut regs = Vec::new();

        unique(&self.saved_args).into_iter().for_each(|r| {
            regs.push(r);
        });

        self.scratch
            .registers
            .iter()
            .filter(|r| r.borrow().in_use)
            .for_each(|r| {
                regs.push(Register::Scratch(
                    Rc::clone(r),
                    NEWTypes::Pointer(Box::new(NEWTypes::Primitive(Types::Char))),
                    ValueKind::Rvalue,
                ));
            });
        regs
    }
    fn spill_regs(&mut self, callee_saved_regs: &Vec<Register>) -> Result<(), std::fmt::Error> {
        // push registers that are in use currently onto stack so they won't be overwritten during function
        for reg in callee_saved_regs.iter().by_ref() {
            writeln!(self.output, "\tpushq   {}", reg.base_name())?;
        }

        // have to 16byte align stack depending on amount of pushs before
        if !callee_saved_regs.is_empty() && callee_saved_regs.len() % 2 != 0 {
            writeln!(self.output, "\tsubq    $8,%rsp")?;
        }
        Ok(())
    }
    fn unspill_regs(
        &mut self,
        callee_saved_regs: &Vec<Register>,
        args_len: usize,
    ) -> Result<(), std::fmt::Error> {
        // undo the stack alignment from before call
        if !callee_saved_regs.is_empty() && callee_saved_regs.len() % 2 != 0 {
            writeln!(self.output, "\taddq    $8,%rsp")?;
        }

        // pop registers from before function call back to scratch registers
        for reg in callee_saved_regs.iter().rev().by_ref() {
            writeln!(self.output, "\tpopq   {}", reg.base_name())?;
        }
        // pop all argument registers from current function-call of stack
        for _ in 0..args_len {
            self.saved_args.pop();
        }

        Ok(())
    }

    fn cg_logical(
        &mut self,
        left: &Expr,
        token: &Token,
        right: &Expr,
    ) -> Result<Register, std::fmt::Error> {
        match token.token {
            TokenType::AmpAmp => self.cg_and(left, right),
            TokenType::PipePipe => self.cg_or(left, right),
            _ => unreachable!(),
        }
    }
    fn cg_or(&mut self, left: &Expr, right: &Expr) -> Result<Register, std::fmt::Error> {
        let mut left = self.execute_expr(left)?;
        left = convert_reg!(self, left, Register::Literal(..));

        let true_label = create_label(&mut self.label_index);

        // jump to true label left is true => short circuit
        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tjne    L{}",
            left.get_type().suffix(),
            left.name(),
            true_label
        )?;
        left.free();

        let mut right = self.execute_expr(right)?;
        right = convert_reg!(self, right, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if right is false we know expression is false
        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tje    L{}",
            right.get_type().suffix(),
            right.name(),
            false_label
        )?;
        right.free();

        let done_label = create_label(&mut self.label_index);
        let result = Register::Scratch(
            self.scratch.scratch_alloc(),
            NEWTypes::Primitive(Types::Int),
            ValueKind::Rvalue,
        );
        // if expression true write 1 in result and skip false label
        writeln!(
            self.output,
            "L{}:\n\tmovl    $1, {}",
            true_label,
            result.name()
        )?;
        writeln!(self.output, "\tjmp     L{}", done_label)?;

        writeln!(
            self.output,
            "L{}:\n\tmovl    $0, {}",
            false_label,
            result.name()
        )?;
        writeln!(self.output, "L{}:", done_label)?;

        Ok(result)
    }
    fn cg_and(&mut self, left: &Expr, right: &Expr) -> Result<Register, std::fmt::Error> {
        let mut left = self.execute_expr(left)?;
        left = convert_reg!(self, left, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if left is false expression is false, we jump to false label
        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tje    L{}",
            left.get_type().suffix(),
            left.name(),
            false_label
        )?;
        left.free();

        // left is true if right false jump to false label
        let mut right = self.execute_expr(right)?;
        right = convert_reg!(self, right, Register::Literal(..));
        writeln!(
            self.output,
            "\tcmp{}    $0, {}\n\tje    L{}",
            right.get_type().suffix(),
            right.name(),
            false_label
        )?;
        right.free();

        // if no prior jump was taken expression is true
        let true_label = create_label(&mut self.label_index);
        let result = Register::Scratch(
            self.scratch.scratch_alloc(),
            NEWTypes::Primitive(Types::Int),
            ValueKind::Rvalue,
        );
        writeln!(
            self.output,
            "\tmovl    $1, {}\n\tjmp    L{}",
            result.name(),
            true_label
        )?;

        writeln!(self.output, "L{}:", false_label)?;
        writeln!(self.output, "\tmovl    $0, {}", result.name())?;

        writeln!(self.output, "L{}:", true_label)?;
        Ok(result)
    }
    fn cg_unary(
        &mut self,
        token: &Token,
        right: &Expr,
        is_global: bool,
        new_type: NEWTypes,
    ) -> Result<Register, std::fmt::Error> {
        let mut reg = self.execute_expr(right)?;
        if matches!(reg, Register::Literal(..)) {
            reg = self.scratch_temp(reg)?;
        }
        match token.token {
            TokenType::Bang => self.cg_bang(reg),
            TokenType::Minus => self.cg_negate(reg),
            TokenType::Amp => self.cg_address_at(reg, is_global, true),
            TokenType::Star => self.cg_deref(reg, new_type),
            TokenType::Tilde => self.cg_bit_not(reg),
            _ => unreachable!(),
        }
    }
    fn cg_bit_not(&mut self, reg: Register) -> Result<Register, std::fmt::Error> {
        writeln!(self.output, "\tnotl    {}", reg.name())?; // typechecker guarantees integer-type

        Ok(reg)
    }
    fn cg_bang(&mut self, reg: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tcmp{} $0, {}\n\tsete %al",
            reg.get_type().suffix(),
            reg.name()
        )?; // compares reg-value with 0

        let result = Register::Scratch(
            self.scratch.scratch_alloc(),
            reg.get_type(),
            ValueKind::Rvalue,
        );
        // sets %al to 1 if comparison true and to 0 when false and then copies %al to current reg
        if reg.get_type() == NEWTypes::Primitive(Types::Char) {
            writeln!(self.output, "\tmovb %al, {}", result.name())?;
        } else {
            writeln!(
                self.output,
                "\tmovzb{} %al, {}",
                result.get_type().suffix(),
                result.name()
            )?;
        }
        reg.free();

        Ok(result)
    }
    fn cg_negate(&mut self, reg: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tneg{} {}",
            reg.get_type().suffix(),
            reg.name()
        )?;
        Ok(reg)
    }
    fn cg_address_at(
        &mut self,
        reg: Register,
        is_global: bool,
        free: bool,
    ) -> Result<Register, std::fmt::Error> {
        if is_global && matches!(reg, Register::Label(..)) {
            return Ok(reg);
        }
        let dest = Register::Scratch(
            self.scratch.scratch_alloc(),
            NEWTypes::Pointer(Box::new(reg.get_type())),
            ValueKind::Rvalue,
        );
        writeln!(self.output, "\tleaq    {}, {}", reg.name(), dest.name())?;

        if free {
            reg.free();
        }
        Ok(dest)
    }
    fn cg_deref(
        &mut self,
        mut reg: Register,
        new_type: NEWTypes,
    ) -> Result<Register, std::fmt::Error> {
        reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        reg = self.convert_to_rval(reg)?;

        reg.set_type(new_type);
        reg.set_value_kind(ValueKind::Lvalue);
        Ok(reg)
    }

    fn cg_add(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tadd{} {}, {}\n",
            right.get_type().suffix(),
            left.name(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }
    fn cg_sub(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tsub{} {}, {}\n",
            right.get_type().suffix(),
            right.name(),
            left.name()
        )?;

        right.free();
        Ok(left)
    }

    fn cg_mult(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\timul{} {}, {}\n",
            right.get_type().suffix(),
            left.name(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }

    fn cg_div(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tmov{} {}, {}",
            left.get_type().suffix(),
            left.name(),
            left.get_type().return_reg(),
        )?;
        // rax / rcx => rax
        writeln!(
            self.output,
            "\t{}\n\tidiv{} {}",
            match right.get_type().size() {
                0..=7 => "cdq",
                _ => "cqo",
            },
            right.get_type().suffix(),
            right.name()
        )?;
        // move rax(div result) into right reg
        writeln!(
            self.output,
            "\tmov{} {}, {}",
            right.get_type().suffix(),
            right.get_type().return_reg(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }

    fn cg_mod(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tmov{} {}, {}",
            left.get_type().suffix(),
            left.name(),
            left.get_type().return_reg(),
        )?;
        // rax % rcx => rdx
        writeln!(
            self.output,
            "\t{}\n\tidiv{} {}",
            match right.get_type().size() {
                0..=7 => "cdq",
                _ => "cqo",
            },
            right.get_type().suffix(),
            right.name()
        )?;
        writeln!(
            self.output,
            "\tmov{} {}, {}",
            right.get_type().suffix(),
            Register::Arg(2, right.get_type()).name(), // rdx register stores remainder
            right.name()
        )?;

        left.free();
        Ok(right)
    }

    fn cg_bit_xor(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\txor{} {}, {}\n",
            right.get_type().suffix(),
            left.name(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }
    fn cg_bit_or(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tor{} {}, {}\n",
            right.get_type().suffix(),
            left.name(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }
    fn cg_bit_and(&mut self, left: Register, right: Register) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tand{} {}, {}\n",
            right.get_type().suffix(),
            left.name(),
            right.name()
        )?;

        left.free();
        Ok(right)
    }
    fn cg_shift(
        &mut self,
        direction: &str,
        left: Register,
        right: Register,
    ) -> Result<Register, std::fmt::Error> {
        // expects shift amount to be in %cl (4th arg register)
        writeln!(
            self.output,
            "\tmov{}    {},{}",
            right.get_type().suffix(),
            right.name(),
            Register::Arg(3, right.get_type()).name()
        )?;
        right.free();

        writeln!(
            self.output,
            "\tsa{}{} %cl, {}\n",
            direction,
            left.get_type().suffix(),
            left.name()
        )?;

        Ok(left)
    }
    fn cg_comparison(
        &mut self,
        operator: &str,
        left: Register,
        right: Register,
    ) -> Result<Register, std::fmt::Error> {
        writeln!(
            self.output,
            "\tcmp{} {}, {}",
            right.get_type().suffix(),
            right.name(),
            left.name()
        )?;
        // write ZF to %al based on operator and zero extend %right_register with value of %al
        writeln!(self.output, "\t{operator} %al",)?;
        if right.get_type() == NEWTypes::Primitive(Types::Char) {
            writeln!(self.output, "\tmovb %al, {}", right.name())?;
        } else {
            writeln!(
                self.output,
                "\tmovzb{} %al, {}",
                right.get_type().suffix(),
                right.name()
            )?;
        }

        left.free();
        Ok(right)
    }

    fn cg_binary(
        &mut self,
        mut left_reg: Register,
        token: &TokenType,
        mut right_reg: Register,
    ) -> Result<Register, std::fmt::Error> {
        left_reg = convert_reg!(
            self,
            left_reg,
            Register::Literal(..) | Register::Label(..) | Register::Stack(..)
        );
        right_reg = convert_reg!(
            self,
            right_reg,
            Register::Literal(..) | Register::Label(..) | Register::Stack(..)
        );

        left_reg = self.convert_to_rval(left_reg)?;
        right_reg = self.convert_to_rval(right_reg)?;

        match token {
            TokenType::Plus => self.cg_add(left_reg, right_reg),
            TokenType::Minus => self.cg_sub(left_reg, right_reg),
            TokenType::Star => self.cg_mult(left_reg, right_reg),
            TokenType::Slash => self.cg_div(left_reg, right_reg),
            TokenType::Mod => self.cg_mod(left_reg, right_reg),
            TokenType::Xor => self.cg_bit_xor(left_reg, right_reg),
            TokenType::Pipe => self.cg_bit_or(left_reg, right_reg),
            TokenType::Amp => self.cg_bit_and(left_reg, right_reg),
            TokenType::LessLess => self.cg_shift("l", left_reg, right_reg),
            TokenType::GreaterGreater => self.cg_shift("r", left_reg, right_reg),
            TokenType::EqualEqual => self.cg_comparison("sete", left_reg, right_reg),
            TokenType::BangEqual => self.cg_comparison("setne", left_reg, right_reg),
            TokenType::Greater => self.cg_comparison("setg", left_reg, right_reg),
            TokenType::GreaterEqual => self.cg_comparison("setge", left_reg, right_reg),
            TokenType::Less => self.cg_comparison("setl", left_reg, right_reg),
            TokenType::LessEqual => self.cg_comparison("setle", left_reg, right_reg),
            _ => unreachable!(),
        }
    }
    fn convert_to_rval(&mut self, mut reg: Register) -> Result<Register, std::fmt::Error> {
        if reg.is_lval() {
            reg = self.scratch_temp(reg)?
        }
        Ok(reg)
    }
    fn scratch_temp(&mut self, reg: Register) -> Result<Register, std::fmt::Error> {
        let temp_scratch = Register::Scratch(
            self.scratch.scratch_alloc(),
            reg.get_type(),
            ValueKind::Rvalue,
        );

        writeln!(
            self.output,
            "\tmov{}    {}, {}",
            temp_scratch.get_type().suffix(),
            reg.name(),
            temp_scratch.name(),
        )?;
        reg.free();
        Ok(temp_scratch)
    }
}

fn unique(vec: &[Register]) -> Vec<Register> {
    let mut result = Vec::new();

    vec.iter().for_each(|r| {
        if !result.contains(r) {
            result.push(r.clone());
        }
    });

    result
}

pub fn align(offset: usize, type_decl: &NEWTypes) -> usize {
    let size = match type_decl {
        NEWTypes::Array { of, .. } => of.size(),
        _ => type_decl.size(),
    };
    align_by(offset, size)
}
