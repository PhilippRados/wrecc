use crate::codegen::{ir::*, register::*};
use crate::common::{environment::*, expr::*, stmt::*, token::*, types::*};
use crate::typechecker::{align_by, create_label};
use std::collections::{HashMap, VecDeque};

// converts a register into a scratch-register if it matches the pattern
macro_rules! convert_reg {
    ($self:ident,$reg:ident,$($pattern:pat_param)|+) => {
        match $reg {
            $($pattern)|+ => $self.make_temp($reg),
            _ => $reg
        }
    };
}

pub struct Compiler {
    // outputs intermediate-representation that doesn't contain physical registers yet
    output: Vec<Ir>,

    // keep track of current instruction index for live-intervals in register allocation
    instruction_counter: usize,

    // intervals for register allocation that keep track of lifetime of virtual-registers
    // (key:register-id, values: (end of lifetime, reg-type, physical register))
    live_intervals: HashMap<usize, (usize, NEWTypes, Option<TempKind>)>,

    // symbol table
    env: Vec<Symbols>,

    // when in function contains function name to access symbol table
    function_name: Option<Token>,

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
    switches: VecDeque<Vec<Option<i64>>>,

    // case/default-labels get defined in each switch and then the
    // respective case/default-statements pop them in order of appearance
    switch_labels: VecDeque<usize>,
}
impl Compiler {
    pub fn new(
        const_labels: HashMap<String, usize>,
        env: Vec<Symbols>,
        switches: Vec<Vec<Option<i64>>>,
    ) -> Self {
        Compiler {
            env,
            switches: switches.into(),
            const_labels,
            output: Vec::with_capacity(100),
            live_intervals: HashMap::with_capacity(30),
            instruction_counter: 0,
            current_bp_offset: 0,
            label_index: 0,
            function_name: None,
            saved_args: Vec::new(),
            jump_labels: Vec::new(),
            switch_labels: VecDeque::new(),
        }
    }

    pub fn translate(
        mut self,
        statements: &Vec<Stmt>,
    ) -> (
        Vec<Ir>,
        HashMap<usize, (usize, NEWTypes, Option<TempKind>)>,
        Vec<Symbols>,
    ) {
        self.cg_const_labels();
        self.cg_stmts(statements);

        (self.output, self.live_intervals, self.env)
    }
    fn write_out(&mut self, instruction: Ir) {
        self.instruction_counter += 1;
        self.output.push(instruction)
    }
    fn cg_const_labels(&mut self) {
        for (data, label_index) in self.const_labels.clone().into_iter() {
            self.write_out(Ir::StringDeclaration(label_index, data));
        }
    }
    fn cg_stmts(&mut self, statements: &Vec<Stmt>) {
        for s in statements {
            self.visit(s)
        }
    }
    fn visit(&mut self, statement: &Stmt) {
        match statement {
            Stmt::Expr(expr) => {
                let reg = self.execute_expr(expr);
                self.free(reg); // result isn't used
            }
            Stmt::Declaration(decls) => self.declaration(decls),
            Stmt::Block(statements) => self.block(statements),
            Stmt::Function(name, body) => self.function_definition(name, body),
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
            Stmt::Goto(label) => self.goto_statement(label),
            Stmt::Label(name, body) => self.label_statement(name, body),
        }
    }
    fn goto_statement(&mut self, label: &Token) {
        let function_index = self.function_name.clone().unwrap().token.get_index();
        let label_index = self
            .env
            .get_mut(function_index)
            .unwrap()
            .unwrap_func()
            .labels[&label.unwrap_string()];

        self.write_out(Ir::Jmp(label_index));
    }
    fn label_statement(&mut self, name: &Token, body: &Stmt) {
        let function_index = self.function_name.clone().unwrap().token.get_index();
        let label_index = self
            .env
            .get_mut(function_index)
            .unwrap()
            .unwrap_func()
            .labels[&name.unwrap_string()];

        self.write_out(Ir::LabelDefinition(label_index));
        self.visit(body);
    }

    fn switch_statement(&mut self, cond: &Expr, body: &Stmt) {
        let switch_labels = self.switches.pop_front().unwrap();

        let jump_labels: Vec<usize> = (0..switch_labels.len())
            .map(|_| create_label(&mut self.label_index))
            .collect();

        let cond_reg = self.execute_expr(cond);

        let mut default_label = None;
        for (kind, label) in switch_labels.iter().zip(jump_labels.clone()) {
            match kind {
                Some(case_value) => {
                    // WARN: literal can also be negative so needs type i64
                    self.write_out(Ir::Cmp(
                        Register::Literal(*case_value as usize, NEWTypes::default()),
                        cond_reg.clone(),
                    ));
                    self.write_out(Ir::JmpCond("e", label));
                }
                None => default_label = Some(label),
            }
        }
        // default label has to be jumped to at the end (even if there are cases following it) if no other cases match
        if let Some(label) = default_label {
            self.write_out(Ir::Jmp(label));
        }
        self.free(cond_reg);

        let break_label = create_label(&mut self.label_index);

        self.jump_labels.push((break_label, 0));
        self.switch_labels.append(&mut jump_labels.into());

        self.visit(body);

        self.write_out(Ir::LabelDefinition(break_label));

        self.jump_labels.pop();
    }
    fn case_statement(&mut self, body: &Stmt) {
        let label = self.switch_labels.pop_front().unwrap();

        self.write_out(Ir::LabelDefinition(label));

        self.visit(body);
    }
    fn do_statement(&mut self, body: &Stmt, cond: &Expr) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Ir::LabelDefinition(body_label));
        self.visit(body);

        self.write_out(Ir::LabelDefinition(cond_label));
        let mut cond_reg = self.execute_expr(cond);
        cond_reg = self.convert_to_rval(cond_reg);

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.write_out(Ir::JmpCond("ne", body_label));

        self.free(cond_reg);

        self.write_out(Ir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn jump_statement(&mut self, label: usize) {
        self.write_out(Ir::Jmp(label));
    }
    fn init_list(&mut self, type_decl: &NEWTypes, name: &Token, exprs: &[Expr]) {
        match self.env.get(name.token.get_index()).unwrap().is_global() {
            true => {
                self.write_out(Ir::GlobalDeclaration(name.unwrap_string()));

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
                self.declare_var(type_decl, name);
            }
        }
        let is_global = self.env.get(name.token.get_index()).unwrap().is_global();
        for e in exprs.iter() {
            match (is_global, &e.kind) {
                // init-list is assignment syntax sugar
                (true, ExprKind::Assign { r_expr, .. }) => {
                    let r_value = self.execute_expr(r_expr);

                    self.write_out(Ir::GlobalInit(r_value.get_type(), r_value.clone()));
                    self.free(r_value);
                }
                (false, _) => {
                    let reg = self.execute_expr(e);
                    self.free(reg)
                }
                _ => unreachable!(),
            };
        }
    }

    fn for_statement(
        &mut self,
        init: &Option<Box<Stmt>>,
        cond: &Option<Expr>,
        inc: &Option<Expr>,
        body: &Stmt,
    ) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);

        let inc_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, inc_label));
        if let Some(init) = init {
            self.visit(init);
        }
        self.write_out(Ir::Jmp(cond_label));
        self.write_out(Ir::LabelDefinition(body_label));

        self.visit(body);

        self.write_out(Ir::LabelDefinition(inc_label));

        if let Some(inc) = inc {
            let reg = self.execute_expr(inc);
            self.free(reg);
        }

        self.write_out(Ir::LabelDefinition(cond_label));

        match cond {
            Some(cond) => {
                let mut cond_reg = self.execute_expr(cond);
                cond_reg = self.convert_to_rval(cond_reg);

                self.write_out(Ir::Cmp(
                    Register::Literal(0, NEWTypes::default()),
                    cond_reg.clone(),
                ));
                self.write_out(Ir::JmpCond("ne", body_label));
                self.free(cond_reg);
            }
            None => self.write_out(Ir::Jmp(body_label)),
        }

        self.write_out(Ir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }
    fn while_statement(&mut self, cond: &Expr, body: &Stmt) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Ir::Jmp(cond_label));
        self.write_out(Ir::LabelDefinition(body_label));

        self.visit(body);

        self.write_out(Ir::LabelDefinition(cond_label));

        let mut cond_reg = self.execute_expr(cond);
        cond_reg = self.convert_to_rval(cond_reg);

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.write_out(Ir::JmpCond("ne", body_label));
        self.free(cond_reg);

        self.write_out(Ir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn if_statement(&mut self, cond: &Expr, then_branch: &Stmt, else_branch: &Option<Stmt>) {
        let cond_reg = self.execute_expr(cond);
        let cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let mut else_label = done_label;

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.free(cond_reg);

        if !else_branch.is_none() {
            else_label = create_label(&mut self.label_index);
        }
        self.write_out(Ir::JmpCond("e", else_label));

        self.visit(then_branch);

        if let Some(else_branch) = else_branch {
            self.write_out(Ir::Jmp(done_label));
            self.write_out(Ir::LabelDefinition(else_label));
            self.visit(else_branch);
        }
        self.write_out(Ir::LabelDefinition(done_label));
    }
    fn return_statement(&mut self, value: &Option<Expr>) {
        let function_epilogue = self
            .env
            .get_mut(self.function_name.clone().unwrap().token.get_index())
            .unwrap()
            .unwrap_func()
            .epilogue_index;
        match value {
            Some(expr) => {
                let return_value = self.execute_expr(expr);
                self.write_out(Ir::Mov(
                    return_value.clone(),
                    Register::Return(return_value.get_type()),
                ));
                self.write_out(Ir::Jmp(function_epilogue));
                self.free(return_value);
            }
            None => self.write_out(Ir::Jmp(function_epilogue)),
        }
    }
    fn declaration(&mut self, decls: &Vec<DeclarationKind>) {
        for d in decls {
            match d {
                DeclarationKind::Decl(type_decl, name) => self.declare_var(type_decl, name),
                DeclarationKind::Init(type_decl, name, expr) => {
                    let value_reg = self.execute_expr(expr);
                    self.init_var(type_decl, name, value_reg)
                }
                DeclarationKind::InitList(type_decl, name, exprs) => {
                    self.init_list(type_decl, name, exprs)
                }
                DeclarationKind::FuncDecl(..) => (),
            }
        }
    }
    fn declare_var(&mut self, type_decl: &NEWTypes, name: &Token) {
        let reg = match self.env.get(name.token.get_index()).unwrap().is_global() {
            true => {
                self.write_out(Ir::GlobalDeclaration(name.unwrap_string()));
                self.write_out(Ir::GlobalInit(
                    NEWTypes::Primitive(Types::Void),
                    Register::Literal(type_decl.size(), NEWTypes::default()),
                ));
                Register::Label(LabelRegister::Var(name.unwrap_string(), type_decl.clone()))
            }
            false => Register::Stack(StackRegister::new(
                &mut self.current_bp_offset,
                type_decl.clone(),
            )),
        };
        self.env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_var_mut()
            .set_reg(reg);
    }
    fn init_var(&mut self, type_decl: &NEWTypes, var_name: &Token, value_reg: Register) {
        let name = var_name.unwrap_string();

        match self
            .env
            .get(var_name.token.get_index())
            .unwrap()
            .is_global()
        {
            true => {
                self.write_out(Ir::GlobalDeclaration(name.clone()));
                self.write_out(Ir::GlobalInit(type_decl.clone(), value_reg));

                self.env
                    .get_mut(var_name.token.get_index())
                    .unwrap()
                    .unwrap_var_mut()
                    .set_reg(Register::Label(LabelRegister::Var(name, type_decl.clone())));
            }
            false => {
                self.declare_var(type_decl, var_name);

                let reg = self.cg_assign(
                    self.env
                        .get(var_name.token.get_index())
                        .unwrap()
                        .unwrap_var()
                        .get_reg(),
                    value_reg,
                );
                self.free(reg);
            }
        }
    }
    fn function_definition(&mut self, name: &Token, body: &Vec<Stmt>) {
        let func_symbol = self.env.get_mut(name.token.get_index()).unwrap();
        let params = func_symbol.unwrap_func().params.clone();
        let function_epilogue = create_label(&mut self.label_index);
        func_symbol.unwrap_func().epilogue_index = function_epilogue;

        assert!(func_symbol.unwrap_func().epilogue_index == function_epilogue);

        // create a label for all goto-labels inside a function
        for (_, value) in &mut func_symbol.unwrap_func().labels {
            *value = create_label(&mut self.label_index);
        }
        // save function name for return label jump
        self.function_name = Some(name.clone());
        self.current_bp_offset = 0;

        // generate function code
        self.cg_func_preamble(name, &params);
        self.cg_stmts(body);
        self.cg_func_postamble(name, function_epilogue);

        self.function_name = None;
    }
    fn cg_func_preamble(&mut self, name: &Token, params: &[(NEWTypes, Token)]) {
        let stack_size = self
            .env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_func()
            .stack_size;
        self.write_out(Ir::FuncSetup(name.clone(), stack_size));

        // initialize parameters
        for (i, (type_decl, param_name)) in params.iter().enumerate() {
            self.init_var(type_decl, param_name, Register::Arg(i, type_decl.clone()));
        }
    }
    fn cg_func_postamble(&mut self, name: &Token, epilogue_index: usize) {
        self.write_out(Ir::LabelDefinition(epilogue_index));

        let stack_size = self
            .env
            .get_mut(name.token.get_index())
            .unwrap()
            .unwrap_func()
            .stack_size;
        self.write_out(Ir::FuncTeardown(stack_size))
    }

    pub fn block(&mut self, statements: &Vec<Stmt>) {
        self.cg_stmts(statements)
    }

    fn cg_literal(&mut self, num: usize, t: Types) -> Register {
        Register::Literal(
            num,
            NEWTypes::Primitive(match t {
                Types::Char => Types::Char,
                _ if i32::try_from(num).is_ok() => Types::Int,
                _ => Types::Long,
            }),
        )
    }
    pub fn execute_expr(&mut self, ast: &Expr) -> Register {
        match &ast.kind {
            ExprKind::Binary { left, token, right } => {
                let left_reg = self.execute_expr(left);
                let right_reg = self.execute_expr(right);

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
                let left_reg = self.execute_expr(l_expr);
                let right_reg = self.execute_expr(r_expr);

                self.cg_assign(left_reg, right_reg)
            }
            ExprKind::CompoundAssign {
                l_expr,
                r_expr,
                token,
            } => self.cg_comp_assign(l_expr, token, r_expr),
            ExprKind::Ident(name) => self
                .env
                .get(name.token.get_index())
                .unwrap()
                .unwrap_var()
                .get_reg(),
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
                let expr = self.execute_expr(expr);
                self.cg_member_access(expr, member, true)
            }
            ExprKind::Ternary {
                cond,
                true_expr,
                false_expr,
                ..
            } => self.cg_ternary(cond, true_expr, false_expr),
            ExprKind::Comma { left, right } => self.cg_comma(left, right),
            ExprKind::SizeofExpr {
                value: Some(value), ..
            }
            | ExprKind::SizeofType { value } => {
                Register::Literal(*value, NEWTypes::Primitive(Types::Long))
            }
            ExprKind::Nop => Register::Void,
            _ => unreachable!("can only be sizeof but all cases covered"),
        }
    }
    fn cg_comma(&mut self, left: &Expr, right: &Expr) -> Register {
        let reg = self.execute_expr(left);
        self.free(reg);

        self.execute_expr(right)
    }

    fn cg_ternary(&mut self, cond: &Expr, true_expr: &Expr, false_expr: &Expr) -> Register {
        let mut cond_reg = self.execute_expr(cond);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let else_label = create_label(&mut self.label_index);

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.write_out(Ir::JmpCond("e", else_label));
        self.free(cond_reg);

        let result = Register::Temp(TempRegister::new(
            true_expr.clone().type_decl.unwrap(),
            self.instruction_counter,
        ));
        let true_reg = self.execute_expr(true_expr);

        // copy both expressions into result register
        self.write_out(Ir::Mov(true_reg.clone(), result.clone()));
        self.free(true_reg);

        self.write_out(Ir::Jmp(done_label));
        self.write_out(Ir::LabelDefinition(else_label));

        let false_reg = self.execute_expr(false_expr);

        self.write_out(Ir::Mov(false_reg.clone(), result.clone()));
        self.free(false_reg);

        self.write_out(Ir::LabelDefinition(done_label));

        result
    }
    fn cg_member_access(&mut self, reg: Register, member: &Token, free: bool) -> Register {
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

            let address = self.cg_address_at(reg, false, free);
            let mut result = if offset != 0 {
                self.cg_add(
                    Register::Literal(offset, NEWTypes::Primitive(Types::Int)),
                    address,
                )
            } else {
                address
            };
            result.set_type(member_type.clone());
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else if let NEWTypes::Union(s) = reg.get_type() {
            let members_iter = s.members();
            let (member_type, _) = members_iter
                .iter()
                .find(|(_, name)| name.unwrap_string() == member)
                .unwrap();

            let mut result = self.cg_address_at(reg, false, free);

            result.set_type(member_type.clone());
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else {
            unreachable!("{:?}", reg.get_type())
        }
    }
    fn cg_comp_assign(&mut self, l_expr: &Expr, token: &Token, r_expr: &Expr) -> Register {
        let l_reg = self.execute_expr(l_expr);
        let r_reg = self.execute_expr(r_expr);

        let mut temp_scratch = Register::Temp(TempRegister::new(
            l_reg.get_type(),
            self.instruction_counter,
        ));

        // have to do integer-promotion in codegen
        if (temp_scratch.get_type().size() < Types::Int.size())
            && matches!(l_reg, Register::Temp(..) | Register::Stack(..))
        {
            temp_scratch.set_type(NEWTypes::Primitive(Types::Int));
            self.write_out(Ir::Movs(l_reg.clone(), temp_scratch.clone()));
        } else {
            self.write_out(Ir::Mov(l_reg.clone(), temp_scratch.clone()));
        }
        let mut bin_reg = self.cg_binary(temp_scratch, &token.comp_to_binary(), r_reg);

        // we can do this because typechecker would catch any type-errors
        bin_reg.set_type(l_reg.get_type());
        let result = self.cg_assign(l_reg, bin_reg);

        result
    }
    fn cg_postunary(&mut self, token: &Token, expr: &Expr, by_amount: &usize) -> Register {
        let reg = self.execute_expr(expr);
        let mut return_reg = Register::Temp(TempRegister::new(
            expr.type_decl.clone().unwrap(),
            self.instruction_counter,
        ));

        // assign value to return-register before binary operation
        // have to do integer-promotion in codegen
        if return_reg.get_type().size() < Types::Int.size() {
            return_reg.set_type(NEWTypes::Primitive(Types::Int));
            self.write_out(Ir::Movs(reg.clone(), return_reg.clone()));
        } else {
            self.write_out(Ir::Mov(reg.clone(), return_reg.clone()));
        }

        let by_amount = Register::Literal(*by_amount, NEWTypes::default());
        match token.token {
            TokenType::PlusPlus => self.write_out(Ir::Add(by_amount, reg.clone())),
            TokenType::MinusMinus => self.write_out(Ir::Sub(by_amount, reg.clone())),
            _ => unreachable!(),
        };
        self.free(reg);

        return_reg
    }
    fn cg_string(&mut self, name: String) -> Register {
        Register::Label(LabelRegister::String(self.const_labels[&name]))
    }
    fn cg_scale_down(&mut self, expr: &Expr, by_amount: &usize) -> Register {
        let value_reg = self.execute_expr(expr);
        let value_reg = convert_reg!(self, value_reg, Register::Literal(..));

        // right shift number, equivalent to division (works bc type-size is 2^n)
        self.write_out(Ir::Shift(
            "r",
            Register::Literal(*by_amount, NEWTypes::default()),
            value_reg.clone(),
        ));

        value_reg
    }
    fn cg_scale_up(&mut self, expr: &Expr, by_amount: &usize) -> Register {
        let value_reg = self.execute_expr(expr);

        let value_reg = self.cg_mult(
            Register::Literal(*by_amount, NEWTypes::Primitive(Types::Int)),
            value_reg,
        );

        value_reg
    }
    fn cg_cast_down(&mut self, expr: &Expr, new_type: NEWTypes) -> Register {
        let mut value_reg = self.execute_expr(expr);
        value_reg.set_type(new_type);

        value_reg
    }
    fn cg_cast_up(&mut self, expr: &Expr, new_type: NEWTypes) -> Register {
        let mut value_reg = self.execute_expr(expr);

        if matches!(
            value_reg,
            Register::Temp(..) | Register::Stack(..) | Register::Label(..)
        ) {
            let dest_reg = Register::Temp(TempRegister::new(
                new_type.clone(),
                self.instruction_counter,
            ));

            self.write_out(Ir::Movs(value_reg.clone(), dest_reg.clone()));

            self.free(value_reg);
            dest_reg
        } else {
            value_reg.set_type(new_type);
            value_reg
        }
    }
    fn cg_assign(&mut self, l_value: Register, r_value: Register) -> Register {
        if let NEWTypes::Struct(s) = l_value.get_type() {
            // when assigning structs have to assign each member
            for m in s.members().iter() {
                let member_token = Token::default(TokenType::Ident(m.1.unwrap_string(), 0));
                let member_lvalue = self.cg_member_access(l_value.clone(), &member_token, false);
                let member_rvalue = self.cg_member_access(r_value.clone(), &member_token, false);

                let reg = self.cg_assign(member_lvalue, member_rvalue);
                self.free(reg);
            }
            self.free(r_value);
            l_value
        } else {
            // can't move from mem to mem so make temp scratch-register
            let r_value = convert_reg!(self, r_value, Register::Stack(..) | Register::Label(..));
            let r_value = self.convert_to_rval(r_value);

            self.write_out(Ir::Mov(r_value.clone(), l_value.clone()));
            self.free(r_value);
            l_value
        }
    }
    fn cg_call(&mut self, callee: &Expr, args: &Vec<Expr>, return_type: NEWTypes) -> Register {
        let func_name = match &callee.kind {
            ExprKind::Ident(func_name) => func_name.unwrap_string(),
            _ => unreachable!("typechecker"),
        };
        // TODO: implement args by pushing on stack
        assert!(args.len() <= 6, "function cant have more than 6 args");

        let saved_args = unique(&self.saved_args).into_iter().collect();
        self.save_args(&saved_args);

        // moving the arguments into their designated registers
        for (i, expr) in args.iter().enumerate().rev() {
            let reg = self.execute_expr(expr);

            let arg = Register::Arg(i, expr.type_decl.clone().unwrap());
            self.write_out(Ir::Mov(reg.clone(), arg.clone()));
            self.free(reg);

            self.saved_args.push(arg);
        }

        self.write_out(Ir::Call(func_name));

        self.restore_args(&saved_args, args.len());

        if !return_type.is_void() {
            let return_reg = Register::Temp(TempRegister::new(
                return_type.clone(),
                self.instruction_counter,
            ));
            self.write_out(Ir::Mov(Register::Return(return_type), return_reg.clone()));
            return_reg
        } else {
            Register::Void
        }
    }
    // can only save args in this pass because scratch-registers are first used in register-allocation pass
    fn save_args(&mut self, args: &Vec<Register>) {
        // push registers that are in use currently onto stack so they won't be overwritten during function
        for reg in args.iter() {
            self.write_out(Ir::Push(reg.clone()));
        }

        // have to 16byte align stack depending on amount of pushs before
        if !args.is_empty() && args.len() % 2 != 0 {
            self.write_out(Ir::SubSp(8));
        }
    }
    fn restore_args(&mut self, args: &Vec<Register>, args_len: usize) {
        // undo the stack alignment from before call
        if !args.is_empty() && args.len() % 2 != 0 {
            self.write_out(Ir::AddSp(8));
        }

        // pop registers from before function call back to scratch registers
        for reg in args.iter().rev().by_ref() {
            self.write_out(Ir::Pop(reg.clone()));
        }
        // pop all argument registers from current function-call of stack
        for _ in 0..args_len {
            self.saved_args.pop();
        }
    }

    fn cg_logical(&mut self, left: &Expr, token: &Token, right: &Expr) -> Register {
        match token.token {
            TokenType::AmpAmp => self.cg_and(left, right),
            TokenType::PipePipe => self.cg_or(left, right),
            _ => unreachable!(),
        }
    }
    fn cg_or(&mut self, left: &Expr, right: &Expr) -> Register {
        let mut left = self.execute_expr(left);
        left = convert_reg!(self, left, Register::Literal(..));

        let true_label = create_label(&mut self.label_index);

        // jump to true label left is true => short circuit
        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            left.clone(),
        ));
        self.write_out(Ir::JmpCond("ne", true_label));
        self.free(left);

        let mut right = self.execute_expr(right);
        right = convert_reg!(self, right, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if right is false we know expression is false
        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            right.clone(),
        ));
        self.write_out(Ir::JmpCond("e", false_label));
        self.free(right);

        let done_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            NEWTypes::Primitive(Types::Int),
            self.instruction_counter,
        ));
        // if expression true write 1 in result and skip false label
        self.write_out(Ir::LabelDefinition(true_label));
        self.write_out(Ir::Mov(
            Register::Literal(1, NEWTypes::default()),
            result.clone(),
        ));

        self.write_out(Ir::Jmp(done_label));

        self.write_out(Ir::LabelDefinition(false_label));
        self.write_out(Ir::Mov(
            Register::Literal(0, NEWTypes::default()),
            result.clone(),
        ));

        self.write_out(Ir::LabelDefinition(done_label));

        result
    }
    fn cg_and(&mut self, left: &Expr, right: &Expr) -> Register {
        let left = self.execute_expr(left);
        let left = convert_reg!(self, left, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if left is false expression is false, we jump to false label
        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            left.clone(),
        ));
        self.write_out(Ir::JmpCond("e", false_label));
        self.free(left);

        // left is true if right false jump to false label
        let right = self.execute_expr(right);
        let right = convert_reg!(self, right, Register::Literal(..));

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            right.clone(),
        ));
        self.write_out(Ir::JmpCond("e", false_label));
        self.free(right);

        // if no prior jump was taken expression is true
        let true_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            NEWTypes::Primitive(Types::Int),
            self.instruction_counter,
        ));
        self.write_out(Ir::Mov(
            Register::Literal(1, NEWTypes::default()),
            result.clone(),
        ));
        self.write_out(Ir::Jmp(true_label));

        self.write_out(Ir::LabelDefinition(false_label));
        self.write_out(Ir::Mov(
            Register::Literal(0, NEWTypes::default()),
            result.clone(),
        ));

        self.write_out(Ir::LabelDefinition(true_label));

        result
    }
    fn cg_unary(
        &mut self,
        token: &Token,
        right: &Expr,
        is_global: bool,
        new_type: NEWTypes,
    ) -> Register {
        let mut reg = self.execute_expr(right);
        // can't have literal as only operand to unary expression
        reg = convert_reg!(self, reg, Register::Literal(..));

        match token.token {
            TokenType::Bang => self.cg_bang(reg),
            TokenType::Minus => self.cg_negate(reg),
            TokenType::Amp => self.cg_address_at(reg, is_global, true),
            TokenType::Star => self.cg_deref(reg, new_type),
            TokenType::Tilde => self.cg_bit_not(reg),
            _ => unreachable!(),
        }
    }
    fn cg_bit_not(&mut self, reg: Register) -> Register {
        // can't overwrite variable
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        self.write_out(Ir::Not(reg.clone()));

        reg
    }
    fn cg_bang(&mut self, reg: Register) -> Register {
        // compares reg-value with 0
        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            reg.clone(),
        ));
        self.write_out(Ir::Set("sete"));

        let result = Register::Temp(TempRegister::new(reg.get_type(), self.instruction_counter));

        // sets %al to 1 if comparison true and to 0 when false and then copies %al to current reg
        if reg.get_type() == NEWTypes::Primitive(Types::Char) {
            self.write_out(Ir::Mov(
                Register::Return(NEWTypes::Primitive(Types::Char)),
                result.clone(),
            ));
        } else {
            self.write_out(Ir::Movz(
                Register::Return(NEWTypes::Primitive(Types::Char)),
                result.clone(),
            ));
        }
        self.free(reg);

        result
    }
    fn cg_negate(&mut self, reg: Register) -> Register {
        // can't overwrite variable
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        self.write_out(Ir::Neg(reg.clone()));
        reg
    }
    fn cg_address_at(&mut self, reg: Register, is_global: bool, free: bool) -> Register {
        if is_global && matches!(reg, Register::Label(..)) {
            return reg;
        }
        let dest = Register::Temp(TempRegister::new(
            NEWTypes::Pointer(Box::new(reg.get_type())),
            self.instruction_counter,
        ));
        self.write_out(Ir::Load(reg.clone(), dest.clone()));

        if free {
            self.free(reg);
        }

        dest
    }
    fn cg_deref(&mut self, reg: Register, new_type: NEWTypes) -> Register {
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        let mut reg = self.convert_to_rval(reg);

        reg.set_type(new_type);
        reg.set_value_kind(ValueKind::Lvalue);

        reg
    }

    fn cg_add(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Add(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_sub(&mut self, left: Register, right: Register) -> Register {
        let left = convert_reg!(
            self,
            left,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );

        self.write_out(Ir::Sub(right.clone(), left.clone()));

        self.free(right);
        left
    }

    fn cg_mult(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Imul(left.clone(), right.clone()));

        self.free(left);
        right
    }

    fn cg_div(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Mov(left.clone(), Register::Return(left.get_type())));
        // rax / rcx => rax
        self.write_out(Ir::Idiv(right.clone()));

        // move rax(div result) into right reg
        self.write_out(Ir::Mov(Register::Return(right.get_type()), right.clone()));

        self.free(left);
        right
    }

    fn cg_mod(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Mov(left.clone(), Register::Return(left.get_type())));

        // rax % rcx => rdx
        self.write_out(Ir::Idiv(right.clone()));
        // rdx(3nd Argument register) stores remainder
        self.write_out(Ir::Mov(Register::Arg(2, right.get_type()), right.clone()));

        self.free(left);
        right
    }

    fn cg_bit_xor(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Xor(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_bit_or(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Or(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_bit_and(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::And(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_shift(&mut self, direction: &'static str, left: Register, right: Register) -> Register {
        // destination register has to be reg or mem
        let left = self.make_temp(left);

        // expects shift amount to be in %cl (4th arg register)
        self.write_out(Ir::Mov(right.clone(), Register::Arg(3, right.get_type())));
        self.free(right);

        self.write_out(Ir::Shift(
            direction,
            Register::Arg(3, NEWTypes::Primitive(Types::Char)),
            left.clone(),
        ));

        left
    }
    fn cg_comparison(
        &mut self,
        operator: &'static str,
        left: Register,
        right: Register,
    ) -> Register {
        let left = convert_reg!(
            self,
            left,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Cmp(right.clone(), left.clone()));
        self.write_out(Ir::Set(operator));

        // write ZF to %al based on operator and zero extend %right_register with value of %al
        if right.get_type() == NEWTypes::Primitive(Types::Char) {
            self.write_out(Ir::Mov(
                Register::Return(NEWTypes::Primitive(Types::Char)),
                right.clone(),
            ));
        } else {
            self.write_out(Ir::Movz(
                Register::Return(NEWTypes::Primitive(Types::Char)),
                right.clone(),
            ));
        }

        self.free(left);
        right
    }

    fn cg_binary(
        &mut self,
        left_reg: Register,
        token: &TokenType,
        right_reg: Register,
    ) -> Register {
        let (left_reg, right_reg) = (
            self.convert_to_rval(left_reg),
            self.convert_to_rval(right_reg),
        );

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
    fn convert_to_rval(&mut self, reg: Register) -> Register {
        if reg.is_lval() {
            self.make_temp(reg)
        } else {
            reg
        }
    }
    fn make_temp(&mut self, reg: Register) -> Register {
        let result = Register::Temp(TempRegister::new(reg.get_type(), self.instruction_counter));

        self.write_out(Ir::Mov(reg.clone(), result.clone()));
        self.free(reg);

        result
    }
    fn free(&mut self, reg: Register) {
        if let Register::Temp(reg) = reg {
            self.live_intervals
                .insert(reg.id, (self.instruction_counter, reg.type_decl, None));
        }
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
