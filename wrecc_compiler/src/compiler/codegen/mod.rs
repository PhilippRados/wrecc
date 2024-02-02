pub mod lir;
pub mod register;
pub mod register_allocation;

use crate::compiler::codegen::{lir::*, register::*, register_allocation::*};
use crate::compiler::common::{token::*, types::*};
use crate::compiler::typechecker::mir::{decl::*, expr::*, stmt::*};
use crate::compiler::typechecker::{align_by, create_label};

use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

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
    output: Vec<Lir>,

    // keep track of current instruction for live-intervals in register allocation
    instr_counter: usize,

    // key for temporary register into live-intervals
    interval_counter: usize,

    // intervals for register allocation that keep track of lifetime of virtual-registers
    // (key:register-id, values: (end of lifetime, reg-type, physical register))
    live_intervals: HashMap<usize, IntervalEntry>,

    // index of current label
    label_index: usize,

    // map containing Strings and their corresponding label-index
    const_labels: HashMap<String, usize>,

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
    pub fn new(const_labels: HashMap<String, usize>, switches: Vec<Vec<Option<i64>>>) -> Self {
        Compiler {
            switches: switches.into(),
            const_labels,
            output: Vec::with_capacity(100),
            live_intervals: HashMap::with_capacity(30),
            interval_counter: 0,
            instr_counter: 0,
            current_bp_offset: 0,
            label_index: 0,
            jump_labels: Vec::new(),
            switch_labels: VecDeque::new(),
        }
    }

    pub fn translate(
        mut self,
        external_decls: Vec<ExternalDeclaration>,
    ) -> (Vec<Lir>, HashMap<usize, IntervalEntry>) {
        self.cg_const_labels();
        self.cg_external_decls(external_decls);

        (self.output, self.live_intervals)
    }
    fn write_out(&mut self, instruction: Lir) {
        self.instr_counter += 1;
        self.output.push(instruction)
    }
    fn cg_const_labels(&mut self) {
        for (data, label_index) in self.const_labels.clone().into_iter() {
            self.write_out(Lir::StringDeclaration(label_index, data));
        }
    }
    fn cg_external_decls(&mut self, external_decls: Vec<ExternalDeclaration>) {
        for decl in external_decls {
            self.visit_decl(decl)
        }
    }
    fn cg_stmts(&mut self, statements: Vec<Stmt>) {
        for stmt in statements {
            self.visit_stmt(stmt)
        }
    }
    fn visit_decl(&mut self, external_decl: ExternalDeclaration) {
        match external_decl {
            ExternalDeclaration::Declaration(decls) => self.declaration(decls),
            ExternalDeclaration::Function(name, func_symbol, params, body) => {
                self.function_definition(name, func_symbol, params, body)
            }
        }
    }
    fn visit_stmt(&mut self, statement: Stmt) {
        match statement {
            Stmt::Expr(expr) => {
                let reg = self.execute_expr(expr);
                self.free(reg); // result isn't used
            }
            Stmt::Declaration(decls) => self.declaration(decls),
            Stmt::Block(statements) => self.block(statements),
            Stmt::Return(func_symbol, expr) => self.return_statement(func_symbol, expr),
            Stmt::If(cond, then_branch, else_branch) => {
                self.if_statement(cond, *then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(cond, *body),
            Stmt::Do(body, cond) => self.do_statement(*body, cond),
            Stmt::For(init, cond, inc, body) => self.for_statement(init, cond, inc, *body),
            Stmt::Break => self.jump_statement(self.jump_labels.last().expect("typechecker").0),
            Stmt::Continue => self.jump_statement(self.jump_labels.last().expect("typechecker").1),
            Stmt::Switch(cond, body) => self.switch_statement(cond, *body),
            Stmt::Case(body) | Stmt::Default(body) => self.case_statement(*body),
            Stmt::Goto(func_symbol, label) => self.goto_statement(func_symbol, label),
            Stmt::Label(func_symbol, name, body) => self.label_statement(func_symbol, name, *body),
        }
    }
    fn goto_statement(&mut self, func_symbol: FuncSymbol, label: String) {
        let label_index = func_symbol.borrow().unwrap_func().labels[&label];

        self.write_out(Lir::Jmp(label_index));
    }
    fn label_statement(&mut self, func_symbol: FuncSymbol, name: String, body: Stmt) {
        let label_index = func_symbol.borrow().unwrap_func().labels[&name];

        self.write_out(Lir::LabelDefinition(label_index));
        self.visit_stmt(body);
    }

    fn switch_statement(&mut self, cond: Expr, body: Stmt) {
        let switch_labels = self.switches.pop_front().unwrap();

        let jump_labels: Vec<usize> = (0..switch_labels.len())
            .map(|_| create_label(&mut self.label_index))
            .collect();

        let mut cond_reg = self.execute_expr(cond);

        let mut default_label = None;
        for (kind, label) in switch_labels.iter().zip(jump_labels.clone()) {
            match kind {
                Some(case_value) => {
                    // WARN: literal can also be negative so needs type i64
                    cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

                    self.write_out(Lir::Cmp(
                        Register::Literal(*case_value, Type::Primitive(Primitive::Int)),
                        cond_reg.clone(),
                    ));
                    self.write_out(Lir::JmpCond("e", label));
                }
                None => default_label = Some(label),
            }
        }
        // default label has to be jumped to at the end (even if there are cases following it) if no other cases match
        if let Some(label) = default_label {
            self.write_out(Lir::Jmp(label));
        }
        self.free(cond_reg);

        let break_label = create_label(&mut self.label_index);

        self.jump_labels.push((break_label, 0));
        self.switch_labels.append(&mut jump_labels.into());

        self.visit_stmt(body);

        self.write_out(Lir::LabelDefinition(break_label));

        self.jump_labels.pop();
    }
    fn case_statement(&mut self, body: Stmt) {
        let label = self.switch_labels.pop_front().unwrap();

        self.write_out(Lir::LabelDefinition(label));

        self.visit_stmt(body);
    }
    fn do_statement(&mut self, body: Stmt, cond: Expr) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Lir::LabelDefinition(body_label));
        self.visit_stmt(body);

        self.write_out(Lir::LabelDefinition(cond_label));
        let mut cond_reg = self.execute_expr(cond);
        cond_reg = self.convert_to_rval(cond_reg);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            cond_reg.clone(),
        ));
        self.write_out(Lir::JmpCond("ne", body_label));

        self.free(cond_reg);

        self.write_out(Lir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn jump_statement(&mut self, label: usize) {
        self.write_out(Lir::Jmp(label));
    }
    fn for_statement(
        &mut self,
        init: Option<Box<Stmt>>,
        cond: Option<Expr>,
        inc: Option<Expr>,
        body: Stmt,
    ) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);

        let inc_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, inc_label));
        if let Some(init) = init {
            self.visit_stmt(*init);
        }
        self.write_out(Lir::Jmp(cond_label));
        self.write_out(Lir::LabelDefinition(body_label));

        self.visit_stmt(body);

        self.write_out(Lir::LabelDefinition(inc_label));

        if let Some(inc) = inc {
            let reg = self.execute_expr(inc);
            self.free(reg);
        }

        self.write_out(Lir::LabelDefinition(cond_label));

        match cond {
            Some(cond) => {
                let mut cond_reg = self.execute_expr(cond);
                cond_reg = self.convert_to_rval(cond_reg);
                cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

                self.write_out(Lir::Cmp(
                    Register::Literal(0, Type::Primitive(Primitive::Int)),
                    cond_reg.clone(),
                ));
                self.write_out(Lir::JmpCond("ne", body_label));
                self.free(cond_reg);
            }
            None => self.write_out(Lir::Jmp(body_label)),
        }

        self.write_out(Lir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }
    fn while_statement(&mut self, cond: Expr, body: Stmt) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Lir::Jmp(cond_label));
        self.write_out(Lir::LabelDefinition(body_label));

        self.visit_stmt(body);

        self.write_out(Lir::LabelDefinition(cond_label));

        let mut cond_reg = self.execute_expr(cond);
        cond_reg = self.convert_to_rval(cond_reg);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            cond_reg.clone(),
        ));
        self.write_out(Lir::JmpCond("ne", body_label));
        self.free(cond_reg);

        self.write_out(Lir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn if_statement(&mut self, cond: Expr, then_branch: Stmt, else_branch: Option<Box<Stmt>>) {
        let cond_reg = self.execute_expr(cond);
        let cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let mut else_label = done_label;

        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            cond_reg.clone(),
        ));
        self.free(cond_reg);

        if else_branch.is_some() {
            else_label = create_label(&mut self.label_index);
        }
        self.write_out(Lir::JmpCond("e", else_label));

        self.visit_stmt(then_branch);

        if let Some(else_branch) = else_branch {
            self.write_out(Lir::Jmp(done_label));
            self.write_out(Lir::LabelDefinition(else_label));
            self.visit_stmt(*else_branch);
        }
        self.write_out(Lir::LabelDefinition(done_label));
    }
    fn return_statement(&mut self, func_symbol: FuncSymbol, value: Option<Expr>) {
        let function_epilogue = func_symbol.borrow().unwrap_func().epilogue_index;

        match value {
            Some(expr) => {
                let return_value = self.execute_expr(expr);
                self.write_out(Lir::Mov(
                    return_value.clone(),
                    Register::Return(return_value.get_type()),
                ));
                self.write_out(Lir::Jmp(function_epilogue));
                self.free(return_value);
            }
            None => self.write_out(Lir::Jmp(function_epilogue)),
        }
    }
    fn declaration(&mut self, declarators: Vec<Declarator>) {
        for declarator in declarators {
            let var_symbol = declarator.entry.borrow().unwrap_var().clone();

            if declarator.name == var_symbol.token {
                if var_symbol.is_global {
                    self.declare_global_var(
                        declarator.name.unwrap_string(),
                        var_symbol.type_decl,
                        declarator.entry,
                        declarator.init,
                    )
                } else {
                    self.declare_var(declarator.entry, declarator.init)
                }
            }
        }
    }
    fn declare_global_var(
        &mut self,
        name: String,
        type_decl: Type,
        var_symbol: VarSymbol,
        init: Option<Init>,
    ) {
        self.write_out(Lir::GlobalDeclaration(name.clone(), type_decl.is_ptr()));

        if let Some(init) = init {
            self.init_global_var(name, type_decl, var_symbol, init);
        } else {
            self.write_out(Lir::GlobalInit(
                Type::Primitive(Primitive::Void),
                StaticRegister::Literal(type_decl.size() as i64, Type::Primitive(Primitive::Int)),
            ));
            let reg = Register::Label(LabelRegister::Var(name, type_decl));

            var_symbol.borrow_mut().unwrap_var_mut().set_reg(reg);
        }
    }
    fn declare_var(&mut self, var_symbol: VarSymbol, init: Option<Init>) {
        let type_decl = var_symbol.borrow().unwrap_var().type_decl.clone();
        let size = align(type_decl.size(), &type_decl);

        let reg = Register::Stack(StackRegister::new(&mut self.current_bp_offset, type_decl));
        var_symbol.borrow_mut().unwrap_var_mut().set_reg(reg);

        if let Some(init) = init {
            match init {
                Init::Scalar(expr) => self.init_scalar(var_symbol, expr, 0),
                Init::Aggr(list) => {
                    // first overwrite all entries with 0
                    self.clear_mem(Rc::clone(&var_symbol), size);

                    for (expr, offset) in list {
                        self.init_scalar(Rc::clone(&var_symbol), expr, offset)
                    }
                }
            }
        }
    }
    fn init_global_var(&mut self, name: String, type_decl: Type, var_symbol: VarSymbol, init: Init) {
        var_symbol
            .borrow_mut()
            .unwrap_var_mut()
            .set_reg(Register::Label(LabelRegister::Var(name, type_decl.clone())));

        match init {
            Init::Scalar(expr) => {
                let value_reg = self.execute_global_expr(expr);

                self.write_out(Lir::GlobalInit(type_decl, value_reg));
            }
            Init::Aggr(list) => {
                let mut size = type_decl.size() as i64;
                let mut prev_offset: i64 = 0;

                for (expr, offset) in list {
                    let value_reg = self.execute_global_expr(expr);
                    let value_type = value_reg.get_type();

                    // fill gap in offset with zero
                    let diff = offset as i64 - prev_offset;
                    if diff != 0 {
                        self.write_out(Lir::GlobalInit(
                            Type::Primitive(Primitive::Void),
                            StaticRegister::Literal(diff, Type::Primitive(Primitive::Int)),
                        ));
                        size -= diff;
                    }

                    size -= value_type.size() as i64;
                    prev_offset = offset as i64 + value_type.size() as i64;

                    self.write_out(Lir::GlobalInit(value_type, value_reg));
                }

                // fill remaining fields in type
                if size > 0 {
                    self.write_out(Lir::GlobalInit(
                        Type::Primitive(Primitive::Void),
                        StaticRegister::Literal(size, Type::Primitive(Primitive::Int)),
                    ));
                }
            }
        }
    }

    fn init_scalar(&mut self, var_symbol: VarSymbol, expr: Expr, offset: usize) {
        let value_reg = self.execute_expr(expr);
        let mut var_reg = var_symbol.borrow().unwrap_var().get_reg();

        var_reg.set_type(value_reg.get_type());
        if let Register::Stack(stack_reg) = &mut var_reg {
            stack_reg.bp_offset -= offset;

            let value_reg = self.cg_assign(var_reg, value_reg);
            self.free(value_reg);
        } else {
            unreachable!("local variables can only be located on stack")
        }
    }

    fn clear_mem(&mut self, var_symbol: VarSymbol, amount: usize) {
        // writes 0 to stack until amount == 0
        // eax value that gets written
        // ecx amount
        // rdi at memory pos
        let var_reg = var_symbol.borrow().unwrap_var().get_reg();

        // TODO: can be optimized by writing 8Bytes (instead of 1) per repetition but that requires extra logic when amount and size don't align
        let eax_reg = Register::Return(Type::Primitive(Primitive::Char));
        let ecx_reg = Register::Arg(ArgRegister::new(
            3,
            Type::Primitive(Primitive::Int),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        let rdi_reg = Register::Arg(ArgRegister::new(
            0,
            Type::Primitive(Primitive::Long),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Lir::Mov(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            eax_reg.clone(),
        ));
        self.write_out(Lir::Mov(
            Register::Literal(amount as i64, Type::Primitive(Primitive::Int)),
            ecx_reg.clone(),
        ));
        self.write_out(Lir::Load(var_reg, rdi_reg.clone()));
        self.write_out(Lir::Rep);

        self.free(eax_reg);
        self.free(ecx_reg);
        self.free(rdi_reg);
    }

    fn init_arg(&mut self, var_symbol: VarSymbol, arg_reg: Register) {
        self.declare_var(Rc::clone(&var_symbol), None);

        let reg = self.cg_assign(var_symbol.borrow().unwrap_var().get_reg(), arg_reg);
        self.free(reg);
    }

    fn function_definition(
        &mut self,
        name: String,
        func_symbol: FuncSymbol,
        params: Vec<VarSymbol>,
        body: Vec<Stmt>,
    ) {
        let function_epilogue = create_label(&mut self.label_index);
        func_symbol.borrow_mut().unwrap_func_mut().epilogue_index = function_epilogue;

        // create a label for all goto-labels inside a function
        for value in func_symbol.borrow_mut().unwrap_func_mut().labels.values_mut() {
            *value = create_label(&mut self.label_index);
        }

        self.current_bp_offset = 0;

        // generate function code
        self.cg_func_preamble(Rc::clone(&func_symbol), params, name);
        self.cg_stmts(body);
        self.cg_func_postamble(func_symbol, function_epilogue);
    }
    fn cg_func_preamble(&mut self, func_symbol: FuncSymbol, params: Vec<VarSymbol>, name: String) {
        let stack_size = func_symbol.borrow().unwrap_func().stack_size;
        self.write_out(Lir::FuncSetup(name, stack_size));

        // initialize parameters
        for (i, param_symbol) in params.into_iter().enumerate() {
            let type_decl = param_symbol.borrow().unwrap_var().type_decl.clone();
            if i < ARG_REGS.len() {
                let arg = Register::Arg(ArgRegister::new(
                    i,
                    type_decl,
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                self.init_arg(param_symbol, arg);
            } else {
                // if not in designated arg-register get from stack
                let reg = Register::Temp(TempRegister::new(
                    type_decl,
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                let pushed = Register::Stack(StackRegister::new_pushed(i));

                self.write_out(Lir::Mov(pushed, reg.clone()));
                self.init_arg(param_symbol, reg);
            }
        }
    }
    fn cg_func_postamble(&mut self, func_symbol: FuncSymbol, epilogue_index: usize) {
        self.write_out(Lir::LabelDefinition(epilogue_index));

        let stack_size = func_symbol.borrow().unwrap_func().stack_size;
        self.write_out(Lir::FuncTeardown(stack_size))
    }

    pub fn block(&mut self, statements: Vec<Stmt>) {
        self.cg_stmts(statements)
    }

    fn cg_literal(&mut self, n: i64, type_decl: Type) -> Register {
        let literal_reg = Register::Literal(n, type_decl);

        // 64bit literals are only allowed to move to scratch-register
        if let Primitive::Long = integer_type(n) {
            let scratch_reg = Register::Temp(TempRegister::new(
                literal_reg.get_type(),
                &mut self.interval_counter,
                self.instr_counter,
            ));
            self.write_out(Lir::Mov(literal_reg, scratch_reg.clone()));
            scratch_reg
        } else {
            literal_reg
        }
    }
    fn execute_global_expr(&mut self, expr: Expr) -> StaticRegister {
        match expr.kind {
            ExprKind::String(name) => {
                StaticRegister::Label(LabelRegister::String(self.const_labels[&name]))
            }
            ExprKind::Literal(n) => StaticRegister::Literal(n, expr.type_decl),
            ExprKind::Cast { new_type, expr, .. } => {
                let mut reg = self.execute_global_expr(*expr);
                reg.set_type(new_type);
                reg
            }
            ExprKind::ScaleUp { by, expr } => {
                if let StaticRegister::Literal(n, type_decl) = self.execute_global_expr(*expr) {
                    let n = n * by as i64;
                    let scaled_type = integer_type(n);

                    let type_decl = if type_decl.size() < scaled_type.size() {
                        Type::Primitive(scaled_type)
                    } else {
                        type_decl
                    };

                    StaticRegister::Literal(n, type_decl)
                } else {
                    unreachable!("can only scale literal value")
                }
            }
            ExprKind::Unary { operator, right } => {
                let mut reg = self.execute_global_expr(*right);
                match operator {
                    TokenKind::Amp => reg.set_type(Type::Pointer(Box::new(reg.get_type()))),
                    TokenKind::Star => reg.set_type(expr.type_decl),
                    _ => unreachable!("non-constant unary expression"),
                }
                reg
            }
            ExprKind::MemberAccess { expr, member } => {
                let mut reg = self.execute_global_expr(*expr);

                match reg.get_type() {
                    Type::Struct(s) => {
                        let offset = s.member_offset(&member);
                        let member_type = s.member_type(&member);

                        reg.set_type(member_type);
                        match reg {
                            StaticRegister::Label(label_reg) => {
                                StaticRegister::LabelOffset(label_reg, offset as i64, TokenKind::Plus)
                            }
                            StaticRegister::LabelOffset(reg, existant_offset, _) => {
                                let offset = existant_offset + offset as i64;
                                if offset < 0 {
                                    StaticRegister::LabelOffset(reg, offset.abs(), TokenKind::Minus)
                                } else {
                                    StaticRegister::LabelOffset(reg, offset, TokenKind::Plus)
                                }
                            }
                            _ => unreachable!("Literal can't be struct address"),
                        }
                    }
                    Type::Union(s) => {
                        let member_type = s.member_type(&member);
                        reg.set_type(member_type);
                        reg
                    }
                    _ => unreachable!("{:?}", reg.get_type()),
                }
            }
            ExprKind::Binary { left, operator, right } => {
                let left = self.execute_global_expr(*left);
                let right = self.execute_global_expr(*right);

                match (left, right) {
                    (StaticRegister::Label(reg), StaticRegister::Literal(n, _))
                    | (StaticRegister::Literal(n, _), StaticRegister::Label(reg)) => {
                        StaticRegister::LabelOffset(reg, n, operator)
                    }

                    (StaticRegister::LabelOffset(reg, offset, _), StaticRegister::Literal(n, _))
                    | (StaticRegister::Literal(n, _), StaticRegister::LabelOffset(reg, offset, _)) => {
                        let offset = n + offset;
                        if offset < 0 {
                            StaticRegister::LabelOffset(reg, offset.abs(), TokenKind::Minus)
                        } else {
                            StaticRegister::LabelOffset(reg, offset, TokenKind::Plus)
                        }
                    }
                    _ => unreachable!(),
                }
            }
            ExprKind::Ident(var_symbol) => {
                // plain ident isn't compile-time-constant (this gets caught in typechecker)
                // but is needed to evaluate address-constants
                if let Register::Label(reg) = var_symbol.borrow().unwrap_var().get_reg() {
                    StaticRegister::Label(reg)
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!("non global-constant expr"),
        }
    }
    pub fn execute_expr(&mut self, expr: Expr) -> Register {
        match expr.kind {
            ExprKind::Binary { left, operator, right } => {
                let left_reg = self.execute_expr(*left);
                let right_reg = self.execute_expr(*right);

                self.cg_binary(left_reg, &operator, right_reg)
            }
            ExprKind::Literal(n) => self.cg_literal(n, expr.type_decl),
            ExprKind::Grouping { expr } => self.execute_expr(*expr),
            ExprKind::Unary { operator, right } => self.cg_unary(operator, *right, expr.type_decl),
            ExprKind::Logical { left, operator, right } => self.cg_logical(*left, operator, *right),
            ExprKind::Comparison { left, operator, right } => self.compare(*left, operator, *right),
            ExprKind::Assign { l_expr, r_expr } => {
                let left_reg = self.execute_expr(*l_expr);
                let right_reg = self.execute_expr(*r_expr);

                self.cg_assign(left_reg, right_reg)
            }
            ExprKind::CompoundAssign { expr, tmp_symbol } => self.cg_comp_assign(*expr, tmp_symbol),
            ExprKind::Ident(var_symbol) => var_symbol.borrow().unwrap_var().get_reg(),
            ExprKind::Call { name, args } => self.cg_call(name, args, expr.type_decl),
            ExprKind::Cast { expr, direction, new_type } => self.cg_cast(new_type, *expr, direction),
            ExprKind::ScaleUp { expr, by } => self.cg_scale_up(*expr, by),
            ExprKind::ScaleDown { expr, shift_amount } => self.cg_scale_down(*expr, shift_amount),
            ExprKind::String(name) => self.cg_string(name),
            ExprKind::MemberAccess { expr, member } => {
                let reg = self.execute_expr(*expr);
                self.cg_member_access(reg, &member, true)
            }
            ExprKind::Ternary { cond, true_expr, false_expr, .. } => {
                self.cg_ternary(*cond, *true_expr, *false_expr)
            }
            ExprKind::Comma { left, right } => self.cg_comma(*left, *right),
            ExprKind::Nop => Register::Void,
        }
    }
    fn cg_comma(&mut self, left: Expr, right: Expr) -> Register {
        let reg = self.execute_expr(left);
        self.free(reg);

        self.execute_expr(right)
    }

    fn cg_ternary(&mut self, cond: Expr, true_expr: Expr, false_expr: Expr) -> Register {
        let mut cond_reg = self.execute_expr(cond);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let else_label = create_label(&mut self.label_index);

        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            cond_reg.clone(),
        ));
        self.write_out(Lir::JmpCond("e", else_label));
        self.free(cond_reg);

        let result = Register::Temp(TempRegister::new(
            true_expr.clone().type_decl,
            &mut self.interval_counter,
            self.instr_counter,
        ));
        let true_reg = self.execute_expr(true_expr);

        // copy both expressions into result register
        self.write_out(Lir::Mov(true_reg.clone(), result.clone()));
        self.free(true_reg);

        self.write_out(Lir::Jmp(done_label));
        self.write_out(Lir::LabelDefinition(else_label));

        let false_reg = self.execute_expr(false_expr);

        self.write_out(Lir::Mov(false_reg.clone(), result.clone()));
        self.free(false_reg);

        self.write_out(Lir::LabelDefinition(done_label));

        result
    }
    fn cg_member_access(&mut self, reg: Register, member: &str, free: bool) -> Register {
        if let Type::Struct(s) = reg.get_type() {
            let offset = s.member_offset(member);
            let member_type = s.member_type(member);

            let address = self.cg_address_at(reg, free);
            let mut result = if offset != 0 {
                self.cg_add(
                    Register::Literal(offset as i64, Type::Primitive(Primitive::Int)),
                    address,
                )
            } else {
                address
            };

            result.set_type(member_type);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else if let Type::Union(s) = reg.get_type() {
            let member_type = s.member_type(member);

            let mut result = self.cg_address_at(reg, free);

            result.set_type(member_type);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else {
            unreachable!("{:?}", reg.get_type())
        }
    }
    fn cg_comp_assign(&mut self, expr: Expr, tmp_symbol: VarSymbol) -> Register {
        // only have to declare tmp var, since compound assign is only syntax sugar
        self.declare_var(tmp_symbol, None);
        self.execute_expr(expr)
    }
    fn cg_string(&mut self, name: String) -> Register {
        Register::Label(LabelRegister::String(self.const_labels[&name]))
    }
    fn cg_scale_down(&mut self, expr: Expr, by_amount: usize) -> Register {
        let value_reg = self.execute_expr(expr);
        let value_reg = convert_reg!(self, value_reg, Register::Literal(..));

        // right shift number, equivalent to division (works bc type-size is 2^n)
        self.write_out(Lir::Shift(
            "r",
            Register::Literal(by_amount as i64, Type::Primitive(Primitive::Int)),
            value_reg.clone(),
        ));

        value_reg
    }
    fn cg_scale_up(&mut self, expr: Expr, by_amount: usize) -> Register {
        let value_reg = self.execute_expr(expr);

        self.cg_mult(
            Register::Literal(by_amount as i64, Type::Primitive(Primitive::Int)),
            value_reg,
        )
    }
    fn cg_cast(&mut self, new_type: Type, expr: Expr, direction: CastDirection) -> Register {
        match direction {
            CastDirection::Up => self.cg_cast_up(expr, new_type),
            CastDirection::Down => self.cg_cast_down(expr, new_type),
            CastDirection::Equal => self.execute_expr(expr),
        }
    }
    fn cg_cast_down(&mut self, expr: Expr, new_type: Type) -> Register {
        let mut value_reg = self.execute_expr(expr);
        value_reg.set_type(new_type);

        value_reg
    }
    fn cg_cast_up(&mut self, expr: Expr, new_type: Type) -> Register {
        let mut value_reg = self.execute_expr(expr);

        if matches!(
            value_reg,
            Register::Temp(..) | Register::Stack(..) | Register::Label(..)
        ) {
            let dest_reg = Register::Temp(TempRegister::new(
                new_type,
                &mut self.interval_counter,
                self.instr_counter,
            ));

            self.write_out(Lir::Movs(value_reg.clone(), dest_reg.clone()));

            self.free(value_reg);
            dest_reg
        } else {
            value_reg.set_type(new_type);
            value_reg
        }
    }
    fn cg_assign(&mut self, l_value: Register, r_value: Register) -> Register {
        if let Type::Struct(s) = l_value.get_type() {
            // when assigning structs have to assign each member
            for (_, member) in s.members().iter() {
                let member_lvalue =
                    self.cg_member_access(l_value.clone(), &member.unwrap_string(), false);
                let member_rvalue =
                    self.cg_member_access(r_value.clone(), &member.unwrap_string(), false);

                let reg = self.cg_assign(member_lvalue, member_rvalue);
                self.free(reg);
            }
            self.free(r_value);
            l_value
        } else {
            // can't move from mem to mem so make temp scratch-register
            let r_value = convert_reg!(self, r_value, Register::Stack(..) | Register::Label(..));
            let r_value = self.convert_to_rval(r_value);

            self.write_out(Lir::Mov(r_value.clone(), l_value.clone()));
            self.free(r_value);
            l_value
        }
    }
    fn cg_call(&mut self, name: String, args: Vec<Expr>, return_type: Type) -> Register {
        self.write_out(Lir::SaveRegs);

        let args_len = args.len();

        // align stack if pushes args
        if args_len >= ARG_REGS.len() && args_len % 2 != 0 {
            self.write_out(Lir::SubSp(8));
        }
        let mut arg_regs = Vec::new();

        // moving the arguments into their designated registers
        for (i, expr) in args.into_iter().enumerate().rev() {
            let mut reg = self.execute_expr(expr);
            let type_decl = reg.get_type();

            // put first six registers into designated argument-registers; others pushed onto stack
            if i < ARG_REGS.len() {
                let arg = Register::Arg(ArgRegister::new(
                    i,
                    type_decl,
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                self.write_out(Lir::Mov(reg.clone(), arg.clone()));

                arg_regs.push(arg);
            } else {
                // TODO: Literal should be allowed to be pushed
                reg = convert_reg!(self, reg, Register::Literal(..));
                self.write_out(Lir::Push(reg.clone()));
            }
            self.free(reg);
        }

        self.write_out(Lir::Call(name));

        self.remove_spilled_args(args_len);
        for reg in arg_regs {
            self.free(reg);
        }
        self.write_out(Lir::RestoreRegs);

        if !return_type.is_void() {
            let return_reg = Register::Temp(TempRegister::new(
                return_type.clone(),
                &mut self.interval_counter,
                self.instr_counter,
            ));
            self.write_out(Lir::Mov(Register::Return(return_type), return_reg.clone()));
            return_reg
        } else {
            Register::Void
        }
    }
    fn remove_spilled_args(&mut self, args_len: usize) {
        let spilled_args = args_len as isize - ARG_REGS.len() as isize;
        let alignment_offset = if spilled_args % 2 != 0 { 8 } else { 0 };

        if spilled_args > 0 {
            self.write_out(Lir::AddSp((spilled_args * 8 + alignment_offset) as usize));
        }
    }

    fn cg_logical(&mut self, left: Expr, operator: TokenKind, right: Expr) -> Register {
        match operator {
            TokenKind::AmpAmp => self.cg_and(left, right),
            TokenKind::PipePipe => self.cg_or(left, right),
            _ => unreachable!(),
        }
    }
    fn compare(&mut self, left: Expr, operator: TokenKind, right: Expr) -> Register {
        let left_reg = self.execute_expr(left);
        let right_reg = self.execute_expr(right);

        let left_reg = self.convert_to_rval(left_reg);
        let right_reg = self.convert_to_rval(right_reg);

        match operator {
            TokenKind::EqualEqual => self.cg_comparison("sete", left_reg, right_reg),
            TokenKind::BangEqual => self.cg_comparison("setne", left_reg, right_reg),
            TokenKind::Greater => self.cg_comparison("setg", left_reg, right_reg),
            TokenKind::GreaterEqual => self.cg_comparison("setge", left_reg, right_reg),
            TokenKind::Less => self.cg_comparison("setl", left_reg, right_reg),
            TokenKind::LessEqual => self.cg_comparison("setle", left_reg, right_reg),
            _ => unreachable!(),
        }
    }

    fn cg_comparison(&mut self, operator: &'static str, left: Register, right: Register) -> Register {
        let left = convert_reg!(
            self,
            left,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        let mut right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Cmp(right.clone(), left.clone()));
        self.write_out(Lir::Set(operator));

        right.set_type(Type::Primitive(Primitive::Int));
        self.write_out(Lir::Movz(
            Register::Return(Type::Primitive(Primitive::Char)),
            right.clone(),
        ));

        self.free(left);
        right
    }

    fn cg_or(&mut self, left: Expr, right: Expr) -> Register {
        let mut left = self.execute_expr(left);
        left = convert_reg!(self, left, Register::Literal(..));

        let true_label = create_label(&mut self.label_index);

        // jump to true label left is true => short circuit
        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            left.clone(),
        ));
        self.write_out(Lir::JmpCond("ne", true_label));
        self.free(left);

        let mut right = self.execute_expr(right);
        right = convert_reg!(self, right, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if right is false we know expression is false
        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            right.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(right);

        let done_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        // if expression true write 1 in result and skip false label
        self.write_out(Lir::LabelDefinition(true_label));
        self.write_out(Lir::Mov(
            Register::Literal(1, Type::Primitive(Primitive::Int)),
            result.clone(),
        ));

        self.write_out(Lir::Jmp(done_label));

        self.write_out(Lir::LabelDefinition(false_label));
        self.write_out(Lir::Mov(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            result.clone(),
        ));

        self.write_out(Lir::LabelDefinition(done_label));

        result
    }
    fn cg_and(&mut self, left: Expr, right: Expr) -> Register {
        let left = self.execute_expr(left);
        let left = convert_reg!(self, left, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if left is false expression is false, we jump to false label
        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            left.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(left);

        // left is true if right false jump to false label
        let right = self.execute_expr(right);
        let right = convert_reg!(self, right, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            right.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(right);

        // if no prior jump was taken expression is true
        let true_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        self.write_out(Lir::Mov(
            Register::Literal(1, Type::Primitive(Primitive::Int)),
            result.clone(),
        ));
        self.write_out(Lir::Jmp(true_label));

        self.write_out(Lir::LabelDefinition(false_label));
        self.write_out(Lir::Mov(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            result.clone(),
        ));

        self.write_out(Lir::LabelDefinition(true_label));

        result
    }
    fn cg_unary(&mut self, operator: TokenKind, right: Expr, new_type: Type) -> Register {
        let mut reg = self.execute_expr(right);
        // can't have literal as only operand to unary expression
        reg = convert_reg!(self, reg, Register::Literal(..));

        match operator {
            TokenKind::Bang => self.cg_bang(reg),
            TokenKind::Minus => self.cg_negate(reg),
            TokenKind::Plus => reg,
            TokenKind::Amp => self.cg_address_at(reg, true),
            TokenKind::Star => self.cg_deref(reg, new_type),
            TokenKind::Tilde => self.cg_bit_not(reg),
            _ => unreachable!(),
        }
    }
    fn cg_bit_not(&mut self, reg: Register) -> Register {
        // can't overwrite variable
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        self.write_out(Lir::Not(reg.clone()));

        reg
    }
    fn cg_bang(&mut self, reg: Register) -> Register {
        // compares reg-value with 0
        self.write_out(Lir::Cmp(
            Register::Literal(0, Type::Primitive(Primitive::Int)),
            reg.clone(),
        ));
        self.write_out(Lir::Set("sete"));

        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Lir::Movz(
            Register::Return(Type::Primitive(Primitive::Char)),
            result.clone(),
        ));
        self.free(reg);

        result
    }
    fn cg_negate(&mut self, reg: Register) -> Register {
        // can't overwrite variable
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        self.write_out(Lir::Neg(reg.clone()));
        reg
    }
    fn cg_address_at(&mut self, reg: Register, free: bool) -> Register {
        let dest = Register::Temp(TempRegister::new(
            Type::Pointer(Box::new(reg.get_type())),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        self.write_out(Lir::Load(reg.clone(), dest.clone()));

        if free {
            self.free(reg);
        }

        dest
    }
    fn cg_deref(&mut self, reg: Register, new_type: Type) -> Register {
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
        self.write_out(Lir::Add(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_sub(&mut self, left: Register, right: Register) -> Register {
        let left = convert_reg!(
            self,
            left,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );

        self.write_out(Lir::Sub(right.clone(), left.clone()));

        self.free(right);
        left
    }

    fn cg_mult(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Imul(left.clone(), right.clone()));

        self.free(left);
        right
    }

    fn cg_div(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Mov(left.clone(), Register::Return(left.get_type())));
        // rdx(3rd Argument register) stores remainder
        let rdx_reg = Register::Arg(ArgRegister::new(
            2,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // rax / right => rax
        self.write_out(Lir::Idiv(right.clone()));

        // move rax(div result) into right reg
        self.write_out(Lir::Mov(Register::Return(right.get_type()), right.clone()));

        self.free(rdx_reg);
        self.free(left);
        right
    }

    fn cg_mod(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Mov(left.clone(), Register::Return(left.get_type())));

        // rdx(3rd Argument register) stores remainder
        let rdx_reg = Register::Arg(ArgRegister::new(
            2,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // rax % rcx => rdx
        self.write_out(Lir::Idiv(right.clone()));
        self.write_out(Lir::Mov(rdx_reg.clone(), right.clone()));

        self.free(rdx_reg);
        self.free(left);
        right
    }

    fn cg_bit_xor(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Xor(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_bit_or(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::Or(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_bit_and(&mut self, left: Register, right: Register) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Lir::And(left.clone(), right.clone()));

        self.free(left);
        right
    }
    fn cg_shift(&mut self, direction: &'static str, left: Register, right: Register) -> Register {
        // destination register has to be reg or mem
        let left = self.make_temp(left);

        // expects shift amount to be in %cl (4th arg register)
        let mut cl_reg = Register::Arg(ArgRegister::new(
            3,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        self.write_out(Lir::Mov(right.clone(), cl_reg.clone()));
        self.free(right);

        cl_reg.set_type(Type::Primitive(Primitive::Char));
        self.write_out(Lir::Shift(direction, cl_reg.clone(), left.clone()));

        self.free(cl_reg);

        left
    }
    fn cg_binary(&mut self, left_reg: Register, token: &TokenKind, right_reg: Register) -> Register {
        let (left_reg, right_reg) = (self.convert_to_rval(left_reg), self.convert_to_rval(right_reg));

        match token {
            TokenKind::Plus => self.cg_add(left_reg, right_reg),
            TokenKind::Minus => self.cg_sub(left_reg, right_reg),
            TokenKind::Star => self.cg_mult(left_reg, right_reg),
            TokenKind::Slash => self.cg_div(left_reg, right_reg),
            TokenKind::Mod => self.cg_mod(left_reg, right_reg),
            TokenKind::Xor => self.cg_bit_xor(left_reg, right_reg),
            TokenKind::Pipe => self.cg_bit_or(left_reg, right_reg),
            TokenKind::Amp => self.cg_bit_and(left_reg, right_reg),
            TokenKind::LessLess => self.cg_shift("l", left_reg, right_reg),
            TokenKind::GreaterGreater => self.cg_shift("r", left_reg, right_reg),
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
        let result = Register::Temp(TempRegister::new(
            reg.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Lir::Mov(reg.clone(), result.clone()));
        self.free(reg);

        result
    }
    fn free(&mut self, reg: Register) {
        match reg {
            Register::Temp(reg) => {
                assert!(!self.live_intervals.contains_key(&reg.id));
                self.live_intervals.insert(
                    reg.id,
                    IntervalEntry::new(reg.start_idx, self.instr_counter, None, reg.type_decl),
                );
            }
            Register::Arg(reg) => {
                assert!(!self.live_intervals.contains_key(&reg.id));
                self.live_intervals.insert(
                    reg.id,
                    IntervalEntry::new(reg.start_idx, self.instr_counter, Some(reg.reg), reg.type_decl),
                );
            }
            _ => (),
        }
    }
}

pub fn align(offset: usize, type_decl: &Type) -> usize {
    let size = match type_decl {
        Type::Array { of, .. } => of.size(),
        _ => type_decl.size(),
    };
    align_by(offset, size)
}
