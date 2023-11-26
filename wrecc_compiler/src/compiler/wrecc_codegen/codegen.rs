use crate::compiler::common::{expr::*, stmt::*, token::*, types::*};
use crate::compiler::typechecker::{align_by, create_label};
use crate::compiler::wrecc_codegen::{ir::*, register::*, register_allocation::*};
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

    // keep track of current instruction for live-intervals in register allocation
    instr_counter: usize,

    // key for temporary register into live-intervals
    interval_counter: usize,

    // intervals for register allocation that keep track of lifetime of virtual-registers
    // (key:register-id, values: (end of lifetime, reg-type, physical register))
    live_intervals: HashMap<usize, IntervalEntry>,

    // when in function contains function name to access symbol table
    function_name: Option<Token>,

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
            function_name: None,
            jump_labels: Vec::new(),
            switch_labels: VecDeque::new(),
        }
    }

    pub fn translate(mut self, statements: Vec<Stmt>) -> (Vec<Ir>, HashMap<usize, IntervalEntry>) {
        self.cg_const_labels();
        self.cg_stmts(statements);

        (self.output, self.live_intervals)
    }
    fn write_out(&mut self, instruction: Ir) {
        self.instr_counter += 1;
        self.output.push(instruction)
    }
    fn cg_const_labels(&mut self) {
        for (data, label_index) in self.const_labels.clone().into_iter() {
            self.write_out(Ir::StringDeclaration(label_index, data));
        }
    }
    fn cg_stmts(&mut self, statements: Vec<Stmt>) {
        for s in statements {
            self.visit(s)
        }
    }
    fn visit(&mut self, statement: Stmt) {
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
                self.if_statement(cond, *then_branch, else_branch)
            }
            Stmt::While(_, cond, body) => self.while_statement(cond, *body),
            Stmt::Do(_, body, cond) => self.do_statement(*body, cond),
            Stmt::For(_, init, cond, inc, body) => self.for_statement(init, cond, inc, *body),
            Stmt::Break(..) => self.jump_statement(self.jump_labels.last().expect("typechecker").0),
            Stmt::Continue(..) => {
                self.jump_statement(self.jump_labels.last().expect("typechecker").1)
            }
            Stmt::Switch(_, cond, body) => self.switch_statement(cond, *body),
            Stmt::Case(_, _, body) | Stmt::Default(_, body) => self.case_statement(*body),
            Stmt::Goto(label) => self.goto_statement(label),
            Stmt::Label(name, body) => self.label_statement(name, *body),
        }
    }
    fn goto_statement(&mut self, label: Token) {
        let func = self
            .function_name
            .as_ref()
            .unwrap()
            .token
            .get_symbol_entry();
        let label_index = func.borrow().unwrap_func().labels[&label.unwrap_string()];

        self.write_out(Ir::Jmp(label_index));
    }
    fn label_statement(&mut self, name: Token, body: Stmt) {
        let func = self
            .function_name
            .as_ref()
            .unwrap()
            .token
            .get_symbol_entry();
        let label_index = func.borrow().unwrap_func().labels[&name.unwrap_string()];

        self.write_out(Ir::LabelDefinition(label_index));
        self.visit(body);
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

                    self.write_out(Ir::Cmp(
                        Register::Literal(*case_value, NEWTypes::default()),
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
    fn case_statement(&mut self, body: Stmt) {
        let label = self.switch_labels.pop_front().unwrap();

        self.write_out(Ir::LabelDefinition(label));

        self.visit(body);
    }
    fn do_statement(&mut self, body: Stmt, cond: Expr) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Ir::LabelDefinition(body_label));
        self.visit(body);

        self.write_out(Ir::LabelDefinition(cond_label));
        let mut cond_reg = self.execute_expr(cond);
        cond_reg = self.convert_to_rval(cond_reg);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

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
            self.visit(*init);
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
                cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

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
    fn while_statement(&mut self, cond: Expr, body: Stmt) {
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
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.write_out(Ir::JmpCond("ne", body_label));
        self.free(cond_reg);

        self.write_out(Ir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn if_statement(&mut self, cond: Expr, then_branch: Stmt, else_branch: Option<Box<Stmt>>) {
        let cond_reg = self.execute_expr(cond);
        let cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let mut else_label = done_label;

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.free(cond_reg);

        if else_branch.is_some() {
            else_label = create_label(&mut self.label_index);
        }
        self.write_out(Ir::JmpCond("e", else_label));

        self.visit(then_branch);

        if let Some(else_branch) = else_branch {
            self.write_out(Ir::Jmp(done_label));
            self.write_out(Ir::LabelDefinition(else_label));
            self.visit(*else_branch);
        }
        self.write_out(Ir::LabelDefinition(done_label));
    }
    fn return_statement(&mut self, value: Option<Expr>) {
        let func = self
            .function_name
            .as_ref()
            .unwrap()
            .token
            .get_symbol_entry();
        let function_epilogue = func.borrow().unwrap_func().epilogue_index;

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
    fn declaration(&mut self, decls: Vec<DeclarationKind>) {
        for d in decls {
            match d {
                DeclarationKind::Decl(type_decl, name, true) => {
                    self.declare_global_var(type_decl, name)
                }
                DeclarationKind::Decl(type_decl, name, false) => self.declare_var(type_decl, &name),
                DeclarationKind::Initializer(type_decl, name, init, true) => {
                    self.init_global_var(type_decl, name, init)
                }
                DeclarationKind::Initializer(type_decl, name, init, false) => {
                    let size = align(type_decl.size(), &type_decl);
                    self.declare_var(type_decl, &name);

                    self.init_var(&name, init, size);
                }
                DeclarationKind::FuncDecl(..) => (),
            }
        }
    }
    fn declare_global_var(&mut self, type_decl: NEWTypes, name: Token) {
        self.write_out(Ir::GlobalDeclaration(
            name.unwrap_string(),
            type_decl.is_ptr(),
        ));
        self.write_out(Ir::GlobalInit(
            NEWTypes::Primitive(Types::Void),
            StaticRegister::Literal(type_decl.size() as i64, NEWTypes::default()),
        ));
        let reg = Register::Label(LabelRegister::Var(name.unwrap_string(), type_decl));

        name.token
            .get_symbol_entry()
            .borrow_mut()
            .unwrap_var_mut()
            .set_reg(reg);
    }
    fn declare_var(&mut self, type_decl: NEWTypes, name: &Token) {
        let reg = Register::Stack(StackRegister::new(&mut self.current_bp_offset, type_decl));
        name.token
            .get_symbol_entry()
            .borrow_mut()
            .unwrap_var_mut()
            .set_reg(reg);
    }
    fn init_global_var(&mut self, type_decl: NEWTypes, var_name: Token, init: Init) {
        self.write_out(Ir::GlobalDeclaration(
            var_name.unwrap_string(),
            type_decl.is_ptr(),
        ));

        var_name
            .token
            .get_symbol_entry()
            .borrow_mut()
            .unwrap_var_mut()
            .set_reg(Register::Label(LabelRegister::Var(
                var_name.unwrap_string(),
                type_decl.clone(),
            )));

        match init.kind {
            InitKind::Scalar(expr) => {
                let value_reg = self.execute_global_expr(expr);

                self.write_out(Ir::GlobalInit(type_decl, value_reg));
            }
            InitKind::Aggr(list) => {
                let mut size = type_decl.size() as i64;
                let mut prev_offset: i64 = 0;

                for init in list {
                    if let InitKind::Scalar(expr) = init.kind {
                        let value_reg = self.execute_global_expr(expr);
                        let value_type = value_reg.get_type();

                        // fill gap in offset with zero
                        let diff = init.offset - prev_offset;
                        if diff != 0 {
                            self.write_out(Ir::GlobalInit(
                                NEWTypes::Primitive(Types::Void),
                                StaticRegister::Literal(diff, NEWTypes::default()),
                            ));
                            size -= diff;
                        }

                        size -= value_type.size() as i64;
                        prev_offset = init.offset + value_type.size() as i64;

                        self.write_out(Ir::GlobalInit(value_type, value_reg));
                    } else {
                        unreachable!("aggregate list was flattened in typechecker")
                    }
                }

                // fill remaining fields in type
                if size > 0 {
                    self.write_out(Ir::GlobalInit(
                        NEWTypes::Primitive(Types::Void),
                        StaticRegister::Literal(size as i64, NEWTypes::default()),
                    ));
                }
            }
        }
    }

    fn init_var(&mut self, var_name: &Token, init: Init, size: usize) {
        match init.kind {
            InitKind::Scalar(expr) => {
                let value_reg = self.execute_expr(expr);
                let mut var_reg = var_name
                    .token
                    .get_symbol_entry()
                    .borrow()
                    .unwrap_var()
                    .get_reg();

                var_reg.set_type(value_reg.get_type());
                if let Register::Stack(stack_reg) = &mut var_reg {
                    stack_reg.bp_offset -= init.offset as usize;

                    let value_reg = self.cg_assign(var_reg, value_reg);
                    self.free(value_reg);
                } else {
                    unreachable!("local variables can only be located on stack")
                }
            }
            InitKind::Aggr(list) => {
                // first overwrite all entries with 0
                self.clear_mem(var_name, size);

                for init in list {
                    self.init_var(var_name, *init, size)
                }
            }
        }
    }

    fn clear_mem(&mut self, var_name: &Token, amount: usize) {
        // writes 0 to stack until amount == 0
        // eax value that gets written
        // ecx amount
        // rdi at memory pos
        let var = var_name
            .token
            .get_symbol_entry()
            .borrow()
            .unwrap_var()
            .get_reg();
        // TODO: can be optimized by writing 8Bytes (instead of 1) per repetition but that requires extra logic when amount and size don't align
        let eax_reg = Register::Return(NEWTypes::Primitive(Types::Char));
        let ecx_reg = Register::Arg(ArgRegister::new(
            3,
            NEWTypes::default(),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        let rdi_reg = Register::Arg(ArgRegister::new(
            0,
            NEWTypes::Primitive(Types::Long),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Ir::Mov(
            Register::Literal(0, NEWTypes::default()),
            eax_reg.clone(),
        ));
        self.write_out(Ir::Mov(
            Register::Literal(amount as i64, NEWTypes::default()),
            ecx_reg.clone(),
        ));
        self.write_out(Ir::Load(var, rdi_reg.clone()));
        self.write_out(Ir::Rep);

        self.free(eax_reg);
        self.free(ecx_reg);
        self.free(rdi_reg);
    }

    fn init_arg(&mut self, type_decl: NEWTypes, var_name: Token, arg_reg: Register) {
        self.declare_var(type_decl, &var_name);

        let reg = self.cg_assign(
            var_name
                .token
                .get_symbol_entry()
                .borrow()
                .unwrap_var()
                .get_reg(),
            arg_reg,
        );
        self.free(reg);
    }

    fn function_definition(&mut self, name: Token, body: Vec<Stmt>) {
        let func_symbol = name.token.get_symbol_entry();
        let params = func_symbol.borrow().unwrap_func().params.clone();

        let function_epilogue = create_label(&mut self.label_index);
        func_symbol.borrow_mut().unwrap_func_mut().epilogue_index = function_epilogue;

        // create a label for all goto-labels inside a function
        for value in func_symbol
            .borrow_mut()
            .unwrap_func_mut()
            .labels
            .values_mut()
        {
            *value = create_label(&mut self.label_index);
        }
        // save function name for return label jump
        self.function_name = Some(name.clone());
        self.current_bp_offset = 0;

        // generate function code
        self.cg_func_preamble(
            &name,
            params
                .into_iter()
                .map(|(t, name)| (t, name.expect("all parameters to be named")))
                .collect(),
        );
        self.cg_stmts(body);
        self.cg_func_postamble(name, function_epilogue);

        self.function_name = None;
    }
    fn cg_func_preamble(&mut self, name: &Token, params: Vec<(NEWTypes, Token)>) {
        let func = self
            .function_name
            .as_ref()
            .unwrap()
            .token
            .get_symbol_entry();
        let stack_size = func.borrow().unwrap_func().stack_size;
        self.write_out(Ir::FuncSetup(name.clone(), stack_size));

        // initialize parameters
        for (i, (type_decl, param_name)) in params.into_iter().enumerate() {
            if i < ARG_REGS.len() {
                let arg = Register::Arg(ArgRegister::new(
                    i,
                    type_decl.clone(),
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                self.init_arg(type_decl, param_name, arg);
            } else {
                // if not in designated arg-register get from stack
                let reg = Register::Temp(TempRegister::new(
                    type_decl.clone(),
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                let pushed = Register::Stack(StackRegister::new_pushed(i));

                self.write_out(Ir::Mov(pushed, reg.clone()));
                self.init_arg(type_decl, param_name, reg);
            }
        }
    }
    fn cg_func_postamble(&mut self, name: Token, epilogue_index: usize) {
        self.write_out(Ir::LabelDefinition(epilogue_index));

        let stack_size = name
            .token
            .get_symbol_entry()
            .borrow()
            .unwrap_func()
            .stack_size;
        self.write_out(Ir::FuncTeardown(stack_size))
    }

    pub fn block(&mut self, statements: Vec<Stmt>) {
        self.cg_stmts(statements)
    }

    fn cg_literal(&mut self, n: i64, type_decl: NEWTypes) -> Register {
        let literal_reg = Register::Literal(n, type_decl);

        // 64bit literals are only allowed to move to scratch-register
        if let Types::Long = integer_type(n) {
            let scratch_reg = Register::Temp(TempRegister::new(
                literal_reg.get_type(),
                &mut self.interval_counter,
                self.instr_counter,
            ));
            self.write_out(Ir::Mov(literal_reg, scratch_reg.clone()));
            scratch_reg
        } else {
            literal_reg
        }
    }
    fn execute_global_expr(&mut self, ast: Expr) -> StaticRegister {
        match ast.kind {
            ExprKind::String(token) => {
                let name = token.unwrap_string();
                StaticRegister::Label(LabelRegister::String(self.const_labels[&name]))
            }
            ExprKind::Literal(n) => StaticRegister::Literal(n, ast.type_decl.unwrap()),
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
                        NEWTypes::Primitive(scaled_type)
                    } else {
                        type_decl
                    };

                    StaticRegister::Literal(n, type_decl)
                } else {
                    unreachable!("can only scale literal value")
                }
            }
            ExprKind::Unary { right, token, .. } => {
                let mut reg = self.execute_global_expr(*right);
                match token.token {
                    TokenType::Amp => reg.set_type(NEWTypes::Pointer(Box::new(reg.get_type()))),
                    TokenType::Star => reg.set_type(ast.type_decl.unwrap()),
                    _ => unreachable!("non-constant unary expression"),
                }
                reg
            }
            ExprKind::MemberAccess { expr, member, .. } => {
                let mut reg = self.execute_global_expr(*expr);

                match reg.get_type() {
                    NEWTypes::Struct(s) => {
                        let offset = s.member_offset(&member.unwrap_string());
                        let member_type = s.member_type(&member.unwrap_string());

                        reg.set_type(member_type);
                        match reg {
                            StaticRegister::Label(label_reg) => StaticRegister::LabelOffset(
                                label_reg,
                                offset as i64,
                                TokenType::Plus,
                            ),
                            StaticRegister::LabelOffset(reg, existant_offset, _) => {
                                let offset = existant_offset + offset as i64;
                                if offset < 0 {
                                    StaticRegister::LabelOffset(reg, offset.abs(), TokenType::Minus)
                                } else {
                                    StaticRegister::LabelOffset(reg, offset, TokenType::Plus)
                                }
                            }
                            _ => unreachable!("Literal can't be struct address"),
                        }
                    }
                    NEWTypes::Union(s) => {
                        let member_type = s.member_type(&member.unwrap_string());
                        reg.set_type(member_type);
                        reg
                    }
                    _ => unreachable!("{:?}", reg.get_type()),
                }
            }
            ExprKind::Binary { left, token, right } => {
                let left = self.execute_global_expr(*left);
                let right = self.execute_global_expr(*right);

                match (left, right) {
                    (StaticRegister::Label(reg), StaticRegister::Literal(n, _))
                    | (StaticRegister::Literal(n, _), StaticRegister::Label(reg)) => {
                        StaticRegister::LabelOffset(reg, n, token.token)
                    }

                    (
                        StaticRegister::LabelOffset(reg, offset, _),
                        StaticRegister::Literal(n, _),
                    )
                    | (
                        StaticRegister::Literal(n, _),
                        StaticRegister::LabelOffset(reg, offset, _),
                    ) => {
                        let offset = n + offset;
                        if offset < 0 {
                            StaticRegister::LabelOffset(reg, offset.abs(), TokenType::Minus)
                        } else {
                            StaticRegister::LabelOffset(reg, offset, TokenType::Plus)
                        }
                    }
                    _ => unreachable!(),
                }
            }
            ExprKind::Ident(name) => {
                // plain ident isn't compile-time-constant (this gets caught in typechecker)
                // but is needed to evaluate address-constants
                if let Register::Label(reg) = name
                    .token
                    .get_symbol_entry()
                    .borrow()
                    .unwrap_var()
                    .get_reg()
                {
                    StaticRegister::Label(reg)
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!("non global-constant expr {}", ast),
        }
    }
    pub fn execute_expr(&mut self, ast: Expr) -> Register {
        match ast.kind {
            ExprKind::Binary { left, token, right } => {
                let left_reg = self.execute_expr(*left);
                let right_reg = self.execute_expr(*right);

                self.cg_binary(left_reg, &token.token, right_reg)
            }
            ExprKind::Literal(n) => self.cg_literal(n, ast.type_decl.unwrap()),
            ExprKind::Grouping { expr } => self.execute_expr(*expr),
            ExprKind::Unary { token, right } => {
                self.cg_unary(token, *right, ast.type_decl.unwrap())
            }
            ExprKind::Logical { left, token, right } => self.cg_logical(*left, token, *right),
            ExprKind::Comparison { left, token, right } => self.compare(*left, token, *right),
            ExprKind::Assign { l_expr, r_expr, .. } => {
                let left_reg = self.execute_expr(*l_expr);
                let right_reg = self.execute_expr(*r_expr);

                self.cg_assign(left_reg, right_reg)
            }
            ExprKind::CompoundAssign { l_expr, r_expr, token } => {
                self.cg_comp_assign(*l_expr, token, *r_expr)
            }
            ExprKind::Ident(name) => name
                .token
                .get_symbol_entry()
                .borrow()
                .unwrap_var()
                .get_reg(),
            ExprKind::Call { name, args, .. } => self.cg_call(name, args, ast.type_decl.unwrap()),
            ExprKind::Cast { expr, direction, new_type, .. } => {
                self.cg_cast(new_type, *expr, direction.unwrap())
            }
            ExprKind::ScaleUp { expr, by } => self.cg_scale_up(*expr, by),
            ExprKind::ScaleDown { expr, shift_amount } => self.cg_scale_down(*expr, shift_amount),
            ExprKind::String(token) => self.cg_string(token.unwrap_string()),
            ExprKind::PostUnary { token, left, by_amount } => {
                self.cg_postunary(token, *left, by_amount)
            }
            ExprKind::MemberAccess { expr, member, .. } => {
                let reg = self.execute_expr(*expr);
                self.cg_member_access(reg, &member.unwrap_string(), true)
            }
            ExprKind::Ternary { cond, true_expr, false_expr, .. } => {
                self.cg_ternary(*cond, *true_expr, *false_expr)
            }
            ExprKind::Comma { left, right } => self.cg_comma(*left, *right),
            ExprKind::SizeofExpr { value: Some(value), .. } | ExprKind::SizeofType { value } => {
                Register::Literal(value as i64, NEWTypes::Primitive(Types::Long))
            }
            ExprKind::Nop => Register::Void,
            _ => unreachable!("can only be sizeof but all cases covered"),
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

        self.write_out(Ir::Cmp(
            Register::Literal(0, NEWTypes::default()),
            cond_reg.clone(),
        ));
        self.write_out(Ir::JmpCond("e", else_label));
        self.free(cond_reg);

        let result = Register::Temp(TempRegister::new(
            true_expr.clone().type_decl.unwrap(),
            &mut self.interval_counter,
            self.instr_counter,
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
    fn cg_member_access(&mut self, reg: Register, member: &str, free: bool) -> Register {
        if let NEWTypes::Struct(s) = reg.get_type() {
            let offset = s.member_offset(&member);
            let member_type = s.member_type(&member);

            let address = self.cg_address_at(reg, free);
            let mut result = if offset != 0 {
                self.cg_add(
                    Register::Literal(offset as i64, NEWTypes::Primitive(Types::Int)),
                    address,
                )
            } else {
                address
            };

            result.set_type(member_type);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else if let NEWTypes::Union(s) = reg.get_type() {
            let member_type = s.member_type(&member);

            let mut result = self.cg_address_at(reg, free);

            result.set_type(member_type);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else {
            unreachable!("{:?}", reg.get_type())
        }
    }
    fn cg_comp_assign(&mut self, l_expr: Expr, token: Token, r_expr: Expr) -> Register {
        let l_reg = self.execute_expr(l_expr);
        let r_reg = self.execute_expr(r_expr);

        let mut temp_scratch = Register::Temp(TempRegister::new(
            l_reg.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // INFO: have to do integer-promotion in codegen
        // would like it to be in typechecker but doesn't work because expressions would be overwritten
        match (l_reg.get_type().size(), r_reg.get_type().size()) {
            (l_size, r_size)
                if (l_size < r_size)
                    && matches!(l_reg, Register::Temp(..) | Register::Stack(..)) =>
            {
                temp_scratch.set_type(r_reg.get_type());
                self.write_out(Ir::Movs(l_reg.clone(), temp_scratch.clone()));
            }
            (size, _)
                if (size < Types::Int.size())
                    && matches!(l_reg, Register::Temp(..) | Register::Stack(..)) =>
            {
                temp_scratch.set_type(NEWTypes::Primitive(Types::Int));
                self.write_out(Ir::Movs(l_reg.clone(), temp_scratch.clone()));
            }
            _ => {
                self.write_out(Ir::Mov(l_reg.clone(), temp_scratch.clone()));
            }
        }

        let mut bin_reg = self.cg_binary(temp_scratch, &token.comp_to_binary(), r_reg);

        // we can do this because typechecker would catch any type-errors
        bin_reg.set_type(l_reg.get_type());

        self.cg_assign(l_reg, bin_reg)
    }
    fn cg_postunary(&mut self, token: Token, expr: Expr, by_amount: usize) -> Register {
        let reg = self.execute_expr(expr);

        let return_reg = Register::Temp(TempRegister::new(
            reg.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // Assign value to return-register before binary operation
        self.write_out(Ir::Mov(reg.clone(), return_reg.clone()));

        // Do binary operation with at least 4Byte register
        let mut operation_reg = Register::Temp(TempRegister::new(
            reg.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        if operation_reg.get_type().size() < Types::Int.size() {
            operation_reg.set_type(NEWTypes::Primitive(Types::Int));
            self.write_out(Ir::Movs(return_reg.clone(), operation_reg.clone()));
        } else {
            self.write_out(Ir::Mov(return_reg.clone(), operation_reg.clone()));
        }

        let by_amount = Register::Literal(by_amount as i64, NEWTypes::default());
        match token.token {
            TokenType::PlusPlus => self.write_out(Ir::Add(by_amount, operation_reg.clone())),
            TokenType::MinusMinus => self.write_out(Ir::Sub(by_amount, operation_reg.clone())),
            _ => unreachable!(),
        };

        // reset operation-regs type to type of original reg
        operation_reg.set_type(reg.get_type());

        // Write operation result back to original reg
        self.write_out(Ir::Mov(operation_reg.clone(), reg.clone()));

        self.free(reg);
        self.free(operation_reg);

        return_reg
    }
    fn cg_string(&mut self, name: String) -> Register {
        Register::Label(LabelRegister::String(self.const_labels[&name]))
    }
    fn cg_scale_down(&mut self, expr: Expr, by_amount: usize) -> Register {
        let value_reg = self.execute_expr(expr);
        let value_reg = convert_reg!(self, value_reg, Register::Literal(..));

        // right shift number, equivalent to division (works bc type-size is 2^n)
        self.write_out(Ir::Shift(
            "r",
            Register::Literal(by_amount as i64, NEWTypes::default()),
            value_reg.clone(),
        ));

        value_reg
    }
    fn cg_scale_up(&mut self, expr: Expr, by_amount: usize) -> Register {
        let value_reg = self.execute_expr(expr);

        self.cg_mult(
            Register::Literal(by_amount as i64, NEWTypes::Primitive(Types::Int)),
            value_reg,
        )
    }
    fn cg_cast(&mut self, new_type: NEWTypes, expr: Expr, direction: CastDirection) -> Register {
        match direction {
            CastDirection::Up => self.cg_cast_up(expr, new_type),
            CastDirection::Down => self.cg_cast_down(expr, new_type),
            CastDirection::Equal => self.execute_expr(expr),
        }
    }
    fn cg_cast_down(&mut self, expr: Expr, new_type: NEWTypes) -> Register {
        let mut value_reg = self.execute_expr(expr);
        value_reg.set_type(new_type);

        value_reg
    }
    fn cg_cast_up(&mut self, expr: Expr, new_type: NEWTypes) -> Register {
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

            self.write_out(Ir::Mov(r_value.clone(), l_value.clone()));
            self.free(r_value);
            l_value
        }
    }
    fn cg_call(&mut self, func_name: Token, args: Vec<Expr>, return_type: NEWTypes) -> Register {
        self.write_out(Ir::SaveRegs);

        let args_len = args.len();

        // align stack if pushes args
        if args_len >= ARG_REGS.len() && args_len % 2 != 0 {
            self.write_out(Ir::SubSp(8));
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
                self.write_out(Ir::Mov(reg.clone(), arg.clone()));

                arg_regs.push(arg);
            } else {
                // TODO: Literal should be allowed to be pushed
                reg = convert_reg!(self, reg, Register::Literal(..));
                self.write_out(Ir::Push(reg.clone()));
            }
            self.free(reg);
        }

        self.write_out(Ir::Call(func_name.unwrap_string()));

        self.remove_spilled_args(args_len);
        for reg in arg_regs {
            self.free(reg);
        }
        self.write_out(Ir::RestoreRegs);

        if !return_type.is_void() {
            let return_reg = Register::Temp(TempRegister::new(
                return_type.clone(),
                &mut self.interval_counter,
                self.instr_counter,
            ));
            self.write_out(Ir::Mov(Register::Return(return_type), return_reg.clone()));
            return_reg
        } else {
            Register::Void
        }
    }
    fn remove_spilled_args(&mut self, args_len: usize) {
        let spilled_args = args_len as isize - ARG_REGS.len() as isize;
        let alignment_offset = if spilled_args % 2 != 0 { 8 } else { 0 };

        if spilled_args > 0 {
            self.write_out(Ir::AddSp((spilled_args * 8 + alignment_offset) as usize));
        }
    }

    fn cg_logical(&mut self, left: Expr, token: Token, right: Expr) -> Register {
        match token.token {
            TokenType::AmpAmp => self.cg_and(left, right),
            TokenType::PipePipe => self.cg_or(left, right),
            _ => unreachable!(),
        }
    }
    fn compare(&mut self, left: Expr, token: Token, right: Expr) -> Register {
        let left_reg = self.execute_expr(left);
        let right_reg = self.execute_expr(right);

        let (left_reg, right_reg) = (
            self.convert_to_rval(left_reg),
            self.convert_to_rval(right_reg),
        );

        match token.token {
            TokenType::EqualEqual => self.cg_comparison("sete", left_reg, right_reg),
            TokenType::BangEqual => self.cg_comparison("setne", left_reg, right_reg),
            TokenType::Greater => self.cg_comparison("setg", left_reg, right_reg),
            TokenType::GreaterEqual => self.cg_comparison("setge", left_reg, right_reg),
            TokenType::Less => self.cg_comparison("setl", left_reg, right_reg),
            TokenType::LessEqual => self.cg_comparison("setle", left_reg, right_reg),
            _ => unreachable!(),
        }
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
        let mut right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );
        self.write_out(Ir::Cmp(right.clone(), left.clone()));
        self.write_out(Ir::Set(operator));

        right.set_type(NEWTypes::Primitive(Types::Int));
        self.write_out(Ir::Movz(
            Register::Return(NEWTypes::Primitive(Types::Char)),
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
            &mut self.interval_counter,
            self.instr_counter,
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
    fn cg_and(&mut self, left: Expr, right: Expr) -> Register {
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
            &mut self.interval_counter,
            self.instr_counter,
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
    fn cg_unary(&mut self, token: Token, right: Expr, new_type: NEWTypes) -> Register {
        let mut reg = self.execute_expr(right);
        // can't have literal as only operand to unary expression
        reg = convert_reg!(self, reg, Register::Literal(..));

        match token.token {
            TokenType::Bang => self.cg_bang(reg),
            TokenType::Minus => self.cg_negate(reg),
            TokenType::Plus => reg,
            TokenType::Amp => self.cg_address_at(reg, true),
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

        let result = Register::Temp(TempRegister::new(
            NEWTypes::Primitive(Types::Int),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Ir::Movz(
            Register::Return(NEWTypes::Primitive(Types::Char)),
            result.clone(),
        ));
        self.free(reg);

        result
    }
    fn cg_negate(&mut self, reg: Register) -> Register {
        // can't overwrite variable
        let reg = convert_reg!(self, reg, Register::Label(..) | Register::Stack(..));
        self.write_out(Ir::Neg(reg.clone()));
        reg
    }
    fn cg_address_at(&mut self, reg: Register, free: bool) -> Register {
        let dest = Register::Temp(TempRegister::new(
            NEWTypes::Pointer(Box::new(reg.get_type())),
            &mut self.interval_counter,
            self.instr_counter,
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
        // rdx(3rd Argument register) stores remainder
        let rdx_reg = Register::Arg(ArgRegister::new(
            2,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // rax / right => rax
        self.write_out(Ir::Idiv(right.clone()));

        // move rax(div result) into right reg
        self.write_out(Ir::Mov(Register::Return(right.get_type()), right.clone()));

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
        self.write_out(Ir::Mov(left.clone(), Register::Return(left.get_type())));

        // rdx(3rd Argument register) stores remainder
        let rdx_reg = Register::Arg(ArgRegister::new(
            2,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        // rax % rcx => rdx
        self.write_out(Ir::Idiv(right.clone()));
        self.write_out(Ir::Mov(rdx_reg.clone(), right.clone()));

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
        let mut cl_reg = Register::Arg(ArgRegister::new(
            3,
            right.get_type(),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        self.write_out(Ir::Mov(right.clone(), cl_reg.clone()));
        self.free(right);

        cl_reg.set_type(NEWTypes::Primitive(Types::Char));
        self.write_out(Ir::Shift(direction, cl_reg.clone(), left.clone()));

        self.free(cl_reg);

        left
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

        self.write_out(Ir::Mov(reg.clone(), result.clone()));
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
                    IntervalEntry::new(
                        reg.start_idx,
                        self.instr_counter,
                        Some(reg.reg),
                        reg.type_decl,
                    ),
                );
            }
            _ => (),
        }
    }
}

pub fn align(offset: usize, type_decl: &NEWTypes) -> usize {
    let size = match type_decl {
        NEWTypes::Array { of, .. } => of.size(),
        _ => type_decl.size(),
    };
    align_by(offset, size)
}
