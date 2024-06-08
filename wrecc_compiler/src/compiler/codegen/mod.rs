//! Converts [AST](crate::compiler::typechecker::mir) into linear [LIR](lir).<br>
//! Also builds live-intervals for every virtual-register to be filled in by real scratch-registers
//! during [Register Allocation](register_allocation)

pub mod lir;
pub mod register;
pub mod register_allocation;

use crate::compiler::codegen::{lir::*, register::*, register_allocation::*};
use crate::compiler::common::{environment::SymbolRef, token::*, types::*};
use crate::compiler::typechecker::mir::{decl::*, expr::*, stmt::*};
use crate::compiler::typechecker::{align_by, create_label, ConstLabels};

use std::collections::HashMap;
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

struct StaticLabels(HashMap<String, usize>);
impl StaticLabels {
    fn update(&mut self, name: String) -> String {
        if let Some(index) = self.0.get_mut(&name) {
            *index += 1;
            format!("{}.{}", name, index)
        } else {
            self.0.insert(name.clone(), 0);
            format!("{}.0", name)
        }
    }
}

pub struct Compiler {
    // outputs intermediate-representation that doesn't contain physical registers yet
    output: Vec<Lir>,

    // keep track of current instruction for live-intervals in register allocation
    instr_counter: usize,

    // key for temporary register into live-intervals
    interval_counter: usize,

    // intervals for register allocation that keep track of lifetime of virtual-registers
    live_intervals: HashMap<usize, IntervalEntry>,

    // index of current label
    label_index: usize,

    // map containing strings and their corresponding label-index
    const_labels: ConstLabels,

    // loop labels saved so that break and continue jump to them
    jump_labels: Vec<(usize, usize)>,

    // if the same static variable is declared in different scopes they get an index appended:
    // void foo() {static int a;}
    // void bar() {static int a;}
    // will be stored as a.0 and a.1 because they refer to different values
    static_labels: StaticLabels,

    // case/default-labels get defined in each switch and then the
    // respective case/default-statements pop them in order of appearance
    switch_labels: Vec<usize>,
}
impl Compiler {
    pub fn new(const_labels: ConstLabels) -> Self {
        Compiler {
            const_labels,
            output: Vec::with_capacity(100),
            live_intervals: HashMap::with_capacity(30),
            static_labels: StaticLabels(HashMap::new()),
            interval_counter: 0,
            instr_counter: 0,
            label_index: 0,
            jump_labels: Vec::new(),
            switch_labels: Vec::new(),
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
    fn cg_stmts(&mut self, func: &mut Function, statements: Vec<Stmt>) {
        for stmt in statements {
            self.visit_stmt(func, stmt)
        }
    }
    fn visit_decl(&mut self, external_decl: ExternalDeclaration) {
        match external_decl {
            ExternalDeclaration::Declaration(decls) => self.global_declaration(decls),
            ExternalDeclaration::Function(func, func_symbol, stmts) => {
                self.function_definition(func, func_symbol, stmts)
            }
        }
    }
    fn visit_stmt(&mut self, func: &mut Function, statement: Stmt) {
        match statement {
            Stmt::Expr(expr) => {
                let reg = self.execute_expr(func, expr);
                self.free(reg); // result isn't used
            }
            Stmt::Declaration(decls) => self.declaration(func, decls),
            Stmt::Block(statements) => self.block(func, statements),
            Stmt::Return(expr) => self.return_statement(func, expr),
            Stmt::If(cond, then_branch, else_branch) => {
                self.if_statement(func, cond, *then_branch, else_branch)
            }
            Stmt::While(cond, body) => self.while_statement(func, cond, *body),
            Stmt::Do(body, cond) => self.do_statement(func, *body, cond),
            Stmt::For(init, cond, inc, body) => self.for_statement(func, init, cond, inc, *body),
            Stmt::Break => self.jump_statement(self.jump_labels.last().expect("typechecker").0),
            Stmt::Continue => self.jump_statement(self.jump_labels.last().expect("typechecker").1),
            Stmt::Switch(cond, body) => self.switch_statement(func, cond, *body),
            Stmt::Case(body) | Stmt::Default(body) => self.case_statement(func, *body),
            Stmt::Goto(label) => self.goto_statement(func, label),
            Stmt::Label(name, body) => self.label_statement(func, name, *body),
        }
    }
    fn goto_statement(&mut self, func: &Function, label: String) {
        let label_index = func.labels[&label];

        self.write_out(Lir::Jmp(label_index));
    }
    fn label_statement(&mut self, func: &mut Function, name: String, body: Stmt) {
        let label_index = func.labels[&name];

        self.write_out(Lir::LabelDefinition(label_index));
        self.visit_stmt(func, body);
    }

    fn switch_statement(&mut self, func: &mut Function, cond: Expr, body: Stmt) {
        let switch_labels = func.switches.pop_front().unwrap();

        let switch_jump_labels: Vec<usize> = (0..switch_labels.borrow().len())
            .map(|_| create_label(&mut self.label_index))
            .collect();

        let mut cond_reg = self.execute_expr(func, cond);

        let mut default_label = None;
        for (kind, label) in switch_labels.borrow().iter().zip(switch_jump_labels.clone()) {
            match kind {
                CaseKind::Case(case_value) => {
                    cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

                    self.write_out(Lir::Cmp(
                        Register::Literal(case_value.clone(), Type::Primitive(Primitive::Int(false))),
                        cond_reg.clone(),
                    ));
                    self.write_out(Lir::JmpCond("e", label));
                }
                CaseKind::Default => default_label = Some(label),
            }
        }
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, 0));
        self.switch_labels
            .append(&mut switch_jump_labels.into_iter().rev().collect());

        // default label has to be jumped to at the end (even if there are cases following it) if no other cases match
        if let Some(label) = default_label {
            self.write_out(Lir::Jmp(label));
        } else {
            self.write_out(Lir::Jmp(end_label));
        }

        self.free(cond_reg);

        self.visit_stmt(func, body);

        self.write_out(Lir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }
    fn case_statement(&mut self, func: &mut Function, body: Stmt) {
        let label = self.switch_labels.pop().unwrap();

        self.write_out(Lir::LabelDefinition(label));

        self.visit_stmt(func, body);
    }
    fn do_statement(&mut self, func: &mut Function, body: Stmt, cond: Expr) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Lir::LabelDefinition(body_label));
        self.visit_stmt(func, body);

        self.write_out(Lir::LabelDefinition(cond_label));
        let mut cond_reg = self.execute_expr(func, cond);
        cond_reg = self.convert_to_rval(cond_reg);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
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
        func: &mut Function,
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
            self.visit_stmt(func, *init);
        }
        self.write_out(Lir::Jmp(cond_label));
        self.write_out(Lir::LabelDefinition(body_label));

        self.visit_stmt(func, body);

        self.write_out(Lir::LabelDefinition(inc_label));

        if let Some(inc) = inc {
            let reg = self.execute_expr(func, inc);
            self.free(reg);
        }

        self.write_out(Lir::LabelDefinition(cond_label));

        match cond {
            Some(cond) => {
                let mut cond_reg = self.execute_expr(func, cond);
                cond_reg = self.convert_to_rval(cond_reg);
                cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

                self.write_out(Lir::Cmp(
                    Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
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
    fn while_statement(&mut self, func: &mut Function, cond: Expr, body: Stmt) {
        let body_label = create_label(&mut self.label_index);
        let cond_label = create_label(&mut self.label_index);
        let end_label = create_label(&mut self.label_index);

        self.jump_labels.push((end_label, cond_label));

        self.write_out(Lir::Jmp(cond_label));
        self.write_out(Lir::LabelDefinition(body_label));

        self.visit_stmt(func, body);

        self.write_out(Lir::LabelDefinition(cond_label));

        let mut cond_reg = self.execute_expr(func, cond);
        cond_reg = self.convert_to_rval(cond_reg);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            cond_reg.clone(),
        ));
        self.write_out(Lir::JmpCond("ne", body_label));
        self.free(cond_reg);

        self.write_out(Lir::LabelDefinition(end_label));

        self.jump_labels.pop();
    }

    fn if_statement(
        &mut self,
        func: &mut Function,
        cond: Expr,
        then_branch: Stmt,
        else_branch: Option<Box<Stmt>>,
    ) {
        let cond_reg = self.execute_expr(func, cond);
        let cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let mut else_label = done_label;

        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            cond_reg.clone(),
        ));
        self.free(cond_reg);

        if else_branch.is_some() {
            else_label = create_label(&mut self.label_index);
        }
        self.write_out(Lir::JmpCond("e", else_label));

        self.visit_stmt(func, then_branch);

        if let Some(else_branch) = else_branch {
            self.write_out(Lir::Jmp(done_label));
            self.write_out(Lir::LabelDefinition(else_label));
            self.visit_stmt(func, *else_branch);
        }
        self.write_out(Lir::LabelDefinition(done_label));
    }
    fn return_statement(&mut self, func: &mut Function, value: Option<Expr>) {
        let function_epilogue = func.epilogue_index;

        match value {
            Some(expr) => {
                let return_value = self.execute_expr(func, expr);
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
    fn global_declaration(&mut self, declarators: Vec<Declarator>) {
        for declarator in declarators {
            let var_symbol = declarator.entry.borrow().clone();
            let ty = var_symbol.qtype.ty.clone();

            if declarator.name == var_symbol.token && !var_symbol.is_extern() {
                let name = declarator.name.unwrap_string();
                let label_name = if var_symbol.is_static() {
                    self.static_labels.update(name)
                } else {
                    name
                };

                self.declare_global_var(label_name, ty, declarator.entry, declarator.init)
            }
            // if variable is declared but its initialization is after the first use then
            // still needs a register to access:
            // ```
            // int a;
            // int main() {printf("%d",a);} // prints 3
            // int a = 3;
            // ```
            else if var_symbol.reg.is_none() {
                declarator
                    .entry
                    .borrow_mut()
                    .set_reg(Register::Label(LabelRegister::Var(
                        declarator.name.unwrap_string(),
                        ty,
                        var_symbol.is_extern(),
                    )))
            }
        }
    }

    fn declare_global_var(
        &mut self,
        label_name: String,
        ty: Type,
        var_symbol: SymbolRef,
        init: Option<Init>,
    ) {
        self.write_out(Lir::GlobalDeclaration(
            label_name.clone(),
            ty.is_ptr(),
            var_symbol.borrow().is_static(),
        ));

        if let Some(init) = init {
            self.init_global_var(label_name, ty, var_symbol, init);
        } else {
            self.write_out(Lir::GlobalInit(
                Type::Primitive(Primitive::Void),
                StaticRegister::Literal(
                    LiteralKind::Signed(ty.size() as i64),
                    Type::Primitive(Primitive::Long(false)),
                ),
            ));

            // since external declarations don't emit any code it is fine to assume that this label
            // doesn't have run-time addressing
            let reg = Register::Label(LabelRegister::Var(label_name, ty, false));

            var_symbol.borrow_mut().set_reg(reg);
        }
    }
    fn init_global_var(&mut self, name: String, ty: Type, var_symbol: SymbolRef, init: Init) {
        var_symbol
            .borrow_mut()
            .set_reg(Register::Label(LabelRegister::Var(name, ty.clone(), false)));

        match init {
            Init::Scalar(expr) => {
                let value_reg = self.execute_global_expr(expr);

                self.write_out(Lir::GlobalInit(ty, value_reg));
            }
            Init::Aggr(list) => {
                let mut size = ty.size() as i64;
                let mut prev_offset: i64 = 0;

                for (expr, offset) in list {
                    let value_reg = self.execute_global_expr(expr);
                    let value_type = value_reg.get_type();

                    // fill gap in offset with zero
                    let diff = offset as i64 - prev_offset;
                    if diff != 0 {
                        self.write_out(Lir::GlobalInit(
                            Type::Primitive(Primitive::Void),
                            StaticRegister::Literal(
                                LiteralKind::Signed(diff),
                                Type::Primitive(Primitive::Long(false)),
                            ),
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
                        StaticRegister::Literal(
                            LiteralKind::Signed(size),
                            Type::Primitive(Primitive::Long(false)),
                        ),
                    ));
                }
            }
        }
    }

    fn declaration(&mut self, func: &mut Function, declarators: Vec<Declarator>) {
        for declarator in declarators {
            let var_symbol = declarator.entry.borrow().clone();

            match var_symbol.storage_class {
                Some(StorageClass::Extern | StorageClass::Static) => {
                    let name = declarator.name.unwrap_string();
                    let label_name = if var_symbol.is_static() {
                        self.static_labels.update(name)
                    } else {
                        name
                    };

                    // declarations are declared after function but register has to be known inside
                    // of function already, so have to set it now
                    declarator
                        .entry
                        .borrow_mut()
                        .set_reg(Register::Label(LabelRegister::Var(
                            label_name.clone(),
                            var_symbol.qtype.ty.clone(),
                            var_symbol.is_extern(),
                        )));

                    func.static_declarations.push((label_name, declarator));
                }
                None | Some(StorageClass::Auto | StorageClass::Register)
                    if declarator.name == var_symbol.token && !var_symbol.qtype.ty.is_func() =>
                {
                    self.declare_var(func, declarator.entry, declarator.init)
                }
                // only function-declarations can be redeclared inside of a function body
                _ if var_symbol.reg.is_none() => {
                    declarator
                        .entry
                        .borrow_mut()
                        .set_reg(Register::Label(LabelRegister::Var(
                            declarator.name.unwrap_string(),
                            var_symbol.qtype.ty.clone(),
                            var_symbol.is_extern(),
                        )))
                }
                _ => (),
            }
        }
    }

    fn declare_var(&mut self, func: &mut Function, var_symbol: SymbolRef, init: Option<Init>) {
        let ty = var_symbol.borrow().qtype.ty.clone();
        let size = align(ty.size(), &ty);

        let reg = Register::Stack(StackRegister::new(&mut func.current_bp_offset, ty));
        var_symbol.borrow_mut().set_reg(reg);

        if let Some(init) = init {
            match init {
                Init::Scalar(expr) => self.init_scalar(func, var_symbol, expr, 0),
                Init::Aggr(list) => {
                    // first overwrite all entries with 0
                    self.clear_mem(Rc::clone(&var_symbol), size);

                    for (expr, offset) in list {
                        self.init_scalar(func, Rc::clone(&var_symbol), expr, offset)
                    }
                }
            }
        }
    }

    fn init_scalar(&mut self, func: &mut Function, var_symbol: SymbolRef, expr: Expr, offset: usize) {
        let value_reg = self.execute_expr(func, expr);
        let mut var_reg = var_symbol.borrow().get_reg();

        var_reg.set_type(value_reg.get_type());
        if let Register::Stack(stack_reg) = &mut var_reg {
            stack_reg.bp_offset -= offset;

            let value_reg = self.cg_assign(var_reg, value_reg);
            self.free(value_reg);
        } else {
            unreachable!("local variables can only be located on stack")
        }
    }

    fn clear_mem(&mut self, var_symbol: SymbolRef, amount: usize) {
        // writes 0 to stack until amount == 0
        // eax value that gets written
        // ecx amount
        // rdi at memory pos
        let var_reg = var_symbol.borrow().get_reg();

        let eax_reg = Register::Return(Type::Primitive(Primitive::Char(false)));
        let ecx_reg = Register::Arg(ArgRegister::new(
            3,
            Type::Primitive(Primitive::Int(false)),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        let rdi_reg = Register::Arg(ArgRegister::new(
            0,
            Type::Primitive(Primitive::Long(false)),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Lir::Mov(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            eax_reg.clone(),
        ));
        self.write_out(Lir::Mov(
            Register::Literal(
                LiteralKind::Signed(amount as i64),
                Type::Primitive(Primitive::Long(false)),
            ),
            ecx_reg.clone(),
        ));
        self.write_out(Lir::Load(var_reg, rdi_reg.clone()));
        self.write_out(Lir::Rep);

        self.free(eax_reg);
        self.free(ecx_reg);
        self.free(rdi_reg);
    }

    fn init_arg(&mut self, func: &mut Function, var_symbol: SymbolRef, arg_reg: Register) {
        self.declare_var(func, Rc::clone(&var_symbol), None);

        let reg = self.cg_assign(var_symbol.borrow().get_reg(), arg_reg);
        self.free(reg);
    }

    fn function_definition(&mut self, mut func: Function, func_symbol: SymbolRef, stmts: Vec<Stmt>) {
        func_symbol
            .borrow_mut()
            .set_reg(Register::Label(LabelRegister::Var(
                func.name.clone(),
                func.return_type.ty.clone(),
                // since function is defined in this translation unit,
                // it doesn't have to be accessed using `@GOTPCREL`
                false,
            )));

        func.epilogue_index = create_label(&mut self.label_index);

        // create a label for all goto-labels inside a function
        for value in func.labels.values_mut() {
            *value = create_label(&mut self.label_index);
        }

        // generate function code
        self.cg_func_preamble(&mut func, func_symbol);
        self.cg_stmts(&mut func, stmts);
        self.cg_func_postamble(&func);

        // declare all statically linked declarations that are declared inside of function-body
        for (label_name, declarator) in func.static_declarations {
            let var_symbol = declarator.entry.borrow().clone();

            if declarator.name == var_symbol.token && !var_symbol.is_extern() {
                self.declare_global_var(
                    label_name,
                    var_symbol.qtype.ty,
                    declarator.entry,
                    declarator.init,
                )
            }
        }
    }
    fn cg_func_preamble(&mut self, func: &mut Function, func_symbol: SymbolRef) {
        self.write_out(Lir::FuncSetup(
            func.name.clone(),
            func.stack_size,
            func_symbol.borrow().is_static() || (!func_symbol.borrow().is_extern() && func.is_inline),
        ));

        // initialize parameters
        for (i, param_symbol) in func.params.clone().into_iter().enumerate() {
            let ty = param_symbol.borrow().qtype.ty.clone();
            if i < ARG_REGS.len() {
                let arg = Register::Arg(ArgRegister::new(
                    i,
                    ty,
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                self.init_arg(func, param_symbol, arg);
            } else {
                // if not in designated arg-register get from stack
                let reg = Register::Temp(TempRegister::new(
                    ty,
                    &mut self.interval_counter,
                    self.instr_counter,
                ));
                let pushed = Register::Stack(StackRegister::new_pushed(i));

                self.write_out(Lir::Mov(pushed, reg.clone()));
                self.init_arg(func, param_symbol, reg);
            }
        }
    }
    fn cg_func_postamble(&mut self, func: &Function) {
        self.write_out(Lir::LabelDefinition(func.epilogue_index));

        self.write_out(Lir::FuncTeardown(func.stack_size))
    }

    pub fn block(&mut self, func: &mut Function, statements: Vec<Stmt>) {
        self.cg_stmts(func, statements)
    }

    fn cg_literal(&mut self, literal: LiteralKind, ty: Type) -> Register {
        let overflow = literal.type_overflow(&Type::Primitive(Primitive::Int(false)));
        let literal_reg = Register::Literal(literal, ty);

        // 64bit literals are only allowed to move to scratch-register
        if overflow {
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
            ExprKind::Literal(literal) => StaticRegister::Literal(literal, expr.qtype.ty),
            ExprKind::Cast { expr, new_type, .. } => {
                let mut reg = self.execute_global_expr(*expr);
                reg.set_type(new_type);
                reg
            }
            ExprKind::Unary { token, right } => {
                let mut reg = self.execute_global_expr(*right);
                match token.kind {
                    TokenKind::Amp => {
                        reg.set_type(Type::Pointer(Box::new(QualType::new(reg.get_type()))))
                    }
                    TokenKind::Star => reg.set_type(expr.qtype.ty),
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

                        reg.set_type(member_type.ty);
                        match reg {
                            StaticRegister::Label(label_reg) => {
                                StaticRegister::LabelOffset(label_reg, offset as i64, TokenKind::Plus)
                            }
                            StaticRegister::LabelOffset(reg, existant_offset, _) => {
                                let offset = existant_offset.wrapping_add(offset as i64);
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
                        reg.set_type(member_type.ty);
                        reg
                    }
                    _ => unreachable!("no members in type {:?}", reg.get_type()),
                }
            }
            ExprKind::Binary { left, token, right } => {
                let left = self.execute_global_expr(*left);
                let right = self.execute_global_expr(*right);

                match (left, right) {
                    (StaticRegister::Label(reg), StaticRegister::Literal(literal, _))
                    | (StaticRegister::Literal(literal, _), StaticRegister::Label(reg)) => {
                        let n = match literal {
                            LiteralKind::Signed(n) => n,
                            // nobody needs this big of an offset anyway
                            LiteralKind::Unsigned(n) => n as i64,
                        };
                        StaticRegister::LabelOffset(reg, n, token.kind)
                    }

                    (
                        StaticRegister::LabelOffset(reg, offset, _),
                        StaticRegister::Literal(literal, _),
                    )
                    | (
                        StaticRegister::Literal(literal, _),
                        StaticRegister::LabelOffset(reg, offset, _),
                    ) => {
                        let offset = match literal {
                            LiteralKind::Signed(n) => n.wrapping_add(offset as i64),
                            LiteralKind::Unsigned(n) => (n as i64).wrapping_add(offset as i64),
                        };

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
                if let Register::Label(reg) = var_symbol.borrow().get_reg() {
                    StaticRegister::Label(reg)
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!("non global-constant expr"),
        }
    }
    pub fn execute_expr(&mut self, func: &mut Function, expr: Expr) -> Register {
        match expr.kind {
            ExprKind::Binary { left, token, right } => {
                let left_reg = self.execute_expr(func, *left);
                let right_reg = self.execute_expr(func, *right);

                self.cg_binary(left_reg, &token.kind, right_reg)
            }
            ExprKind::Literal(literal) => self.cg_literal(literal, expr.qtype.ty),
            ExprKind::Unary { token, right } => self.cg_unary(func, token.kind, *right, expr.qtype.ty),
            ExprKind::Logical { left, token, right } => self.cg_logical(func, *left, token.kind, *right),
            ExprKind::Comparison { left, token, right } => self.compare(func, *left, token.kind, *right),
            ExprKind::Assign { l_expr, r_expr } => {
                let left_reg = self.execute_expr(func, *l_expr);
                let right_reg = self.execute_expr(func, *r_expr);

                self.cg_assign(left_reg, right_reg)
            }
            ExprKind::CompoundAssign { expr, tmp_symbol } => {
                self.cg_comp_assign(func, *expr, tmp_symbol)
            }
            ExprKind::Ident(var_symbol) => self.ident(var_symbol),
            ExprKind::Call { caller, args } => self.cg_call(func, *caller, args, expr.qtype.ty),
            ExprKind::Cast { expr, direction, new_type } => {
                self.cg_cast(func, new_type, *expr, direction)
            }
            ExprKind::Scale { expr, direction, by_amount, .. } => {
                self.cg_scale(func, direction, *expr, by_amount)
            }
            ExprKind::String(name) => self.cg_string(name),
            ExprKind::MemberAccess { expr, member } => {
                let reg = self.execute_expr(func, *expr);
                self.cg_member_access(reg, &member, true)
            }
            ExprKind::Ternary { cond, true_expr, false_expr, .. } => {
                self.cg_ternary(func, *cond, *true_expr, *false_expr)
            }
            ExprKind::Comma { left, right } => self.cg_comma(func, *left, *right),
            ExprKind::Nop => Register::Void,
        }
    }
    fn ident(&mut self, var_symbol: SymbolRef) -> Register {
        let mut reg = var_symbol.borrow().get_reg();

        // since runtime-address stored in GlobalOffsetTable returns pointer to that address it has
        // to be dereferences first
        if let Register::Label(LabelRegister::Var(.., true)) = &reg {
            let original_type = reg.get_type();
            reg.set_type(Type::Pointer(Box::new(QualType::new(original_type.clone()))));
            self.cg_deref(reg, original_type)
        } else {
            reg
        }
    }
    fn cg_comma(&mut self, func: &mut Function, left: Expr, right: Expr) -> Register {
        let reg = self.execute_expr(func, left);
        self.free(reg);

        self.execute_expr(func, right)
    }

    fn cg_ternary(
        &mut self,
        func: &mut Function,
        cond: Expr,
        true_expr: Expr,
        false_expr: Expr,
    ) -> Register {
        let mut cond_reg = self.execute_expr(func, cond);
        cond_reg = convert_reg!(self, cond_reg, Register::Literal(..));

        let done_label = create_label(&mut self.label_index);
        let else_label = create_label(&mut self.label_index);

        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            cond_reg.clone(),
        ));
        self.write_out(Lir::JmpCond("e", else_label));
        self.free(cond_reg);

        let result = Register::Temp(TempRegister::new(
            true_expr.clone().qtype.ty,
            &mut self.interval_counter,
            self.instr_counter,
        ));
        let true_reg = self.execute_expr(func, true_expr);

        // copy both expressions into result register
        self.write_out(Lir::Mov(true_reg.clone(), result.clone()));
        self.free(true_reg);

        self.write_out(Lir::Jmp(done_label));
        self.write_out(Lir::LabelDefinition(else_label));

        let false_reg = self.execute_expr(func, false_expr);

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
                    Register::Literal(
                        LiteralKind::Signed(offset as i64),
                        Type::Primitive(Primitive::Int(false)),
                    ),
                    address,
                )
            } else {
                address
            };

            result.set_type(member_type.ty);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else if let Type::Union(s) = reg.get_type() {
            let member_type = s.member_type(member);

            let mut result = self.cg_address_at(reg, free);

            result.set_type(member_type.ty);
            result.set_value_kind(ValueKind::Lvalue);
            result
        } else {
            unreachable!("{:?}", reg.get_type())
        }
    }
    fn cg_comp_assign(&mut self, func: &mut Function, expr: Expr, tmp_symbol: SymbolRef) -> Register {
        // only have to declare tmp var, since compound assign is only syntax sugar
        self.declare_var(func, tmp_symbol, None);
        self.execute_expr(func, expr)
    }
    fn cg_string(&mut self, name: String) -> Register {
        Register::Label(LabelRegister::String(self.const_labels[&name]))
    }
    fn cg_scale(
        &mut self,
        func: &mut Function,
        direction: ScaleDirection,
        expr: Expr,
        by_amount: usize,
    ) -> Register {
        let value_reg = self.execute_expr(func, expr);
        let value_reg = self.convert_to_rval(value_reg);
        let by_amount =
            Register::Literal(LiteralKind::new(by_amount as u64, &None), value_reg.get_type());

        match direction {
            ScaleDirection::Up => self.cg_mult(by_amount, value_reg),
            ScaleDirection::Down => {
                let by_amount = self.make_temp(by_amount);
                self.cg_div(value_reg, by_amount, false)
            }
        }
    }
    fn cg_cast(
        &mut self,
        func: &mut Function,
        new_type: Type,
        expr: Expr,
        direction: CastDirection,
    ) -> Register {
        match direction {
            CastDirection::Up => self.cg_cast_up(func, expr, new_type),
            CastDirection::Down | CastDirection::Equal => self.cg_cast_type(func, expr, new_type),
        }
    }
    // only changes the type of the register, doesnt generate any casting asm
    fn cg_cast_type(&mut self, func: &mut Function, expr: Expr, new_type: Type) -> Register {
        let mut value_reg = self.execute_expr(func, expr);
        value_reg.set_type(new_type);

        value_reg
    }
    fn cg_cast_up(&mut self, func: &mut Function, expr: Expr, new_type: Type) -> Register {
        let mut value_reg = self.execute_expr(func, expr);

        if matches!(
            value_reg,
            Register::Temp(..) | Register::Stack(..) | Register::Label(..)
        ) {
            let dest_reg = Register::Temp(TempRegister::new(
                new_type.clone(),
                &mut self.interval_counter,
                self.instr_counter,
            ));

            if value_reg.get_type().is_unsigned() {
                // INFO: `movz` only used for smaller than 32-bit regs:
                // A special case to note is that a mov to write a 32-bit value
                // into a register also zeroes the upper 32 bits of the register by default,
                // i.e does an implicit zero-extend to bitwidth q
                // So `movzlq` is illegal and is done automatically in a normal `mov`
                if value_reg.get_type().size() < 4 {
                    self.write_out(Lir::Movz(value_reg.clone(), dest_reg.clone()));
                } else {
                    // convert registers since otherwise will read memory that isnt
                    // that doesnt belong to value_reg: casting unsigned int to long
                    // int a: -4(%rbp), 4 bytes allocate
                    // `movq -4(%rbp), %r10`, would read 8 bytes
                    value_reg = convert_reg!(self, value_reg, Register::Stack(..) | Register::Label(..));

                    value_reg.set_type(new_type);
                    self.write_out(Lir::Mov(value_reg.clone(), dest_reg.clone()))
                }
            } else {
                self.write_out(Lir::Movs(value_reg.clone(), dest_reg.clone()));
            }

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
    fn cg_call(
        &mut self,
        func: &mut Function,
        caller: Expr,
        args: Vec<Expr>,
        return_type: Type,
    ) -> Register {
        self.write_out(Lir::SaveRegs);

        let args_len = args.len();

        // align stack if pushes args
        if args_len >= ARG_REGS.len() && args_len % 2 != 0 {
            self.write_out(Lir::SubSp(8));
        }
        let mut arg_regs = Vec::new();

        // moving the arguments into their designated registers
        for (i, expr) in args.into_iter().enumerate().rev() {
            let mut reg = self.execute_expr(func, expr);
            let ty = reg.get_type();

            // put first six registers into designated argument-registers; others pushed onto stack
            if i < ARG_REGS.len() {
                let arg = Register::Arg(ArgRegister::new(
                    i,
                    ty,
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

        let caller = self.execute_expr(func, caller);
        self.write_out(Lir::Call(caller.clone()));
        self.free(caller);

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

    fn cg_logical(
        &mut self,
        func: &mut Function,
        left: Expr,
        operator: TokenKind,
        right: Expr,
    ) -> Register {
        match operator {
            TokenKind::AmpAmp => self.cg_and(func, left, right),
            TokenKind::PipePipe => self.cg_or(func, left, right),
            _ => unreachable!(),
        }
    }
    fn compare(
        &mut self,
        func: &mut Function,
        left: Expr,
        operator: TokenKind,
        right: Expr,
    ) -> Register {
        let left_reg = self.execute_expr(func, left);
        let right_reg = self.execute_expr(func, right);

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

        right.set_type(Type::Primitive(Primitive::Int(false)));
        self.write_out(Lir::Movz(
            Register::Return(Type::Primitive(Primitive::Char(false))),
            right.clone(),
        ));

        self.free(left);
        right
    }

    fn cg_or(&mut self, func: &mut Function, left: Expr, right: Expr) -> Register {
        let mut left = self.execute_expr(func, left);
        left = convert_reg!(self, left, Register::Literal(..));

        let true_label = create_label(&mut self.label_index);

        // jump to true label left is true => short circuit
        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            left.clone(),
        ));
        self.write_out(Lir::JmpCond("ne", true_label));
        self.free(left);

        let mut right = self.execute_expr(func, right);
        right = convert_reg!(self, right, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if right is false we know expression is false
        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            right.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(right);

        let done_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int(false)),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        // if expression true write 1 in result and skip false label
        self.write_out(Lir::LabelDefinition(true_label));
        self.write_out(Lir::Mov(
            Register::Literal(LiteralKind::Signed(1), Type::Primitive(Primitive::Int(false))),
            result.clone(),
        ));

        self.write_out(Lir::Jmp(done_label));

        self.write_out(Lir::LabelDefinition(false_label));
        self.write_out(Lir::Mov(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            result.clone(),
        ));

        self.write_out(Lir::LabelDefinition(done_label));

        result
    }
    fn cg_and(&mut self, func: &mut Function, left: Expr, right: Expr) -> Register {
        let left = self.execute_expr(func, left);
        let left = convert_reg!(self, left, Register::Literal(..));

        let false_label = create_label(&mut self.label_index);

        // if left is false expression is false, we jump to false label
        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            left.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(left);

        // left is true if right false jump to false label
        let right = self.execute_expr(func, right);
        let right = convert_reg!(self, right, Register::Literal(..));

        self.write_out(Lir::Cmp(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            right.clone(),
        ));
        self.write_out(Lir::JmpCond("e", false_label));
        self.free(right);

        // if no prior jump was taken expression is true
        let true_label = create_label(&mut self.label_index);
        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int(false)),
            &mut self.interval_counter,
            self.instr_counter,
        ));
        self.write_out(Lir::Mov(
            Register::Literal(LiteralKind::Signed(1), Type::Primitive(Primitive::Int(false))),
            result.clone(),
        ));
        self.write_out(Lir::Jmp(true_label));

        self.write_out(Lir::LabelDefinition(false_label));
        self.write_out(Lir::Mov(
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            result.clone(),
        ));

        self.write_out(Lir::LabelDefinition(true_label));

        result
    }
    fn cg_unary(
        &mut self,
        func: &mut Function,
        operator: TokenKind,
        right: Expr,
        new_type: Type,
    ) -> Register {
        let mut reg = self.execute_expr(func, right);
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
            Register::Literal(LiteralKind::Signed(0), Type::Primitive(Primitive::Int(false))),
            reg.clone(),
        ));
        self.write_out(Lir::Set("sete"));

        let result = Register::Temp(TempRegister::new(
            Type::Primitive(Primitive::Int(false)),
            &mut self.interval_counter,
            self.instr_counter,
        ));

        self.write_out(Lir::Movz(
            Register::Return(Type::Primitive(Primitive::Char(false))),
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
            Type::Pointer(Box::new(QualType::new(reg.get_type()))),
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

    fn cg_div(&mut self, left: Register, right: Register, is_mod: bool) -> Register {
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

        self.write_out(Lir::Div(right.clone()));

        if is_mod {
            // rax % right => rdx
            self.write_out(Lir::Mov(rdx_reg.clone(), right.clone()));
        } else {
            // rax / right => rax
            self.write_out(Lir::Mov(Register::Return(right.get_type()), right.clone()));
        }

        self.free(rdx_reg);
        self.free(left);
        right
    }

    fn cg_bit_op(&mut self, left: Register, right: Register, op: &TokenKind) -> Register {
        let right = convert_reg!(
            self,
            right,
            Register::Stack(..) | Register::Label(..) | Register::Literal(..)
        );

        self.write_out(match op {
            TokenKind::Xor => Lir::Xor(left.clone(), right.clone()),
            TokenKind::Pipe => Lir::Or(left.clone(), right.clone()),
            TokenKind::Amp => Lir::And(left.clone(), right.clone()),
            _ => unreachable!("not binary bit-operator"),
        });

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

        cl_reg.set_type(Type::Primitive(Primitive::Char(false)));
        self.write_out(Lir::Shift(direction, cl_reg.clone(), left.clone()));

        self.free(cl_reg);

        left
    }
    fn cg_binary(&mut self, left_reg: Register, token: &TokenKind, right_reg: Register) -> Register {
        let left_reg = self.convert_to_rval(left_reg);
        let right_reg = self.convert_to_rval(right_reg);

        match token {
            TokenKind::Plus => self.cg_add(left_reg, right_reg),
            TokenKind::Minus => self.cg_sub(left_reg, right_reg),
            TokenKind::Star => self.cg_mult(left_reg, right_reg),
            TokenKind::Slash => self.cg_div(left_reg, right_reg, false),
            TokenKind::Mod => self.cg_div(left_reg, right_reg, true),
            TokenKind::Xor => self.cg_bit_op(left_reg, right_reg, token),
            TokenKind::Pipe => self.cg_bit_op(left_reg, right_reg, token),
            TokenKind::Amp => self.cg_bit_op(left_reg, right_reg, token),
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
                    IntervalEntry::new(reg.start_idx, self.instr_counter, None, reg.ty),
                );
            }
            Register::Arg(reg) => {
                assert!(!self.live_intervals.contains_key(&reg.id));
                self.live_intervals.insert(
                    reg.id,
                    IntervalEntry::new(reg.start_idx, self.instr_counter, Some(reg.reg), reg.ty),
                );
            }
            _ => (),
        }
    }
}

pub fn align(offset: usize, ty: &Type) -> usize {
    let size = match ty {
        Type::Array(of, _) => of.ty.size(),
        _ => ty.size(),
    };
    align_by(offset, size)
}
