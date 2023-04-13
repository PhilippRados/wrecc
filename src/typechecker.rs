use crate::codegen::codegen::align;
use crate::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(PartialEq, Debug)]
enum ScopeKind {
    Global,
    Loop,
    // (function name, return type)
    Function(Token, NEWTypes),
    // (case-values in current switch, indicator if default exists)
    Switch(Vec<i64>, bool),
}
macro_rules! find_scope {
    ($scope:expr,$($expected:pat_param)|+) => {{
        let mut result = None;
        for current in $scope.0.iter_mut().rev() {
            if matches!(current, $($expected)|+) {
                result = Some(current);
                break;
            }
        }
        result
    }};
}

// vector to go through and check if certain statements are
// enclosed by others. eg: return only in functions, break only in switch/loops
#[derive(PartialEq, Debug)]
struct ScopeLevel(Vec<ScopeKind>);
impl ScopeLevel {
    fn increment_stack_size(&mut self, type_decl: &NEWTypes, env: &mut Vec<Symbols>) {
        let ScopeKind::Function(func_name, _) = find_scope!(self, ScopeKind::Function(..))
            .expect("can only be called inside a function") else {unreachable!()};
        let func_symbol = env
            .get_mut(func_name.token.get_index())
            .expect("valid table index");

        let mut size = func_symbol.unwrap_func().get_stack_size() + type_decl.size();
        size = align(size, type_decl);

        func_symbol.unwrap_func().set_stack_size(size);
    }
}
pub struct TypeChecker {
    scope: ScopeLevel,
    env: Vec<Symbols>,
    returns_all_paths: bool,
    const_labels: HashMap<String, usize>,
    const_label_count: usize,

    // save encountered switch-statements together with
    // with info about their cases and defaults, so that
    // codegen is simpler
    switches: Vec<(Vec<i64>, bool)>,
}
macro_rules! cast {
    ($ex:expr,$new_type:expr,$direction:path) => {
        *$ex = Expr {
            kind: ExprKind::Cast {
                token: Token::default(TokenType::LeftParen),
                direction: Some($direction),
                new_type: $new_type,
                expr: Box::new($ex.clone()),
            },
            type_decl: Some($new_type),
            value_kind: $ex.value_kind.clone(),
        }
    };
}

impl TypeChecker {
    pub fn new(env: Vec<Symbols>) -> Self {
        TypeChecker {
            env,
            scope: ScopeLevel(vec![ScopeKind::Global]),
            returns_all_paths: false,
            const_labels: HashMap::new(),
            const_label_count: 0,
            switches: vec![],
        }
    }
    pub fn check(
        mut self,
        statements: &mut Vec<Stmt>,
    ) -> Option<(HashMap<String, usize>, Vec<Symbols>, Vec<(Vec<i64>, bool)>)> {
        match self.check_statements(statements) {
            Ok(_) => Some((self.const_labels, self.env, self.switches)),
            Err(_) => None,
        }
    }
    fn check_statements(&mut self, statements: &mut Vec<Stmt>) -> Result<(), Error> {
        let mut result = Ok(());
        for s in statements {
            if let Err(e) = self.visit(s) {
                e.print_error();
                result = Err(Error::Indicator);
            }
        }

        result
    }
    fn visit(&mut self, statement: &mut Stmt) -> Result<(), Error> {
        match statement {
            Stmt::DeclareVar(type_decl, var_name) => self.declare_var(type_decl, var_name),
            Stmt::InitVar(type_decl, name, expr) => self.init_var(type_decl, name, expr),
            Stmt::InitList(type_decl, var_name, exprs) => {
                self.init_list(type_decl, var_name, exprs)
            }
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(return_type, name, params.clone(), body)
            }
            Stmt::Return(keyword, value) => self.return_statement(keyword, value),
            Stmt::Expr(expr) => match self.expr_type(expr) {
                Ok(_) => Ok(()),
                Err(e) => Err(e),
            },
            Stmt::Block(statements) => self.block(statements),
            Stmt::If(keyword, cond, then_branch, else_branch) => {
                self.if_statement(keyword, cond, then_branch, else_branch)
            }
            Stmt::While(left_paren, cond, body) => self.while_statement(left_paren, cond, body),
            Stmt::Do(keyword, body, cond) => self.do_statement(keyword, body, cond),
            Stmt::For(left_paren, init, cond, inc, body) => {
                self.for_statement(left_paren, init, cond, inc, body)
            }
            Stmt::Break(keyword) => self.break_statement(keyword),
            Stmt::Continue(keyword) => self.continue_statement(keyword),
            Stmt::Switch(keyword, cond, body) => self.switch_statement(keyword, cond, body),
            Stmt::Case(keyword, value, body) => self.case_statement(keyword, value, body),
            Stmt::Default(keyword, body) => self.default_statement(keyword, body),
        }
    }
    fn switch_statement(
        &mut self,
        token: &Token,
        cond: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_integer() {
            return Err(Error::new(
                token,
                &format!(
                    "Switch conditional must be integer type, found '{}'",
                    cond_type,
                ),
            ));
        }
        self.scope.0.push(ScopeKind::Switch(vec![], false));
        let err = self.visit(body);

        let Some(ScopeKind::Switch(cases, defaults)) = self.scope.0.pop() else {
            unreachable!("all other scopes should be popped off by themselves")
        };

        self.switches.push((cases, defaults));

        err?;

        // TODO: check returns in all paths
        // self.self.returns_all_paths = false;

        Ok(())
    }
    fn case_statement(
        &mut self,
        token: &Token,
        value: &mut i64,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(cases, _)) => {
                if !cases.contains(value) {
                    cases.push(*value)
                } else {
                    return Err(Error::new(
                        token,
                        &format!("Duplicate 'case'-statement with value {}", *value),
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    token,
                    "'case'-statements have to be inside a 'switch'-statement",
                ));
            }
        }

        self.visit(body)?;
        Ok(())
    }
    fn default_statement(&mut self, token: &Token, body: &mut Stmt) -> Result<(), Error> {
        match find_scope!(&mut self.scope, ScopeKind::Switch(..)) {
            Some(ScopeKind::Switch(_, defaults)) => {
                if !*defaults {
                    *defaults = true
                } else {
                    return Err(Error::new(
                        token,
                        "Can't have multiple 'default'-statements inside a 'switch'-statement",
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    token,
                    "'default'-statements have to be inside a 'switch'-statement",
                ));
            }
        }
        self.visit(body)?;
        Ok(())
    }
    fn do_statement(
        &mut self,
        token: &Token,
        body: &mut Stmt,
        cond: &mut Expr,
    ) -> Result<(), Error> {
        self.scope.0.push(ScopeKind::Loop);
        self.visit(body)?;
        self.scope.0.pop();

        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                token,
                &format!("Conditional expected scalar type found '{}'", cond_type),
            ));
        }

        self.returns_all_paths = false;

        Ok(())
    }
    fn for_statement(
        &mut self,
        left_paren: &Token,
        init: &mut Option<Box<Stmt>>,
        cond: &mut Option<Expr>,
        inc: &mut Option<Expr>,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        if let Some(init) = init {
            self.visit(&mut *init)?;
        }
        if let Some(cond) = cond {
            let cond_type = self.expr_type(cond)?;
            if !cond_type.is_scalar() {
                return Err(Error::new(
                    left_paren,
                    &format!("Conditional expected scalar type found '{}'", cond_type),
                ));
            }
        }

        self.scope.0.push(ScopeKind::Loop);
        self.visit(body)?;

        if let Some(inc) = inc {
            self.expr_type(inc)?;
        }

        self.scope.0.pop();

        self.returns_all_paths = false;
        Ok(())
    }
    fn break_statement(&mut self, token: &Token) -> Result<(), Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop | ScopeKind::Switch(..)).is_none() {
            Err(Error::new(
                token,
                "'break' must be inside loop/switch-statement",
            ))
        } else {
            Ok(())
        }
    }
    fn continue_statement(&mut self, token: &Token) -> Result<(), Error> {
        if find_scope!(&mut self.scope, ScopeKind::Loop).is_none() {
            Err(Error::new(
                token,
                "'continue' statement must be inside loop",
            ))
        } else {
            Ok(())
        }
    }

    fn while_statement(
        &mut self,
        left_paren: &Token,
        cond: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                left_paren,
                &format!("Conditional expected scalar type found '{}'", cond_type),
            ));
        }

        self.scope.0.push(ScopeKind::Loop);
        self.visit(body)?;
        self.scope.0.pop();

        self.returns_all_paths = false;
        Ok(())
    }
    fn declare_var(&mut self, type_decl: &mut NEWTypes, var_name: &Token) -> Result<(), Error> {
        if type_decl.is_void() {
            return Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", var_name.unwrap_string()),
            ));
        }

        if !self
            .env
            .get(var_name.token.get_index())
            .unwrap()
            .is_global()
        {
            self.scope.increment_stack_size(type_decl, &mut self.env);
        }

        Ok(())
    }
    fn check_type_compatibility(
        &self,
        token: &Token,
        left: &NEWTypes,
        right: &NEWTypes,
    ) -> Result<(), Error> {
        if left.is_void() || right.is_void() || !left.type_compatible(right) {
            Err(Error::new(
                token,
                &format!("Can't assign to type '{}' with type '{}'", left, right),
            ))
        } else {
            Ok(())
        }
    }
    fn init_list(
        &mut self,
        type_decl: &mut NEWTypes,
        var_name: &Token,
        exprs: &mut [Expr],
    ) -> Result<(), Error> {
        // type-check all assigns
        let mut types = vec![];
        for e in exprs.iter_mut() {
            types.push(self.expr_type(e)?);
        }
        // check if every expression is constant if global
        if self
            .env
            .get(var_name.token.get_index())
            .unwrap()
            .is_global()
        {
            for e in exprs.iter().by_ref() {
                if let ExprKind::Assign { r_expr, .. } = &e.kind {
                    if !is_constant(r_expr) {
                        return Err(Error::new(
                            var_name,
                            "Global variables can only be initialized to compile-time constants",
                        ));
                    }
                } else {
                    unreachable!()
                }
            }
        } else {
            self.scope.increment_stack_size(type_decl, &mut self.env);
        }

        Ok(())
    }
    fn init_var(
        &mut self,
        type_decl: &mut NEWTypes,
        var_name: &Token,
        expr: &mut Expr,
    ) -> Result<(), Error> {
        let mut value_type = self.expr_type(expr)?;
        let is_global = self
            .env
            .get(var_name.token.get_index())
            .unwrap()
            .is_global();

        crate::arr_decay!(value_type, expr, var_name, is_global);
        self.check_type_compatibility(var_name, type_decl, &value_type)?;
        self.maybe_cast(type_decl, &value_type, expr);

        if is_global {
            if !is_constant(expr) {
                return Err(Error::new(
                    var_name,
                    "Global variables can only be initialized to compile-time constants",
                ));
            }
        } else {
            self.scope.increment_stack_size(type_decl, &mut self.env);
        }

        Ok(())
    }
    // TODO: display warning when casting down
    fn explicit_cast(
        &mut self,
        token: &Token,
        expr: &mut Expr,
        new_type: &NEWTypes,
        direction: &mut Option<CastDirection>,
    ) -> Result<NEWTypes, Error> {
        let mut old_type = self.expr_type(expr)?;

        crate::arr_decay!(old_type, expr, token, self.is_global());

        if !old_type.is_scalar() || !new_type.is_scalar() {
            return Err(Error::new(
                token,
                &format!(
                    "Invalid cast from '{}' to '{}'. '{}' is not a scalar type",
                    old_type,
                    new_type,
                    if !old_type.is_scalar() {
                        &old_type
                    } else {
                        new_type
                    }
                ),
            ));
        }

        *direction = Some(match old_type.size().cmp(&new_type.size()) {
            Ordering::Less => CastDirection::Up,
            Ordering::Greater => CastDirection::Down,
            Ordering::Equal => CastDirection::Equal,
        });
        Ok(new_type.clone())
    }
    fn maybe_cast(&self, new_type: &NEWTypes, old_type: &NEWTypes, expr: &mut Expr) {
        match old_type.size().cmp(&new_type.size()) {
            Ordering::Less => cast!(expr, new_type.clone(), CastDirection::Up),
            Ordering::Greater => cast!(expr, new_type.clone(), CastDirection::Down),
            Ordering::Equal => (),
        }
    }
    fn if_statement(
        &mut self,
        keyword: &Token,
        cond: &mut Expr,
        then_branch: &mut Stmt,
        else_branch: &mut Option<Stmt>,
    ) -> Result<(), Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                keyword,
                &format!(
                    "Expected scalar type inside of condition, found '{}'",
                    cond_type
                ),
            ));
        }

        self.visit(then_branch)?;
        let then_return = self.returns_all_paths;
        self.returns_all_paths = false;

        if let Some(else_branch) = else_branch {
            self.visit(else_branch)?;
            let else_return = self.returns_all_paths;

            if !then_return || !else_return {
                self.returns_all_paths = false;
            }
        }
        Ok(())
    }
    fn function_definition(
        &mut self,
        return_type: &mut NEWTypes,
        name_token: &Token,
        params: Vec<(NEWTypes, Token)>,
        body: &mut Vec<Stmt>,
    ) -> Result<(), Error> {
        // have to push scope before declaring local variables
        self.scope
            .0
            .push(ScopeKind::Function(name_token.clone(), return_type.clone()));
        for (type_decl, _) in params.iter().by_ref() {
            self.scope.increment_stack_size(type_decl, &mut self.env);
        }

        // check function body
        let err = self.block(body);
        self.scope.0.pop();

        err?;

        self.main_returns_int(name_token, return_type)?;
        self.implicit_return_main(name_token, body);

        // align function stack by 16Bytes
        let size = self
            .env
            .get_mut(name_token.token.get_index())
            .unwrap()
            .unwrap_func()
            .get_stack_size();
        self.env
            .get_mut(name_token.token.get_index())
            .unwrap()
            .unwrap_func()
            .set_stack_size(align_by(size, 16));

        if !return_type.is_void() && !self.returns_all_paths {
            Err(Error::new(
                name_token,
                "Non-void function doesn't return in all code paths",
            ))
        } else {
            self.returns_all_paths = false;
            Ok(())
        }
    }
    fn main_returns_int(&self, name_token: &Token, return_type: &NEWTypes) -> Result<(), Error> {
        if name_token.unwrap_string() == "main" && *return_type != NEWTypes::Primitive(Types::Int) {
            Err(Error::new(
                name_token,
                &format!(
                    "Expected 'main' return type 'int', found: '{}'",
                    *return_type
                ),
            ))
        } else {
            Ok(())
        }
    }
    fn implicit_return_main(&mut self, name_token: &Token, body: &mut Vec<Stmt>) {
        if name_token.unwrap_string() == "main" && !self.returns_all_paths {
            self.returns_all_paths = true;

            body.push(Stmt::Return(
                name_token.clone(),
                Some(Expr::new(ExprKind::Number(0), ValueKind::Rvalue)),
            ));
        }
    }
    fn return_statement(&mut self, keyword: &Token, expr: &mut Option<Expr>) -> Result<(), Error> {
        self.returns_all_paths = true;

        let Some(ScopeKind::Function(_,function_type)) = find_scope!(&mut self.scope, ScopeKind::Function(..)) else {
            unreachable!("parser ensures that statements can only be contained in functions");
        };
        let function_type = function_type.clone();

        if let Some(expr) = expr {
            let mut body_return = self.expr_type(expr)?;

            crate::arr_decay!(body_return, expr, keyword, false);
            self.check_return_compatibility(keyword, &function_type, &body_return)?;
            self.maybe_cast(&function_type, &body_return, expr);
        } else {
            self.check_return_compatibility(
                keyword,
                &function_type,
                &NEWTypes::Primitive(Types::Void),
            )?;
        }
        Ok(())
    }

    pub fn expr_type(&mut self, ast: &mut Expr) -> Result<NEWTypes, Error> {
        ast.type_decl = Some(match &mut ast.kind {
            ExprKind::Binary { left, token, right } => {
                match self.evaluate_binary(left, token, right)? {
                    (result_type, None) => result_type,
                    // if pointer 'op' primitive, scale primitive before operation
                    (result_type, Some(scale_size)) => {
                        ast.kind = ExprKind::ScaleDown {
                            shift_amount: log_2(scale_size as i32),
                            expr: Box::new(ast.clone()),
                        };
                        result_type
                    }
                }
            }
            ExprKind::Unary {
                token,
                right,
                is_global,
            } => {
                *is_global = self.is_global();

                self.evaluate_unary(token, right, *is_global)?
            }
            ExprKind::Grouping { expr } => self.evaluate_grouping(expr)?,
            ExprKind::Number(n) => {
                if i32::try_from(*n).is_ok() {
                    NEWTypes::Primitive(Types::Int)
                } else {
                    NEWTypes::Primitive(Types::Long)
                }
            }
            ExprKind::CharLit(_) => NEWTypes::Primitive(Types::Char),
            ExprKind::String(token) => self.string(token.unwrap_string())?,
            ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(left, token, right)?
            }
            ExprKind::Ident(token) => self.ident(token)?,
            ExprKind::Assign {
                l_expr,
                token,
                r_expr,
            } => {
                let l_type = self.expr_type(l_expr)?;
                let r_type = self.expr_type(r_expr)?;

                self.assign_var(l_expr, l_type, token, r_expr, r_type)?
            }
            ExprKind::CompoundAssign {
                l_expr,
                token,
                r_expr,
            } => self.compound_assign(l_expr, token, r_expr)?,
            ExprKind::Call {
                left_paren,
                callee,
                args,
            } => self.evaluate_call(left_paren, callee, args)?,
            ExprKind::PostUnary {
                left,
                token,
                by_amount,
            } => self.evaluate_postunary(token, left, by_amount)?,
            ExprKind::MemberAccess {
                token,
                expr,
                member,
            } => self.member_access(token, member, expr)?,
            ExprKind::Cast {
                token,
                new_type,
                expr,
                direction,
            } => self.explicit_cast(token, expr, new_type, direction)?,
            ExprKind::Ternary {
                token,
                cond,
                true_expr,
                false_expr,
            } => self.ternary(token, cond, true_expr, false_expr)?,
            ExprKind::ScaleUp { .. } => unreachable!("is only used in codegen"),
            ExprKind::ScaleDown { .. } => unreachable!("is only used in codegen"),
            ExprKind::Nop { .. } => unreachable!("only used in parser"),
        });
        Ok(ast.type_decl.clone().unwrap())
    }
    fn ternary(
        &mut self,
        token: &Token,
        cond: &mut Expr,
        true_expr: &mut Expr,
        false_expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let cond_type = self.expr_type(cond)?;
        if !cond_type.is_scalar() {
            return Err(Error::new(
                token,
                &format!("Conditional expected scalar type found '{}'", cond_type),
            ));
        }
        let mut true_type = self.expr_type(true_expr)?;
        let mut false_type = self.expr_type(false_expr)?;

        if !true_type.type_compatible(&false_type) {
            return Err(Error::new(
                token,
                &format!(
                    "Mismatched operand types in ternary-expression. '{}' and '{}'",
                    true_type, false_type
                ),
            ));
        }

        self.maybe_int_promote(true_expr, &mut true_type);
        self.maybe_int_promote(false_expr, &mut false_type);

        match true_type.size().cmp(&false_type.size()) {
            Ordering::Greater => {
                cast!(false_expr, true_type.clone(), CastDirection::Up);
                Ok(true_type)
            }
            Ordering::Less => {
                cast!(true_expr, false_type.clone(), CastDirection::Up);
                Ok(false_type)
            }
            Ordering::Equal => Ok(true_type),
        }
    }
    fn ident(&mut self, token: &Token) -> Result<NEWTypes, Error> {
        match self.env.get(token.token.get_index()).unwrap() {
            Symbols::Variable(v) => Ok(v.get_type()),
            Symbols::TypeDef(..) | Symbols::Func(..) => Err(Error::new(
                token,
                &format!(
                    "Symbol '{}' doesn't exist as variable",
                    token.unwrap_string()
                ),
            )),
        }
    }
    fn member_access(
        &mut self,
        token: &Token,
        member: &Token,
        expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let expr_type = self.expr_type(expr)?;

        match expr_type.clone() {
            NEWTypes::Struct(s) | NEWTypes::Union(s) => {
                let member = member.unwrap_string();

                if let Some((member_type, _)) = s
                    .members()
                    .iter()
                    .find(|(_, name)| name.unwrap_string() == member)
                {
                    Ok(member_type.clone())
                } else {
                    Err(Error::new(
                        token,
                        &format!("No member '{}' in '{}'", member, expr_type),
                    ))
                }
            }
            _ => Err(Error::new(
                token,
                &format!("Can only access members of structs, not '{}'", expr_type),
            )),
        }
    }
    fn evaluate_postunary(
        &mut self,
        token: &Token,
        expr: &mut Expr,
        by_amount: &mut usize,
    ) -> Result<NEWTypes, Error> {
        let operand = self.expr_type(expr)?;

        if matches!(operand, NEWTypes::Array { .. } | NEWTypes::Struct(..)) {
            return Err(Error::new(
                token,
                &format!("Can't increment value of type '{}'", operand),
            ));
        } else if expr.value_kind == ValueKind::Rvalue {
            return Err(Error::new(token, "Can't increment Rvalues"));
        }

        // scale depending on type-size
        if let NEWTypes::Pointer(inner) = &operand {
            *by_amount *= inner.size()
        }

        Ok(operand)
    }
    fn string(&mut self, data: String) -> Result<NEWTypes, Error> {
        let len = data.len() + 1; // extra byte for \0-Terminator
        self.const_labels
            .insert(data, create_label(&mut self.const_label_count));

        Ok(NEWTypes::Array {
            of: Box::new(NEWTypes::Primitive(Types::Char)),
            amount: len,
        })
    }
    fn compound_assign(
        &mut self,
        l_expr: &mut Expr,
        token: &Token,
        r_expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        // create temporary-expression so that l_expr isn't overwritten
        let mut tmp = l_expr.clone();

        let l_type = self.expr_type(l_expr)?;

        // convert compound token into valid binary token
        let bin_token = &Token {
            token: token.comp_to_binary(),
            line_string: token.line_string.clone(),
            line_index: token.line_index,
            column: token.column,
        };

        // can ignore scale-down because ptr -= ptr is a type-error
        let r_type = self.evaluate_binary(&mut tmp, bin_token, r_expr)?.0;

        // have to clone r_expr so that change from evaluate_binary isn't overwritten
        let type_decl = self.assign_var(l_expr, l_type, token, &mut r_expr.clone(), r_type)?;

        Ok(type_decl)
    }
    fn assign_var(
        &mut self,
        l_expr: &mut Expr,
        l_type: NEWTypes,
        token: &Token,
        r_expr: &mut Expr,
        mut r_type: NEWTypes,
    ) -> Result<NEWTypes, Error> {
        if matches!(l_type, NEWTypes::Array { .. }) {
            return Err(Error::new(
                token,
                &format!("Array {} is not assignable", l_type),
            ));
        }

        if l_expr.value_kind != ValueKind::Lvalue {
            return Err(Error::new(token, "Expect Lvalue left of assignment"));
        }

        crate::arr_decay!(r_type, r_expr, token, self.is_global());

        self.check_type_compatibility(token, &l_type, &r_type)?;
        self.maybe_cast(&l_type, &r_type, r_expr);

        Ok(l_type)
    }

    fn evaluate_call(
        &mut self,
        left_paren: &Token,
        callee: &mut Expr,
        args: &mut Vec<Expr>,
    ) -> Result<NEWTypes, Error> {
        let func_name = match &callee.kind {
            ExprKind::Ident(func_name) => func_name,
            _ => return Err(Error::new(left_paren, "Function-name has to be identifier")),
        };

        let mut arg_types: Vec<NEWTypes> = Vec::new();
        for expr in args.iter_mut() {
            let mut t = self.expr_type(expr)?;

            crate::arr_decay!(t, expr, left_paren, false);
            self.maybe_int_promote(expr, &mut t);
            arg_types.push(t);
        }

        match self.env.get(func_name.token.get_index()).unwrap() {
            Symbols::Variable(_) | Symbols::TypeDef(..) => Err(Error::new(
                left_paren,
                &format!(
                    "Symbol '{}' already exists but not as function",
                    func_name.unwrap_string()
                ),
            )),
            Symbols::Func(function) => {
                if function.arity() == args.len() {
                    self.args_and_params_match(
                        left_paren,
                        &function.clone().get_params(),
                        arg_types,
                    )?;
                    Ok(function.clone().get_return_type())
                } else {
                    Err(Error::new(
                        left_paren,
                        &format!(
                            "At '{}': expected {} argument(s) found {}",
                            func_name.unwrap_string(),
                            function.arity(),
                            args.len()
                        ),
                    ))
                }
            }
        }
    }
    fn args_and_params_match(
        &self,
        left_paren: &Token,
        params: &[(NEWTypes, Token)],
        args: Vec<NEWTypes>,
    ) -> Result<(), Error> {
        for (i, type_decl) in args.iter().enumerate() {
            self.check_type_compatibility(left_paren, &params[i].0, type_decl)?;
        }
        Ok(())
    }
    fn block(&mut self, body: &mut Vec<Stmt>) -> Result<(), Error> {
        self.check_statements(body)
    }

    fn is_valid_bin(token: &Token, left_type: &NEWTypes, right_type: &NEWTypes) -> bool {
        match (&left_type, &right_type) {
            (NEWTypes::Primitive(Types::Void), _) | (_, NEWTypes::Primitive(Types::Void)) => false,
            (NEWTypes::Pointer(_), NEWTypes::Pointer(_)) => {
                if left_type.type_compatible(right_type) {
                    token.token == TokenType::Minus
                        || token.token == TokenType::EqualEqual
                        || token.token == TokenType::BangEqual
                } else {
                    false
                }
            }
            (_, NEWTypes::Pointer(_)) => token.token == TokenType::Plus,
            (NEWTypes::Pointer(_), _) => {
                token.token == TokenType::Plus || token.token == TokenType::Minus
            }
            (NEWTypes::Struct(..), _)
            | (_, NEWTypes::Struct(..))
            | (NEWTypes::Union(..), _)
            | (_, NEWTypes::Union(..)) => false,
            _ => true,
        }
    }
    fn maybe_scale(left: &NEWTypes, right: &NEWTypes, left_expr: &mut Expr, right_expr: &mut Expr) {
        let (expr, amount) = match (left, right) {
            (t, NEWTypes::Pointer(inner)) if !t.is_ptr() && inner.size() > 1 => {
                (left_expr, inner.size())
            }
            (NEWTypes::Pointer(inner), t) if !t.is_ptr() && inner.size() > 1 => {
                (right_expr, inner.size())
            }
            _ => return,
        };

        expr.kind = ExprKind::ScaleUp {
            by: amount,
            expr: Box::new(expr.clone()),
        };
    }
    fn evaluate_logical(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let left_type = self.expr_type(left)?;
        let right_type = self.expr_type(right)?;

        Self::lval_to_rval(left);
        Self::lval_to_rval(right);

        if !left_type.is_scalar() || !right_type.is_scalar() {
            return Err(Error::new(
                token,
                &format!(
                    "invalid logical expression: '{}' {} '{}'. Both types need to be scalar",
                    left_type, token.token, right_type
                ),
            ));
        }

        Ok(NEWTypes::Primitive(Types::Int))
    }
    fn lval_to_rval(expr: &mut Expr) {
        expr.value_kind = ValueKind::Rvalue;
    }
    fn rval_to_lval(expr: &mut Expr) {
        expr.value_kind = ValueKind::Lvalue;
    }
    fn evaluate_binary(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<(NEWTypes, Option<usize>), Error> {
        let mut left_type = self.expr_type(left)?;
        let mut right_type = self.expr_type(right)?;

        Self::lval_to_rval(left);
        Self::lval_to_rval(right);

        crate::arr_decay!(left_type, left, token, false);
        crate::arr_decay!(right_type, right, token, false);

        // check valid operations
        if !Self::is_valid_bin(token, &left_type, &right_type) {
            return Err(Error::new(
                token,
                &format!(
                    "invalid binary expression: '{}' {} '{}'",
                    left_type, token.token, right_type
                ),
            ));
        }

        self.maybe_int_promote(left, &mut left_type);
        self.maybe_int_promote(right, &mut right_type);

        // scale index when pointer arithmetic
        Self::maybe_scale(&left_type, &right_type, left, right);

        // type promote to bigger type
        match left_type.size().cmp(&right_type.size()) {
            Ordering::Greater => {
                cast!(right, left_type.clone(), CastDirection::Up);
                Ok((left_type, None))
            }
            Ordering::Less => {
                cast!(left, right_type.clone(), CastDirection::Up);
                Ok((right_type, None))
            }
            Ordering::Equal => match (&left_type, &right_type) {
                (NEWTypes::Pointer(inner), NEWTypes::Pointer(_)) => {
                    Ok((NEWTypes::Primitive(Types::Long), Some(inner.size())))
                }
                _ => Ok((left_type, None)),
            },
        }
    }
    fn maybe_int_promote(&self, expr: &mut Expr, type_decl: &mut NEWTypes) {
        if !matches!(type_decl, NEWTypes::Primitive(_)) || type_decl.is_void() {
            return;
        }
        if type_decl.size() < NEWTypes::Primitive(Types::Int).size() {
            cast!(expr, NEWTypes::Primitive(Types::Int), CastDirection::Up);
            *type_decl = NEWTypes::Primitive(Types::Int);
        }
    }
    fn evaluate_unary(
        &mut self,
        token: &Token,
        right: &mut Expr,
        is_global: bool,
    ) -> Result<NEWTypes, Error> {
        let mut right_type = self.expr_type(right)?;

        if matches!(token.token, TokenType::Amp) {
            // array doesn't decay during '&' expression
            Ok(self.check_address(token, right_type, right)?)
        } else {
            crate::arr_decay!(right_type, right, token, is_global);
            Ok(match token.token {
                TokenType::Star => self.check_deref(token, right_type, right)?,
                TokenType::Bang => {
                    Self::lval_to_rval(right);
                    NEWTypes::Primitive(Types::Int)
                }
                TokenType::Minus | TokenType::Tilde => {
                    Self::lval_to_rval(right);
                    self.maybe_int_promote(right, &mut right_type);

                    if matches!(right_type, NEWTypes::Pointer(_)) {
                        return Err(Error::new(
                            token,
                            &format!(
                                "Invalid unary-expression '{}' with type '{}'",
                                token.token, right_type
                            ),
                        ));
                    }
                    NEWTypes::Primitive(Types::Int)
                }
                _ => unreachable!(), // ++a or --a are evaluated as compound assignment
            })
        }
    }
    fn check_address(
        &self,
        token: &Token,
        type_decl: NEWTypes,
        expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        if expr.value_kind == ValueKind::Lvalue {
            Self::lval_to_rval(expr);
            Ok(NEWTypes::Pointer(Box::new(type_decl)))
        } else {
            Err(Error::new(token, "can't call '&' on r-value"))
        }
    }
    fn check_deref(
        &self,
        token: &Token,
        type_decl: NEWTypes,
        expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        if let Some(inner) = type_decl.deref_at() {
            Self::rval_to_lval(expr);
            Ok(inner)
        } else {
            Err(Error::new(
                token,
                &format!(
                    "can't dereference value-type '{}', expected type 'pointer'",
                    type_decl,
                ),
            ))
        }
    }
    fn evaluate_grouping(&mut self, expr: &mut Expr) -> Result<NEWTypes, Error> {
        self.expr_type(expr)
    }
    fn check_return_compatibility(
        &mut self,
        keyword: &Token,
        function_type: &NEWTypes,
        body_return: &NEWTypes,
    ) -> Result<(), Error> {
        if matches!(function_type, NEWTypes::Array { .. }) {
            Err(Error::new(
                keyword,
                "Can't return stack-array from function",
            ))
        } else if !function_type.type_compatible(body_return) {
            Err(Error::new(
                keyword,
                &format!(
                    "Mismatched function return type: '{}', found: '{}'",
                    function_type, body_return
                ),
            ))
        } else {
            Ok(())
        }
    }
    fn is_global(&self) -> bool {
        self.scope.0.len() == 1
    }
}

pub fn align_by(mut offset: usize, type_size: usize) -> usize {
    let remainder = offset % type_size;
    if remainder != 0 {
        offset += type_size - remainder;
    }
    offset
}
pub fn create_label(index: &mut usize) -> usize {
    let prev = *index;
    *index += 1;
    prev
}

// returns true if expression is known at compile-time
fn is_constant(expr: &Expr) -> bool {
    // 6.6 Constant Expressions
    match &expr.kind {
        ExprKind::String(_)
        | ExprKind::Number(_)
        | ExprKind::CharLit(_)
        | ExprKind::Cast { .. } => true,
        // don't have to specify matching array-type because it decays into '&' anyway
        ExprKind::Unary { token, right, .. } if matches!(token.token, TokenType::Amp) => {
            matches!(&right.kind, ExprKind::Ident(_) | ExprKind::String(_))
        }
        _ => false,
    }
}

// helper function for calculating log2
const fn num_bits<T>() -> usize {
    std::mem::size_of::<T>() * 8
}

fn log_2(x: i32) -> usize {
    assert!(x > 0);
    (num_bits::<i32>() as u32 - x.leading_zeros() - 1) as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alignes_stack1() {
        let offset = 12;
        let result = align_by(offset, 8);

        assert_eq!(result, 16);
    }
    #[test]
    fn alignes_stack2() {
        let offset = 9;
        let result = align_by(offset, 4);

        assert_eq!(result, 12);
    }
    #[test]
    fn alignes_stackpointer1() {
        let offset = 31;
        let result = align_by(offset, 16);

        assert_eq!(result, 32);
    }
    #[test]
    fn alignes_stackpointer2() {
        let offset = 5;
        let result = align_by(offset, 16);

        assert_eq!(result, 16);
    }
    #[test]
    fn finds_nested_loop() {
        let mut scopes = ScopeLevel(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![], false),
            ScopeKind::Switch(vec![], false),
        ]);
        let expected = true;
        let actual = find_scope!(scopes, ScopeKind::Loop).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn doesnt_find_switch() {
        let mut scopes = ScopeLevel(vec![ScopeKind::Global, ScopeKind::Loop, ScopeKind::Loop]);
        let expected = false;
        let actual = find_scope!(scopes, ScopeKind::Switch(..)).is_some();

        assert_eq!(actual, expected);
    }
    #[test]
    fn finds_and_mutates_scope() {
        let mut scopes = ScopeLevel(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![], false),
            ScopeKind::Switch(vec![], false),
            ScopeKind::Loop,
        ]);
        let expected = ScopeLevel(vec![
            ScopeKind::Global,
            ScopeKind::Loop,
            ScopeKind::Switch(vec![], false),
            ScopeKind::Switch(vec![1, 3], true),
            ScopeKind::Loop,
        ]);
        let ScopeKind::Switch(cases, defaults) =
            find_scope!(scopes, ScopeKind::Switch(..)).unwrap() else {unreachable!()};
        cases.push(1);
        cases.push(3);
        *defaults = true;

        let cases = cases.clone();
        let defaults = defaults.clone();

        assert_eq!(scopes, expected);
        assert_eq!(cases, vec![1, 3]);
        assert_eq!(defaults, true);
    }
}
