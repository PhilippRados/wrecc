use crate::codegen::codegen::align_by;
use crate::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(PartialEq)]
enum Scope {
    Global,
    Block,
    Function(String, NEWTypes), // function name and return type
}
pub struct TypeChecker {
    errors: Vec<Error>,
    scope: Vec<Scope>,
    env: Environment<NEWTypes>,
    global_env: Environment<NEWTypes>,
    returns_all_paths: bool,
    builtins: Vec<(&'static str, Function)>,
    func_stack_size: HashMap<String, usize>, // typechecker passes info about how many stack allocation there are in a function
    found_main: bool,
}
macro_rules! cast {
    ($ex:expr,$new_type:expr,$kind:ident) => {
        *$ex = Expr {
            kind: ExprKind::$kind {
                expr: Box::new($ex.clone()),
            },
            type_decl: Some($new_type),
            value_kind: $ex.value_kind.clone(),
        }
    };
}
impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            errors: vec![],
            env: Environment::new(None),
            global_env: Environment::new(None),
            scope: vec![Scope::Global],
            returns_all_paths: false,
            found_main: false,
            func_stack_size: HashMap::new(),
            builtins: vec![(
                "printint",
                Function::new(
                    NEWTypes::Primitive(Types::Void),
                    vec![(
                        NEWTypes::Primitive(Types::Char),
                        Token::new(TokenType::Ident("".to_string()), -1, -1, "".to_string()),
                    )],
                ),
            )],
        }
    }
    pub fn check(
        &mut self,
        statements: &mut Vec<Stmt>,
    ) -> Result<HashMap<String, usize>, Vec<Error>> {
        // initialze builtins so typechecker doesnt throw error when it doesnt find them in the program
        for (name, f) in self.builtins.iter().by_ref() {
            self.global_env
                .current
                .func_decl
                .insert(name.to_string(), f.clone());
        }
        if let Err(e) = self.check_statements(statements) {
            self.errors.push(e);
            // synchronize
        }
        if !self.errors.is_empty() {
            Err(self.errors.clone())
        } else if !self.found_main {
            Err(vec![Error::missing_entrypoint()])
        } else {
            Ok(self.func_stack_size.clone())
        }
    }
    fn check_statements(&mut self, statements: &mut Vec<Stmt>) -> Result<(), Error> {
        for s in statements {
            self.visit(s)?
        }
        Ok(())
    }
    fn check_global(&self, statement: &Stmt) -> Result<(), Error> {
        if !matches!(statement, Stmt::Function(_, _, _, _))
            && !matches!(statement, Stmt::FunctionDeclaration(_, _, _))
            && find_function(&self.scope) == None
        {
            return Err(Error::new(
                statement.get_token(),
                &format!("can't have {} in global scope", statement),
            ));
        }
        Ok(())
    }
    fn visit(&mut self, statement: &mut Stmt) -> Result<(), Error> {
        self.check_global(statement)?;

        match statement {
            Stmt::DeclareVar(type_decl, var_name) => self.declare_var(type_decl, var_name),
            Stmt::InitVar(type_decl, name, ref mut expr) => {
                self.init_var(type_decl.clone(), name, expr)
            }
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(return_type, name, params.clone(), body)
            }
            Stmt::FunctionDeclaration(return_type, name, params) => {
                self.function_declaration(return_type, name, params)
            }
            Stmt::Return(keyword, ref mut value) => self.return_statement(keyword, value),
            Stmt::Expr(ref mut expr) => match self.expr_type(expr) {
                Ok(_) => Ok(()),
                Err(e) => Err(e),
            },
            Stmt::Block(left_paren, statements) => {
                self.scope.push(Scope::Block);
                self.block(
                    left_paren,
                    statements,
                    Environment::new(Some(Box::new(self.env.clone()))),
                )
            }
            Stmt::If(keyword, ref mut cond, then_branch, else_branch) => {
                self.if_statement(keyword, cond, then_branch, else_branch)
            }
            Stmt::While(left_paren, ref mut cond, body) => {
                self.while_statement(left_paren, cond, body)
            }
        }
    }
    fn while_statement(
        &mut self,
        left_paren: &Token,
        cond: &mut Expr,
        body: &mut Stmt,
    ) -> Result<(), Error> {
        if self.expr_type(cond)?.is_void() {
            return Err(Error::new(
                left_paren,
                "conditional expected scalar type found ‘void'",
            ));
        }
        self.visit(body)?;
        self.returns_all_paths = false;
        Ok(())
    }
    fn declare_var(&mut self, type_decl: &NEWTypes, var_name: &Token) -> Result<(), Error> {
        let name = var_name.unwrap_string();

        if self.env.current.vars.contains_key(&name) {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", var_name.unwrap_string()),
            ));
        }
        if *type_decl == NEWTypes::Primitive(Types::Void) {
            return Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", var_name.unwrap_string()),
            ));
        }
        self.increment_stack_size(var_name, type_decl.size())?;
        self.env.declare_var(name, type_decl.clone());
        Ok(())
    }
    fn check_type_compatibility(
        &self,
        token: &Token,
        left: &NEWTypes,
        right: &NEWTypes,
    ) -> Result<(), Error> {
        if left.is_void() || right.is_void() {
            Err(Error::new(
                token,
                &format!("Can't assign to type '{}' with type '{}'", left, right),
            ))
        } else if !left.type_compatible(right) {
            Err(Error::new(
                token,
                &format!("Can't assign to type '{}' with type '{}'", left, right),
            ))
        } else {
            Ok(())
        }
    }
    fn init_var(
        &mut self,
        type_decl: NEWTypes,
        var_name: &Token,
        expr: &mut Expr,
    ) -> Result<(), Error> {
        let name = var_name.unwrap_string();
        let value_type = self.expr_type(expr)?;

        if self.env.current.vars.contains_key(&name) {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", name),
            ));
        }
        self.check_type_compatibility(var_name, &type_decl, &value_type)?;
        self.maybe_cast(&type_decl, &value_type, expr);

        self.increment_stack_size(var_name, type_decl.size())?;
        // currently only type-checks for void since int and char are interchangeable
        self.env.init_var(name, type_decl);
        Ok(())
    }
    fn maybe_cast(&self, type_decl: &NEWTypes, other_type: &NEWTypes, expr: &mut Expr) {
        match other_type.size().cmp(&type_decl.size()) {
            Ordering::Less => cast!(expr, type_decl.clone(), CastUp),
            Ordering::Greater => cast!(expr, type_decl.clone(), CastDown),
            Ordering::Equal => (),
        }
    }
    fn increment_stack_size(&mut self, var_name: &Token, type_size: usize) -> Result<(), Error> {
        match find_function(&self.scope) {
            Some(Scope::Function(name, _)) => {
                *self.func_stack_size.get_mut(name).unwrap() += type_size;
                *self.func_stack_size.get_mut(name).unwrap() =
                    align_by(self.func_stack_size[name], type_size);
                Ok(())
            }
            _ => Err(Error::new(
                var_name,
                "cant declare stack variables in global scope",
            )),
        }
    }
    fn if_statement(
        &mut self,
        keyword: &Token,
        cond: &mut Expr,
        then_branch: &mut Stmt,
        else_branch: &mut Option<Stmt>,
    ) -> Result<(), Error> {
        let cond = self.expr_type(cond)?;
        if cond.is_void() {
            return Err(Error::new(
                keyword,
                "expected Expression inside of condition, found 'void'",
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
    fn function_declaration(
        &mut self,
        return_type: &NEWTypes,
        name_token: &Token,
        params: &Vec<(NEWTypes, Token)>,
    ) -> Result<(), Error> {
        let name = &name_token.unwrap_string();
        if let Some(f) = self.global_env.get_func(name, FunctionKind::Declaration) {
            self.cmp_decl(name_token, f, return_type, params)?;
        }
        if let Some(f) = self.global_env.get_func(name, FunctionKind::DefDeclaration) {
            self.cmp_decl(name_token, f, return_type, params)?;
        }
        self.global_env.declare_func(
            return_type.clone(),
            name,
            params.clone(),
            FunctionKind::Declaration,
        );
        Ok(())
    }
    fn function_definition(
        &mut self,
        return_type: &NEWTypes,
        name_token: &Token,
        params: Vec<(NEWTypes, Token)>,
        body: &mut Vec<Stmt>,
    ) -> Result<(), Error> {
        if *self.scope.last().unwrap() != Scope::Global {
            return Err(Error::new(
                name_token,
                "can only define functions in global scope",
            ));
        }
        let name = name_token.unwrap_string();
        if name == "main" {
            self.found_main = true;
        }
        if self
            .global_env
            .get_func(&name, FunctionKind::DefDeclaration)
            .is_some()
        {
            return Err(Error::new(
                name_token,
                &format!("Redefinition of function '{}'", name),
            ));
        } else if let Some(f) = self.global_env.get_func(&name, FunctionKind::Declaration) {
            // compare function_definition with declaration and see if they match
            self.cmp_decl(name_token, f, return_type, &params)?;
        } else {
            self.global_env.declare_func(
                return_type.clone(),
                &name,
                params.clone(),
                FunctionKind::DefDeclaration,
            );
        }

        // have to push scope before declaring local variables
        self.scope
            .push(Scope::Function(name.clone(), return_type.clone()));
        let mut env = Environment::new(Some(Box::new(self.env.clone()))); // create new scope for function body

        // initialize stack size for current function-scope
        self.func_stack_size.insert(name.clone(), 0);
        for (type_decl, name) in params.iter().by_ref() {
            self.increment_stack_size(name, type_decl.size())?; // add params to stack-size
            env.init_var(name.unwrap_string(), type_decl.clone()) // initialize params in local scope
        }

        // check function body
        self.block(name_token, body, env)?;

        self.main_returns_int(name_token, return_type)?;
        self.implicit_return_main(name_token, body);

        if !return_type.is_void() && !self.returns_all_paths {
            Err(Error::new(
                name_token,
                "non-void function doesnt return in all code paths",
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
                    "expected 'main()' return type 'int', found: '{}'",
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
    fn cmp_decl(
        &self,
        name_token: &Token,
        declaration: &Function,
        return_type: &NEWTypes,
        params: &Vec<(NEWTypes, Token)>,
    ) -> Result<(), Error> {
        if declaration.return_type != *return_type {
            Err(Error::new(
                name_token,
                &format!(
                    "Conflicting return-types in function-declarations: expected {}, found {}",
                    declaration.return_type, return_type
                ),
            ))
        } else if declaration.arity() != params.len() {
            Err(Error::new(name_token,&format!("Mismatched number of parameters in function-declarations: expected {}, found {}",declaration.arity(),params.len())))
        } else {
            for (i, (types, token)) in params.iter().enumerate() {
                if *types != declaration.params[i].0 {
                    return Err(Error::new(token,&format!("Mismatched parameter-types in function-declarations: expected '{}', found '{}'",declaration.params[i].0,types)));
                }
            }
            Ok(())
        }
    }
    fn get_function_type(&self, token: &Token) -> Result<&NEWTypes, Error> {
        if let Some(Scope::Function(_, function_type)) = find_function(&self.scope) {
            Ok(function_type)
        } else {
            Err(Error::new(
                token,
                "can only define return statements inside a function",
            ))
        }
    }
    fn return_statement(&mut self, keyword: &Token, expr: &mut Option<Expr>) -> Result<(), Error> {
        self.returns_all_paths = true;
        let function_type = self.get_function_type(keyword)?.clone();

        if let Some(expr) = expr {
            let body_return = self.expr_type(expr)?;

            self.check_return_compatibility(keyword, &function_type, &body_return)?;
            self.maybe_cast(&body_return, &function_type, expr);
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
                    (result_type, Some(scale_size)) => {
                        ast.kind = ExprKind::ScaleDown {
                            shift_amount: log_2(scale_size as i32),
                            expr: Box::new(ast.clone()),
                        };
                        result_type
                    }
                }
            }
            ExprKind::Unary { token, right } => self.evaluate_unary(token, right)?,
            ExprKind::Grouping { expr } => self.evaluate_grouping(expr)?,
            ExprKind::Number(_) => NEWTypes::Primitive(Types::Int),
            ExprKind::CharLit(_) => NEWTypes::Primitive(Types::Char),
            ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(left, token, right)?
            }
            ExprKind::Ident(v) => self.env.get_var(v)?,
            ExprKind::Assign {
                l_expr: store_expr,
                token,
                r_expr: expr,
            } => self.assign_var(store_expr, token, expr)?,
            ExprKind::Call {
                left_paren,
                callee,
                args,
            } => self.evaluate_call(left_paren, callee, args)?,
            ExprKind::CastUp { .. } => unimplemented!("explicit casts"),
            ExprKind::CastDown { .. } => unimplemented!("explicit casts"),
            ExprKind::ScaleUp { .. } => unreachable!("is only used in codegen"),
            ExprKind::ScaleDown { .. } => unreachable!("is only used in codegen"),
        });
        Ok(ast.type_decl.clone().unwrap())
    }
    fn assign_var(
        &mut self,
        store_expr: &mut Expr,
        token: &Token,
        expr: &mut Expr,
    ) -> Result<NEWTypes, Error> {
        let type_decl = self.expr_type(store_expr)?;
        let value = self.expr_type(expr)?;

        if matches!(type_decl, NEWTypes::Array { .. }) {
            return Err(Error::new(
                token,
                &format!("array {} is not assignable", type_decl),
            ));
        }
        self.check_type_compatibility(token, &type_decl, &value)?;
        self.maybe_cast(&type_decl, &value, expr);

        Ok(type_decl)
    }

    fn evaluate_call(
        &mut self,
        left_paren: &Token,
        callee: &mut Expr,
        args: &mut Vec<Expr>,
    ) -> Result<NEWTypes, Error> {
        let func_name = match &callee.kind {
            ExprKind::Ident(func_name) => func_name,
            _ => return Err(Error::new(left_paren, "function-name has to be identifier")),
        };

        let mut arg_types = args
            .iter_mut()
            .map(|expr| self.expr_type(expr))
            .collect::<Result<Vec<NEWTypes>, Error>>()?;

        match (
            self.global_env
                .current
                .func_def_decl
                .get(&func_name.unwrap_string()),
            self.global_env
                .current
                .func_decl
                .get(&func_name.unwrap_string()),
        ) {
            (None, None) => Err(Error::new(
                left_paren,
                &format!("no function {} exists", func_name.unwrap_string()),
            )),
            (Some(function), None) | (None, Some(function)) | (Some(function), Some(_)) => {
                if function.arity() == args.len() {
                    self.args_and_params_match(left_paren, &function.params, args, &mut arg_types)?;
                    Ok(function.return_type.clone())
                } else {
                    Err(Error::new(
                        left_paren,
                        &format!(
                            "at '{}': expected {} argument(s) found {}",
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
        expressions: &mut [Expr],
        args: &mut Vec<NEWTypes>,
    ) -> Result<(), Error> {
        for (i, type_decl) in args.iter_mut().enumerate() {
            self.check_type_compatibility(left_paren, type_decl, &params[i].0)?;
            self.maybe_int_promote(&mut expressions[i], type_decl);
        }
        Ok(())
    }
    fn block(
        &mut self,
        token: &Token,
        body: &mut Vec<Stmt>,
        env: Environment<NEWTypes>,
    ) -> Result<(), Error> {
        if find_function(&self.scope) == None {
            return Err(Error::new(token, "can't declare block in global scope"));
        }
        self.env = env;
        let result = self.check_statements(body);

        self.env = *self.env.enclosing.as_ref().unwrap().clone();
        self.scope.pop();

        result
    }
    fn is_valid_bin(token: &Token, left_type: &NEWTypes, right_type: &NEWTypes) -> bool {
        match (&left_type, &right_type) {
            (NEWTypes::Primitive(Types::Void), _) | (_, NEWTypes::Primitive(Types::Void)) => false,
            (NEWTypes::Pointer(_), NEWTypes::Pointer(_))
            | (NEWTypes::Array { .. }, NEWTypes::Array { .. })
                if left_type.type_compatible(right_type) =>
            {
                token.token == TokenType::Minus
                    || token.token == TokenType::EqualEqual
                    || token.token == TokenType::BangEqual
            }
            (_, NEWTypes::Pointer(_)) | (_, NEWTypes::Array { .. }) => {
                token.token == TokenType::Plus
            }
            (NEWTypes::Pointer(_), _) | (NEWTypes::Array { .. }, _) => {
                token.token == TokenType::Plus || token.token == TokenType::Minus
            }
            _ => true,
        }
    }
    fn maybe_scale(left: &NEWTypes, right: &NEWTypes, left_expr: &mut Expr, right_expr: &mut Expr) {
        let (expr, amount) = match (left, right) {
            (
                t,
                NEWTypes::Pointer(inner)
                | NEWTypes::Array {
                    element_type: inner,
                    ..
                },
            ) if !t.is_ptr() && inner.size() > 1 => (left_expr, inner.size()),
            (
                NEWTypes::Pointer(inner)
                | NEWTypes::Array {
                    element_type: inner,
                    ..
                },
                t,
            ) if !t.is_ptr() && inner.size() > 1 => (right_expr, inner.size()),
            _ => return,
        };

        expr.kind = ExprKind::ScaleUp {
            shift_amount: log_2(amount as i32),
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

        if left_type.is_void() || right_type.is_void() {
            return Err(Error::new(
                token,
                &format!(
                    "invalid logical expression: '{}' {} '{}'",
                    left_type, token.token, right_type
                ),
            ));
        }

        Ok(NEWTypes::Primitive(Types::Int))
    }
    fn evaluate_binary(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<(NEWTypes, Option<usize>), Error> {
        let mut left_type = self.expr_type(left)?;
        let mut right_type = self.expr_type(right)?;

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
                cast!(right, left_type.clone(), CastUp);
                Ok((left_type, None))
            }
            Ordering::Less => {
                cast!(left, right_type.clone(), CastUp);
                Ok((right_type, None))
            }
            Ordering::Equal => match (&left_type, &right_type) {
                (NEWTypes::Pointer(inner), NEWTypes::Pointer(_)) => {
                    Ok((NEWTypes::Primitive(Types::Long), Some(inner.size())))
                }
                (
                    NEWTypes::Array {
                        element_type: inner,
                        ..
                    },
                    NEWTypes::Array { .. },
                ) => Ok((NEWTypes::Primitive(Types::Long), Some(inner.size()))),
                _ => Ok((left_type, None)),
            },
        }
    }
    fn maybe_int_promote(&self, expr: &mut Expr, type_decl: &mut NEWTypes) {
        if !matches!(type_decl, NEWTypes::Primitive(_)) {
            return;
        }
        if type_decl.size() < NEWTypes::Primitive(Types::Int).size() {
            cast!(expr, NEWTypes::Primitive(Types::Int), CastUp);
            *type_decl = NEWTypes::Primitive(Types::Int);
        }
    }
    fn evaluate_unary(&mut self, token: &Token, right: &mut Expr) -> Result<NEWTypes, Error> {
        let right_type = self.expr_type(right)?;

        Ok(match token.token {
            TokenType::Amp => self.check_address(token, right_type, right)?,
            TokenType::Star => self.check_deref(token, right_type)?,
            TokenType::Bang => NEWTypes::Primitive(Types::Int),
            TokenType::Minus => {
                if matches!(right_type, NEWTypes::Pointer(_))
                    || matches!(right_type, NEWTypes::Array { .. })
                {
                    return Err(Error::new(
                        token,
                        &format!("Invalid unary-expression '-' with type '{}'", right_type),
                    ));
                }
                right_type
            }
            _ => unreachable!(),
        })
    }
    fn check_address(
        &self,
        token: &Token,
        type_decl: NEWTypes,
        expr: &Expr,
    ) -> Result<NEWTypes, Error> {
        if expr.value_kind == ValueKind::Lvalue {
            Ok(NEWTypes::Pointer(Box::new(type_decl)))
        } else {
            Err(Error::new(token, "can't call '&' on r-value"))
        }
    }
    fn check_deref(&self, token: &Token, type_decl: NEWTypes) -> Result<NEWTypes, Error> {
        if let Some(inner) = type_decl.deref_at() {
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
                &format!("Can't return stack-array from function"),
            ))
        } else if !function_type.type_compatible(&body_return) {
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
}
fn find_function(scopes: &[Scope]) -> Option<&Scope> {
    for ref scope in scopes.iter().rev() {
        if matches!(scope, Scope::Function(_, _)) {
            return Some(scope);
        }
    }
    None
}
// helper function for calculating log2
const fn num_bits<T>() -> usize {
    std::mem::size_of::<T>() * 8
}

fn log_2(x: i32) -> usize {
    assert!(x > 0);
    (num_bits::<i32>() as u32 - x.leading_zeros() - 1) as usize
}
