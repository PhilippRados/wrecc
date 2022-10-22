use crate::common::{environment::*, error::*, expr::*, stmt::*, token::*, types::*};
use std::collections::HashMap;

#[derive(PartialEq)]
enum Scope {
    Global,
    Block,
    Function(String, Types), // function name and return type
}
pub struct TypeChecker {
    errors: Vec<Error>,
    scope: Vec<Scope>,
    env: Environment<Types>,
    global_env: Environment<Types>,
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
                    Types::Void,
                    vec![(
                        Types::Char,
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
                .funcs
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
    fn visit(&mut self, statement: &mut Stmt) -> Result<(), Error> {
        if !matches!(statement, Stmt::Function(_, _, _, _)) && self.find_function() == None {
            return Err(Error::new(
                statement.get_token(),
                &format!("can't have {} in global scope", statement),
            ));
        }
        match statement {
            Stmt::DeclareVar(type_decl, var_name) => self.declare_var(type_decl, var_name),
            Stmt::InitVar(type_decl, name, ref mut expr) => self.init_var(type_decl, name, expr),
            Stmt::Function(return_type, name, params, body) => {
                self.function_definition(*return_type, name, params.clone(), body)
            }
            Stmt::Return(keyword, ref mut value) => self.return_statement(keyword, value),
            Stmt::Print(token, ref mut expr) => self.print_statement(token, expr),
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
        if self.expr_type(cond)? == Types::Void {
            return Err(Error::new(
                left_paren,
                "conditional expected scalar type found ‘void'",
            ));
        }
        self.visit(body)?;
        self.returns_all_paths = false;
        Ok(())
    }
    fn declare_var(&mut self, type_decl: &Types, var_name: &Token) -> Result<(), Error> {
        let name = var_name.unwrap_string();

        if self.env.current.vars.contains_key(&name) {
            return Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", var_name.unwrap_string()),
            ));
        }
        if *type_decl == Types::Void {
            return Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", var_name.unwrap_string()),
            ));
        }
        self.increment_stack_size(var_name, type_decl)?;
        self.env.declare_var(name, *type_decl);
        Ok(())
    }
    fn init_var(
        &mut self,
        type_decl: &Types,
        var_name: &Token,
        expr: &mut Expr,
    ) -> Result<(), Error> {
        let name = var_name.unwrap_string();
        let value = self.expr_type(expr)?;

        if self.env.current.vars.contains_key(&name) {
            Err(Error::new(
                var_name,
                &format!("Redefinition of variable '{}'", name),
            ))
        } else if *type_decl == Types::Void {
            Err(Error::new(
                var_name,
                &format!("Can't assign to 'void' {}", name),
            ))
        } else if value == Types::Void {
            Err(Error::new(
                var_name,
                &format!(
                    "'void' cant be assigned to variable {} of type {}",
                    name, type_decl
                ),
            ))
        } else {
            if value < *type_decl {
                cast!(expr, *type_decl, CastUp);
            } else if value > *type_decl {
                cast!(expr, *type_decl, CastDown);
            }
            self.increment_stack_size(var_name, type_decl)?;
            // currently only type-checks for void since int and char are interchangeable
            self.env.init_var(name, *type_decl);
            Ok(())
        }
    }
    fn increment_stack_size(&mut self, var_name: &Token, type_decl: &Types) -> Result<(), Error> {
        match self.find_function() {
            Some(Scope::Function(name, _)) => {
                *self.func_stack_size.entry(name.to_owned()).or_default() += type_decl.size();
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
        if cond == Types::Void {
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
    fn print_statement(&mut self, token: &Token, expr: &mut Expr) -> Result<(), Error> {
        let t = self.expr_type(expr)?;
        if t == Types::Void {
            Err(Error::new(token, "can't print 'void' expression"))
        } else {
            Ok(())
        }
    }
    fn function_definition(
        &mut self,
        return_type: Types,
        name: &Token,
        params: Vec<(Types, Token)>,
        body: &mut Vec<Stmt>,
    ) -> Result<(), Error> {
        if *self.scope.last().unwrap() != Scope::Global {
            return Err(Error::new(
                name,
                "can only define functions in global scope",
            ));
        }
        if name.unwrap_string() == "main" {
            self.found_main = true;
        }

        self.global_env
            .declare_func(return_type, &name.unwrap_string(), params.clone());

        // have to push scope before declaring local variables
        self.scope
            .push(Scope::Function(name.unwrap_string(), return_type));
        let mut env = Environment::new(Some(Box::new(self.env.clone()))); // create new scope for function body

        // initialize stack size for current function-scope
        self.func_stack_size.insert(name.unwrap_string(), 0);
        for (type_decl, name) in params.iter() {
            self.increment_stack_size(name, type_decl)?; // add params to stack-size
            env.init_var(name.unwrap_string(), *type_decl) // initialize params in local scope
        }

        // check function body
        self.block(name, body, env)?;

        if return_type != Types::Void && !self.returns_all_paths {
            Err(Error::new(
                name,
                "non-void function doesnt return in all code paths",
            ))
        } else {
            self.returns_all_paths = false;
            Ok(())
        }
    }
    fn return_statement(&mut self, keyword: &Token, expr: &mut Option<Expr>) -> Result<(), Error> {
        self.returns_all_paths = true;
        if let Some(expr) = expr {
            let type_decl = self.expr_type(expr)?;
            self.check_return(keyword, type_decl)
        } else {
            self.check_return(keyword, Types::Void)
        }
    }

    pub fn expr_type(&mut self, ast: &mut Expr) -> Result<Types, Error> {
        ast.type_decl = Some(match &mut ast.kind {
            ExprKind::Binary { left, token, right } => self.evaluate_binary(left, token, right)?,
            ExprKind::Unary { token: _, right } => self.evaluate_unary(right)?,
            ExprKind::Grouping { expr } => self.evaluate_grouping(expr)?,
            ExprKind::Number(_) => Types::Int,
            ExprKind::CharLit(_) => Types::Char,
            ExprKind::Logical { left, token, right } => {
                self.evaluate_logical(left, token, right)?
            }
            ExprKind::Ident(v) => self.env.get_var(v)?,
            ExprKind::Assign { name, expr } => {
                let value = self.expr_type(expr)?;
                self.env.assign_var(name, value)?
            }
            ExprKind::Call {
                left_paren,
                callee,
                args,
            } => self.evaluate_call(left_paren, callee, args)?,
            ExprKind::CastUp { expr: _ } => unimplemented!("explicit casts"),
            ExprKind::CastDown { expr: _ } => unimplemented!("explicit casts"),
        });
        Ok(ast.type_decl.unwrap())
    }

    fn evaluate_call(
        &mut self,
        left_paren: &Token,
        callee: &mut Expr,
        args: &mut Vec<Expr>,
    ) -> Result<Types, Error> {
        let func_name = match &callee.kind {
            ExprKind::Ident(func_name) => func_name,
            _ => return Err(Error::new(left_paren, "function-name has to be identifier")),
        };

        let arg_types = args
            .iter_mut()
            .map(|expr| self.expr_type(expr))
            .collect::<Result<Vec<Types>, Error>>()?;

        match self
            .global_env
            .current
            .funcs
            .get(&func_name.unwrap_string())
        {
            Some(function) => {
                if function.arity() == args.len() {
                    self.args_and_params_match(left_paren, &function.params, args, arg_types)?;
                    Ok(function.return_type)
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
            None => Err(Error::new(
                left_paren,
                &format!("no function {} exists", func_name.unwrap_string()),
            )),
        }
    }
    fn args_and_params_match(
        &self,
        left_paren: &Token,
        params: &Vec<(Types, Token)>,
        expressions: &mut Vec<Expr>,
        args: Vec<Types>,
    ) -> Result<(), Error> {
        // TODO: actually compare args not only testing for void
        for (i, type_decl) in args.iter().enumerate() {
            // let type_decl = self.expr_type(expr)?;
            if *type_decl == Types::Void {
                return Err(Error::new(
                    left_paren,
                    &format!(
                        "expected argument to be of type {} found {}",
                        params[i].0, type_decl
                    ),
                ));
            }
            self.maybe_int_promote(&mut expressions[i]);
        }
        Ok(())
    }
    fn block(
        &mut self,
        token: &Token,
        body: &mut Vec<Stmt>,
        env: Environment<Types>,
    ) -> Result<(), Error> {
        if self.find_function() == None {
            return Err(Error::new(token, "can't declare block in global scope"));
        }
        self.env = env;
        let result = self.check_statements(body);

        self.env = *self.env.enclosing.as_ref().unwrap().clone();
        self.scope.pop();

        result
    }
    fn evaluate_logical(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<Types, Error> {
        self.evaluate_binary(left, token, right)
    }
    fn evaluate_binary(
        &mut self,
        left: &mut Expr,
        token: &Token,
        right: &mut Expr,
    ) -> Result<Types, Error> {
        let mut left_type = self.expr_type(left)?;
        let mut right_type = self.expr_type(right)?;

        if left_type == Types::Void || right_type == Types::Void {
            return Err(Error::new(
                token,
                &format!(
                    "invalid binary expression: {} {} {}",
                    left_type, token.token, right_type
                ),
            ));
        }

        left_type = self.maybe_int_promote(left);
        right_type = self.maybe_int_promote(right);

        // TODO: translate this into codegen
        Ok(if left_type > right_type {
            left_type
        } else {
            right_type
        })
    }
    fn maybe_int_promote(&self, expr: &mut Expr) -> Types {
        if expr.type_decl.unwrap() < Types::Int {
            cast!(expr, Types::Int, CastUp);
            Types::Int
        } else {
            expr.type_decl.unwrap()
        }
    }
    fn evaluate_unary(&mut self, right: &mut Expr) -> Result<Types, Error> {
        self.expr_type(right)
    }
    fn evaluate_grouping(&mut self, expr: &mut Expr) -> Result<Types, Error> {
        self.expr_type(expr)
    }
    fn check_return(&mut self, keyword: &Token, body_return: Types) -> Result<(), Error> {
        match self.find_function() {
            Some(Scope::Function(_, function_type)) => {
                if *function_type == Types::Void && body_return != Types::Void {
                    return Err(Error::new(
                        keyword,
                        &format!(
                            "function return expects type:'void', found: {}",
                            body_return
                        ),
                    ));
                } else if *function_type != Types::Void && body_return == Types::Void {
                    return Err(Error::new(
                        keyword,
                        &format!(
                            "function return expects type:{}, found: 'void'",
                            function_type
                        ),
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    keyword,
                    "can only define return statements inside a function",
                ));
            }
        };
        Ok(())
    }
    fn find_function(&self) -> Option<&Scope> {
        for ref scope in self.scope.iter().rev() {
            if matches!(scope, Scope::Function(_, _)) {
                return Some(scope);
            }
        }
        None
    }
}
