use std::collections::hash_map::{Entry, HashMap};
use std::convert::TryFrom;
use std::fmt;

use crate::interpreter::Interpreter;
use crate::parser;
use crate::reporter::Reporter;

// FIXME(yanchith): impl error::Error;
// FIXME(yanchith): span info
pub enum ResolveError {
    VarReadsItselfInInitializer(String),
    VarRedeclaredInLocalScope(String),
    TopLevelReturnStatement,
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ResolveError::VarReadsItselfInInitializer(ident) => write!(
                f,
                "Variable declaration '{}' refers to itself in its initializer",
                ident,
            ),
            ResolveError::VarRedeclaredInLocalScope(ident) => {
                write!(f, "Variable '{}' already declared in this scope", ident)
            }
            ResolveError::TopLevelReturnStatement => {
                write!(f, "Can't use top level return statement")
            }
        }
    }
}

pub type ResolveResult = Result<(), ResolveError>;

pub fn resolve(reporter: &mut Reporter, interpreter: &mut Interpreter, stmts: &[parser::Stmt]) {
    let mut ctx = ResolveCtx::new(interpreter);
    let res = resolve_stmts(&mut ctx, stmts);

    if let Err(err) = res {
        reporter.report_compile_error(err.to_string());
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FunctionTy {
    None,
    Function,
}

#[derive(Debug)]
struct ResolveCtx<'a> {
    interpreter: &'a mut Interpreter,
    scopes: Vec<HashMap<String, bool>>,
    current_function: FunctionTy,
}

impl<'a> ResolveCtx<'a> {
    fn new(interpreter: &'a mut Interpreter) -> Self {
        Self {
            interpreter,
            scopes: Vec::new(),
            current_function: FunctionTy::None,
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn current_function(&self) -> FunctionTy {
        self.current_function
    }

    fn set_current_function(&mut self, function: FunctionTy) {
        self.current_function = function;
    }

    fn declare(&mut self, ident: &str) -> ResolveResult {
        if let Some(scope) = self.scopes.last_mut() {
            match scope.entry(ident.to_string()) {
                Entry::Occupied(_) => {
                    Err(ResolveError::VarRedeclaredInLocalScope(ident.to_string()))
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(false);
                    Ok(())
                }
            }
        } else {
            // Declaring (even redeclaring) variables in global scope is fine
            Ok(())
        }
    }

    fn define(&mut self, ident: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            let declaration = scope
                .get_mut(ident)
                .expect("Variable should already be declared");
            *declaration = true;
        }
    }

    fn write_resolution(&mut self, ast_id: u64, ident: &str) {
        for (distance, scope) in self.scopes.iter().rev().enumerate() {
            if scope.contains_key(ident) {
                self.interpreter.resolve(
                    ast_id,
                    u64::try_from(distance).expect("Scope distance too large"),
                );
                return;
            }
        }
    }
}

fn resolve_stmts(ctx: &mut ResolveCtx, stmts: &[parser::Stmt]) -> ResolveResult {
    for stmt in stmts {
        resolve_stmt(ctx, stmt)?;
    }

    Ok(())
}

fn resolve_stmt(ctx: &mut ResolveCtx, stmt: &parser::Stmt) -> ResolveResult {
    match stmt {
        parser::Stmt::VarDecl(var_decl) => resolve_var_decl_stmt(ctx, var_decl),
        parser::Stmt::FunDecl(fun_decl) => resolve_fun_decl_stmt(ctx, fun_decl),
        parser::Stmt::Expr(expr) => resolve_expr_stmt(ctx, expr),
        parser::Stmt::If(if_) => resolve_if_stmt(ctx, if_),
        parser::Stmt::While(while_) => resolve_while_stmt(ctx, while_),
        parser::Stmt::Print(print) => resolve_print_stmt(ctx, print),
        parser::Stmt::Return(return_) => resolve_return_stmt(ctx, return_),
        parser::Stmt::Block(block) => resolve_block_stmt(ctx, block),
    }
}

fn resolve_var_decl_stmt(ctx: &mut ResolveCtx, var_decl: &parser::VarDeclStmt) -> ResolveResult {
    // We first declare the variable, then resolve the initializer,
    // and only afterwards mark the variable as defined. This is
    // because the initializer expression lives in the same scope as
    // the variable declaration and could potentially refer to itself
    // (which we forbid by not allowing use of declared but not yet
    // defined variables).

    ctx.declare(var_decl.ident())?;
    if let Some(initializer) = var_decl.initializer() {
        resolve_expr(ctx, initializer)?;
    }
    ctx.define(var_decl.ident());

    Ok(())
}

fn resolve_fun_decl_stmt(ctx: &mut ResolveCtx, fun_decl: &parser::FunDeclStmt) -> ResolveResult {
    ctx.declare(fun_decl.ident())?;
    ctx.define(fun_decl.ident());

    let enclosing_function = ctx.current_function();
    ctx.set_current_function(FunctionTy::Function);
    ctx.push_scope();
    for param in fun_decl.params() {
        ctx.declare(param)?;
        ctx.define(param);
    }
    resolve_stmts(ctx, fun_decl.body())?;
    ctx.pop_scope();
    ctx.set_current_function(enclosing_function);

    Ok(())
}

fn resolve_expr_stmt(ctx: &mut ResolveCtx, expr: &parser::ExprStmt) -> ResolveResult {
    resolve_expr(ctx, expr.expr())
}

fn resolve_if_stmt(ctx: &mut ResolveCtx, if_: &parser::IfStmt) -> ResolveResult {
    resolve_expr(ctx, if_.cond())?;
    resolve_stmt(ctx, if_.then())?;
    if let Some(else_) = if_.else_() {
        resolve_stmt(ctx, else_)?;
    }

    Ok(())
}

fn resolve_while_stmt(ctx: &mut ResolveCtx, while_: &parser::WhileStmt) -> ResolveResult {
    resolve_expr(ctx, while_.cond())?;
    resolve_stmt(ctx, while_.loop_())?;

    Ok(())
}

fn resolve_print_stmt(ctx: &mut ResolveCtx, print: &parser::PrintStmt) -> ResolveResult {
    resolve_expr(ctx, print.expr())
}

fn resolve_return_stmt(ctx: &mut ResolveCtx, return_: &parser::ReturnStmt) -> ResolveResult {
    if let FunctionTy::None = ctx.current_function() {
        Err(ResolveError::TopLevelReturnStatement)
    } else if let Some(expr) = return_.expr() {
        resolve_expr(ctx, expr)
    } else {
        Ok(())
    }
}

fn resolve_block_stmt(ctx: &mut ResolveCtx, block: &parser::BlockStmt) -> ResolveResult {
    ctx.push_scope();
    resolve_stmts(ctx, block.stmts())?;
    ctx.pop_scope();

    Ok(())
}

fn resolve_expr(ctx: &mut ResolveCtx, expr: &parser::Expr) -> ResolveResult {
    match expr {
        parser::Expr::Lit(lit) => resolve_lit_expr(ctx, lit),
        parser::Expr::Group(group) => resolve_group_expr(ctx, group),
        parser::Expr::Unary(unary) => resolve_unary_expr(ctx, unary),
        parser::Expr::Binary(binary) => resolve_binary_expr(ctx, binary),
        parser::Expr::Logic(logic) => resolve_logic_expr(ctx, logic),
        parser::Expr::Var(var) => resolve_var_expr(ctx, var),
        parser::Expr::Assign(assign) => resolve_assign_expr(ctx, assign),
        parser::Expr::Call(call) => resolve_call_expr(ctx, call),
    }
}

fn resolve_lit_expr(_: &mut ResolveCtx, _: &parser::LitExpr) -> ResolveResult {
    Ok(())
}

fn resolve_group_expr(ctx: &mut ResolveCtx, group: &parser::GroupExpr) -> ResolveResult {
    resolve_expr(ctx, group.expr())
}

fn resolve_unary_expr(ctx: &mut ResolveCtx, unary: &parser::UnaryExpr) -> ResolveResult {
    resolve_expr(ctx, unary.expr())
}

fn resolve_binary_expr(ctx: &mut ResolveCtx, binary: &parser::BinaryExpr) -> ResolveResult {
    resolve_expr(ctx, binary.left())?;
    resolve_expr(ctx, binary.right())?;

    Ok(())
}

fn resolve_logic_expr(ctx: &mut ResolveCtx, logic: &parser::LogicExpr) -> ResolveResult {
    resolve_expr(ctx, logic.left())?;
    resolve_expr(ctx, logic.right())?;

    Ok(())
}

fn resolve_var_expr(ctx: &mut ResolveCtx, var: &parser::VarExpr) -> ResolveResult {
    if let Some(scope) = ctx.scopes.last_mut() {
        if let Some(false) = scope.get(var.ident()) {
            let ident = var.ident().to_string();
            return Err(ResolveError::VarReadsItselfInInitializer(ident));
        }
    }

    ctx.write_resolution(var.ast_id(), var.ident());

    Ok(())
}

fn resolve_assign_expr(ctx: &mut ResolveCtx, assign: &parser::AssignExpr) -> ResolveResult {
    resolve_expr(ctx, assign.expr())?;

    ctx.write_resolution(assign.ast_id(), assign.ident());

    Ok(())
}

fn resolve_call_expr(ctx: &mut ResolveCtx, call: &parser::CallExpr) -> ResolveResult {
    resolve_expr(ctx, call.callee())?;
    for arg in call.args() {
        resolve_expr(ctx, arg)?;
    }

    Ok(())
}
