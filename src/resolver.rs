use std::collections::hash_map::{Entry, HashMap};
use std::convert::TryFrom;
use std::fmt;

use crate::ast;
use crate::interpreter::Interpreter;
use crate::reporter::Reporter;

// FIXME(yanchith): impl error::Error;
// FIXME(yanchith): span info
pub enum ResolveError {
    VarReadsItselfInInitializer(String),
    VarRedeclaredInLocalScope(String),
    TopLevelReturnStatement,
    ThisOutsideMethod,
    InitializerReturnsValue,
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
            ResolveError::ThisOutsideMethod => write!(f, "Can't use 'this' outside of methods"),
            ResolveError::InitializerReturnsValue => write!(f, "Initializers Can't return a value"),
        }
    }
}

pub type ResolveResult = Result<(), ResolveError>;

pub fn resolve(reporter: &mut Reporter, interpreter: &mut Interpreter, stmts: &[ast::Stmt]) {
    let mut ctx = ResolveCtx::new(interpreter);
    let res = resolve_stmts(&mut ctx, stmts);

    if let Err(err) = res {
        reporter.report_compile_error(err.to_string());
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FunTy {
    None,
    Function,
    Method,
    Initializer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ClassTy {
    None,
    Class,
}

#[derive(Debug)]
struct ResolveCtx<'a> {
    interpreter: &'a mut Interpreter,
    scopes: Vec<HashMap<String, bool>>,
    current_fun: FunTy,
    current_class: ClassTy,
}

impl<'a> ResolveCtx<'a> {
    fn new(interpreter: &'a mut Interpreter) -> Self {
        Self {
            interpreter,
            scopes: Vec::new(),
            current_fun: FunTy::None,
            current_class: ClassTy::None,
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn current_fun(&self) -> FunTy {
        self.current_fun
    }

    fn set_current_fun(&mut self, fun: FunTy) {
        self.current_fun = fun;
    }

    fn current_class(&self) -> ClassTy {
        self.current_class
    }

    fn set_current_class(&mut self, class: ClassTy) {
        self.current_class = class;
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

fn resolve_stmts(ctx: &mut ResolveCtx, stmts: &[ast::Stmt]) -> ResolveResult {
    for stmt in stmts {
        resolve_stmt(ctx, stmt)?;
    }

    Ok(())
}

fn resolve_stmt(ctx: &mut ResolveCtx, stmt: &ast::Stmt) -> ResolveResult {
    match stmt {
        ast::Stmt::VarDecl(var_decl) => resolve_var_decl_stmt(ctx, var_decl),
        ast::Stmt::FunDecl(fun_decl) => resolve_fun_decl_stmt(ctx, fun_decl, FunTy::Function),
        ast::Stmt::ClassDecl(class_decl) => resolve_class_decl_stmt(ctx, class_decl),
        ast::Stmt::Expr(expr) => resolve_expr_stmt(ctx, expr),
        ast::Stmt::If(if_) => resolve_if_stmt(ctx, if_),
        ast::Stmt::While(while_) => resolve_while_stmt(ctx, while_),
        ast::Stmt::Print(print) => resolve_print_stmt(ctx, print),
        ast::Stmt::Return(return_) => resolve_return_stmt(ctx, return_),
        ast::Stmt::Block(block) => resolve_block_stmt(ctx, block),
    }
}

fn resolve_var_decl_stmt(ctx: &mut ResolveCtx, var_decl: &ast::VarDeclStmt) -> ResolveResult {
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

fn resolve_fun_decl_stmt(
    ctx: &mut ResolveCtx,
    fun_decl: &ast::FunDeclStmt,
    fun_ty: FunTy,
) -> ResolveResult {
    ctx.declare(fun_decl.ident())?;
    ctx.define(fun_decl.ident());

    let enclosing_fun = ctx.current_fun();
    ctx.set_current_fun(fun_ty);
    ctx.push_scope();
    for param in fun_decl.params() {
        ctx.declare(param)?;
        ctx.define(param);
    }
    resolve_stmts(ctx, fun_decl.body())?;
    ctx.pop_scope();
    ctx.set_current_fun(enclosing_fun);

    Ok(())
}

fn resolve_class_decl_stmt(ctx: &mut ResolveCtx, class_decl: &ast::ClassDeclStmt) -> ResolveResult {
    ctx.declare(class_decl.ident())?;
    ctx.define(class_decl.ident());

    // A class has its own scope with "this" defined
    let enclosing_class = ctx.current_class();
    ctx.set_current_class(ClassTy::Class);
    ctx.push_scope();

    ctx.declare("this")?;
    ctx.define("this");

    for method in class_decl.methods() {
        let fun_ty = if method.ident() == "init" {
            FunTy::Initializer
        } else {
            FunTy::Method
        };
        resolve_fun_decl_stmt(ctx, method, fun_ty)?;
    }

    ctx.pop_scope();
    ctx.set_current_class(enclosing_class);

    Ok(())
}

fn resolve_expr_stmt(ctx: &mut ResolveCtx, expr: &ast::ExprStmt) -> ResolveResult {
    resolve_expr(ctx, expr.expr())
}

fn resolve_if_stmt(ctx: &mut ResolveCtx, if_: &ast::IfStmt) -> ResolveResult {
    resolve_expr(ctx, if_.cond())?;
    resolve_stmt(ctx, if_.then())?;
    if let Some(else_) = if_.else_() {
        resolve_stmt(ctx, else_)?;
    }

    Ok(())
}

fn resolve_while_stmt(ctx: &mut ResolveCtx, while_: &ast::WhileStmt) -> ResolveResult {
    resolve_expr(ctx, while_.cond())?;
    resolve_stmt(ctx, while_.loop_())?;

    Ok(())
}

fn resolve_print_stmt(ctx: &mut ResolveCtx, print: &ast::PrintStmt) -> ResolveResult {
    resolve_expr(ctx, print.expr())
}

fn resolve_return_stmt(ctx: &mut ResolveCtx, return_: &ast::ReturnStmt) -> ResolveResult {
    let current_fun = ctx.current_fun();
    if current_fun == FunTy::None {
        Err(ResolveError::TopLevelReturnStatement)
    } else if let Some(expr) = return_.expr() {
        if current_fun == FunTy::Initializer {
            Err(ResolveError::InitializerReturnsValue)
        } else {
            resolve_expr(ctx, expr)
        }
    } else {
        Ok(())
    }
}

fn resolve_block_stmt(ctx: &mut ResolveCtx, block: &ast::BlockStmt) -> ResolveResult {
    ctx.push_scope();
    resolve_stmts(ctx, block.stmts())?;
    ctx.pop_scope();

    Ok(())
}

fn resolve_expr(ctx: &mut ResolveCtx, expr: &ast::Expr) -> ResolveResult {
    match expr {
        ast::Expr::Lit(lit) => resolve_lit_expr(ctx, lit),
        ast::Expr::Group(group) => resolve_group_expr(ctx, group),
        ast::Expr::Unary(unary) => resolve_unary_expr(ctx, unary),
        ast::Expr::Binary(binary) => resolve_binary_expr(ctx, binary),
        ast::Expr::Logic(logic) => resolve_logic_expr(ctx, logic),
        ast::Expr::Var(var) => resolve_var_expr(ctx, var),
        ast::Expr::Assign(assign) => resolve_assign_expr(ctx, assign),
        ast::Expr::Call(call) => resolve_call_expr(ctx, call),
        ast::Expr::Get(get) => resolve_get_expr(ctx, get),
        ast::Expr::Set(set) => resolve_set_expr(ctx, set),
        ast::Expr::This(this) => resolve_this_expr(ctx, this),
    }
}

fn resolve_lit_expr(_: &mut ResolveCtx, _: &ast::LitExpr) -> ResolveResult {
    Ok(())
}

fn resolve_group_expr(ctx: &mut ResolveCtx, group: &ast::GroupExpr) -> ResolveResult {
    resolve_expr(ctx, group.expr())
}

fn resolve_unary_expr(ctx: &mut ResolveCtx, unary: &ast::UnaryExpr) -> ResolveResult {
    resolve_expr(ctx, unary.expr())
}

fn resolve_binary_expr(ctx: &mut ResolveCtx, binary: &ast::BinaryExpr) -> ResolveResult {
    resolve_expr(ctx, binary.left())?;
    resolve_expr(ctx, binary.right())?;

    Ok(())
}

fn resolve_logic_expr(ctx: &mut ResolveCtx, logic: &ast::LogicExpr) -> ResolveResult {
    resolve_expr(ctx, logic.left())?;
    resolve_expr(ctx, logic.right())?;

    Ok(())
}

fn resolve_var_expr(ctx: &mut ResolveCtx, var: &ast::VarExpr) -> ResolveResult {
    if let Some(scope) = ctx.scopes.last_mut() {
        if let Some(false) = scope.get(var.ident()) {
            let ident = var.ident().to_string();
            return Err(ResolveError::VarReadsItselfInInitializer(ident));
        }
    }

    ctx.write_resolution(var.ast_id(), var.ident());

    Ok(())
}

fn resolve_assign_expr(ctx: &mut ResolveCtx, assign: &ast::AssignExpr) -> ResolveResult {
    resolve_expr(ctx, assign.expr())?;

    ctx.write_resolution(assign.ast_id(), assign.ident());

    Ok(())
}

fn resolve_call_expr(ctx: &mut ResolveCtx, call: &ast::CallExpr) -> ResolveResult {
    resolve_expr(ctx, call.callee())?;
    for arg in call.args() {
        resolve_expr(ctx, arg)?;
    }

    Ok(())
}

fn resolve_get_expr(ctx: &mut ResolveCtx, get: &ast::GetExpr) -> ResolveResult {
    resolve_expr(ctx, get.object())
}

fn resolve_set_expr(ctx: &mut ResolveCtx, set: &ast::SetExpr) -> ResolveResult {
    resolve_expr(ctx, set.object())?;
    resolve_expr(ctx, set.value())?;

    Ok(())
}

fn resolve_this_expr(ctx: &mut ResolveCtx, this: &ast::ThisExpr) -> ResolveResult {
    if let ClassTy::None = ctx.current_class() {
        Err(ResolveError::ThisOutsideMethod)
    } else {
        ctx.write_resolution(this.ast_id(), "this");
        Ok(())
    }
}
