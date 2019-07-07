use std::convert::TryFrom;
use std::fmt;

use crate::token::{Token, TokenValue};

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    stmts: Vec<Stmt>,
}

impl Program {
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(program")?;

        for stmt in &self.stmts {
            f.write_str(" ")?;
            f.write_str(&stmt.to_string())?;
        }

        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    VarDecl(VarDeclStmt),
    FunDecl(FunDeclStmt),
    ClassDecl(ClassDeclStmt),
    Expr(ExprStmt),
    If(IfStmt),
    While(WhileStmt),
    Print(PrintStmt),
    Return(ReturnStmt),
    Block(BlockStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::VarDecl(var_decl) => write!(f, "{}", var_decl),
            Stmt::FunDecl(fun_decl) => write!(f, "{}", fun_decl),
            Stmt::ClassDecl(class_decl) => write!(f, "{}", class_decl),
            Stmt::Expr(expr) => write!(f, "{}", expr),
            Stmt::If(if_) => write!(f, "{}", if_),
            Stmt::While(while_) => write!(f, "{}", while_),
            Stmt::Print(print) => write!(f, "{}", print),
            Stmt::Return(return_) => write!(f, "{}", return_),
            Stmt::Block(block) => write!(f, "{}", block),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    ident: String, // FIXME(yanchith): intern idents
    initializer: Option<Expr>,
}

impl VarDeclStmt {
    pub fn new(ident: String, initializer: Option<Expr>) -> Self {
        Self { ident, initializer }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn initializer(&self) -> Option<&Expr> {
        self.initializer.as_ref()
    }
}

impl fmt::Display for VarDeclStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.initializer {
            Some(expr) => write!(f, "(decl {} {})", self.ident, expr),
            None => write!(f, "(decl {})", self.ident),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    ident: String, // FIXME(yanchith): indern idents
    params: Vec<String>,
    body: Vec<Stmt>,
}

impl FunDeclStmt {
    pub fn new(ident: String, params: Vec<String>, body: Vec<Stmt>) -> Self {
        Self {
            ident,
            params,
            body,
        }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    // FIXME(yanchith): try using &[&str] as return type
    pub fn params(&self) -> &[String] {
        &self.params
    }

    pub fn body(&self) -> &[Stmt] {
        &self.body
    }
}

impl fmt::Display for FunDeclStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(fun ")?;
        f.write_str(&self.ident)?;

        for param in &self.params {
            f.write_str(" ")?;
            f.write_str(param)?;
        }

        for stmt in &self.body {
            f.write_str(" ")?;
            f.write_str(&stmt.to_string())?;
        }
        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassDeclStmt {
    ident: String, // FIXME(yanchith): intern
    methods: Vec<FunDeclStmt>,
}

impl ClassDeclStmt {
    pub fn new(ident: String, methods: Vec<FunDeclStmt>) -> Self {
        Self { ident, methods }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn methods(&self) -> &[FunDeclStmt] {
        &self.methods
    }
}

impl fmt::Display for ClassDeclStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(class ")?;
        f.write_str(&self.ident)?;

        for method in &self.methods {
            f.write_str(" ")?;
            f.write_str(&method.to_string())?;
        }
        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    expr: Expr,
}

impl ExprStmt {
    pub fn new(expr: Expr) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }
}

impl fmt::Display for ExprStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(expr {})", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    cond: Expr,
    then: Box<Stmt>,
    else_: Option<Box<Stmt>>,
}

impl IfStmt {
    pub fn new(cond: Expr, then: Stmt, else_: Option<Stmt>) -> Self {
        Self {
            cond,
            then: Box::new(then),
            else_: else_.map(Box::new),
        }
    }

    pub fn cond(&self) -> &Expr {
        &self.cond
    }

    pub fn then(&self) -> &Stmt {
        &self.then
    }

    pub fn else_(&self) -> Option<&Stmt> {
        match &self.else_ {
            Some(else_) => Some(&else_),
            None => None,
        }
    }
}

impl fmt::Display for IfStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.else_ {
            Some(else_) => write!(f, "(if {} {} {})", self.cond, self.then, else_),
            None => write!(f, "(if {} {})", self.cond, self.then),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    cond: Expr,
    loop_: Box<Stmt>,
}

impl WhileStmt {
    pub fn new(cond: Expr, loop_: Stmt) -> Self {
        Self {
            cond,
            loop_: Box::new(loop_),
        }
    }

    pub fn cond(&self) -> &Expr {
        &self.cond
    }

    pub fn loop_(&self) -> &Stmt {
        &self.loop_
    }
}

impl fmt::Display for WhileStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(loop {} {})", self.cond, self.loop_)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrintStmt {
    expr: Expr,
}

impl PrintStmt {
    pub fn new(expr: Expr) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }
}

impl fmt::Display for PrintStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(print {})", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    expr: Option<Expr>,
}

impl ReturnStmt {
    pub fn new(expr: Option<Expr>) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> Option<&Expr> {
        self.expr.as_ref()
    }
}

impl fmt::Display for ReturnStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.expr {
            Some(expr) => write!(f, "(return {})", expr),
            None => write!(f, "(return)"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStmt {
    stmts: Vec<Stmt>,
}

impl BlockStmt {
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }
}

impl fmt::Display for BlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(block")?;

        for stmt in &self.stmts {
            f.write_str(" ")?;
            f.write_str(&stmt.to_string())?;
        }

        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Lit(LitExpr),
    Group(GroupExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Logic(LogicExpr),
    Var(VarExpr),
    Assign(AssignExpr),
    Call(CallExpr),
    Get(GetExpr),
    Set(SetExpr),
    This(ThisExpr),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Lit(lit) => write!(f, "{}", lit),
            Expr::Group(group) => write!(f, "{}", group),
            Expr::Unary(unary) => write!(f, "{}", unary),
            Expr::Binary(binary) => write!(f, "{}", binary),
            Expr::Logic(logic) => write!(f, "{}", logic),
            Expr::Var(var) => write!(f, "{}", var),
            Expr::Assign(assign) => write!(f, "{}", assign),
            Expr::Call(call) => write!(f, "{}", call),
            Expr::Get(get) => write!(f, "{}", get),
            Expr::Set(set) => write!(f, "{}", set),
            Expr::This(this) => write!(f, "{}", this),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LitExpr {
    Number(f64),
    String(String),
    Boolean(bool),
    Nil,
}

impl fmt::Display for LitExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LitExpr::Number(number) => write!(f, "{}", number),
            LitExpr::String(string) => write!(f, "\"{}\"", string),
            LitExpr::Boolean(boolean) => write!(f, "{}", boolean),
            LitExpr::Nil => write!(f, "nil"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GroupExpr {
    expr: Box<Expr>,
}

impl GroupExpr {
    pub fn new(expr: Expr) -> Self {
        Self {
            expr: Box::new(expr),
        }
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }
}

impl fmt::Display for GroupExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(group {})", self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    expr: Box<Expr>,
    op: UnaryOp,
}

impl UnaryExpr {
    pub fn new(expr: Expr, op: UnaryOp) -> Self {
        Self {
            expr: Box::new(expr),
            op,
        }
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }

    pub fn op(&self) -> UnaryOp {
        self.op
    }
}

impl fmt::Display for UnaryExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.op, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    left: Box<Expr>,
    right: Box<Expr>,
    op: BinaryOp,
}

impl BinaryExpr {
    pub fn new(left: Expr, right: Expr, op: BinaryOp) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            op,
        }
    }

    pub fn left(&self) -> &Expr {
        &self.left
    }

    pub fn right(&self) -> &Expr {
        &self.right
    }

    pub fn op(&self) -> BinaryOp {
        self.op
    }
}

impl fmt::Display for BinaryExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {} {})", self.op, self.left, self.right)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicExpr {
    left: Box<Expr>,
    right: Box<Expr>,
    op: LogicOp,
}

impl LogicExpr {
    pub fn new(left: Expr, right: Expr, op: LogicOp) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            op,
        }
    }

    pub fn left(&self) -> &Expr {
        &self.left
    }

    pub fn right(&self) -> &Expr {
        &self.right
    }

    pub fn op(&self) -> LogicOp {
        self.op
    }
}

impl fmt::Display for LogicExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {} {})", self.op, self.left, self.right)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarExpr {
    ast_id: u64,
    ident: String,
}

impl VarExpr {
    pub fn new(ast_id: u64, ident: String) -> Self {
        Self { ast_id, ident }
    }

    pub fn ast_id(&self) -> u64 {
        self.ast_id
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }
}

impl fmt::Display for VarExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.ident)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    ast_id: u64,
    ident: String, // FIXME(yanchith): use a `Token` here for span info
    expr: Box<Expr>,
}

impl AssignExpr {
    pub fn new(ast_id: u64, ident: String, expr: Expr) -> Self {
        Self {
            ast_id,
            ident,
            expr: Box::new(expr),
        }
    }

    pub fn ast_id(&self) -> u64 {
        self.ast_id
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }
}

impl fmt::Display for AssignExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(assign {} {})", self.ident, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    callee: Box<Expr>,
    args: Vec<Expr>,
}

impl CallExpr {
    pub fn new(callee: Expr, args: Vec<Expr>) -> Self {
        Self {
            callee: Box::new(callee),
            args,
        }
    }

    pub fn callee(&self) -> &Expr {
        &self.callee
    }

    pub fn args(&self) -> &[Expr] {
        &self.args
    }
}

impl fmt::Display for CallExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(call {}", self.callee)?;

        for arg in &self.args {
            f.write_str(" ")?;
            f.write_str(&arg.to_string())?;
        }

        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GetExpr {
    object: Box<Expr>,
    field: String,
}

impl GetExpr {
    pub fn new(object: Expr, field: String) -> Self {
        Self {
            object: Box::new(object),
            field,
        }
    }

    pub fn object(&self) -> &Expr {
        &self.object
    }

    pub fn field(&self) -> &str {
        &self.field
    }
}

impl fmt::Display for GetExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(. {} {})", self.object, self.field)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SetExpr {
    object: Box<Expr>,
    field: String,
    value: Box<Expr>,
}

impl SetExpr {
    pub fn new(object: Expr, field: String, value: Expr) -> Self {
        Self {
            object: Box::new(object),
            field,
            value: Box::new(value),
        }
    }

    pub fn object(&self) -> &Expr {
        &self.object
    }

    pub fn field(&self) -> &str {
        &self.field
    }

    pub fn value(&self) -> &Expr {
        &self.value
    }
}

impl fmt::Display for SetExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(.= {} {} {})", self.object, self.field, self.value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ThisExpr {
    ast_id: u64,
}

impl ThisExpr {
    pub fn new(ast_id: u64) -> Self {
        Self { ast_id }
    }

    pub fn ast_id(&self) -> u64 {
        self.ast_id
    }
}

impl fmt::Display for ThisExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "this")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Minus,
}

// FIXME(yanchith): token in error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryOpFromTokenError;

impl TryFrom<Token> for UnaryOp {
    type Error = UnaryOpFromTokenError;

    fn try_from(token: Token) -> Result<UnaryOp, Self::Error> {
        match token.value() {
            TokenValue::Bang => Ok(UnaryOp::Not),
            TokenValue::Minus => Ok(UnaryOp::Minus),
            _ => Err(UnaryOpFromTokenError),
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                UnaryOp::Not => "!",
                UnaryOp::Minus => "-",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Plus,
    Minus,
    Multiply,
    Divide,
}

// FIXME(yanchith): token in error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryOpFromTokenError;

impl TryFrom<Token> for BinaryOp {
    type Error = BinaryOpFromTokenError;

    fn try_from(token: Token) -> Result<BinaryOp, Self::Error> {
        match token.value() {
            TokenValue::EqualEqual => Ok(BinaryOp::Equal),
            TokenValue::BangEqual => Ok(BinaryOp::NotEqual),
            TokenValue::Less => Ok(BinaryOp::Less),
            TokenValue::LessEqual => Ok(BinaryOp::LessEqual),
            TokenValue::Greater => Ok(BinaryOp::Greater),
            TokenValue::GreaterEqual => Ok(BinaryOp::GreaterEqual),
            TokenValue::Plus => Ok(BinaryOp::Plus),
            TokenValue::Minus => Ok(BinaryOp::Minus),
            TokenValue::Star => Ok(BinaryOp::Multiply),
            TokenValue::Slash => Ok(BinaryOp::Divide),
            _ => Err(BinaryOpFromTokenError),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinaryOp::Equal => "==",
                BinaryOp::NotEqual => "!=",
                BinaryOp::Less => "<",
                BinaryOp::LessEqual => "<=",
                BinaryOp::Greater => ">",
                BinaryOp::GreaterEqual => ">=",
                BinaryOp::Plus => "+",
                BinaryOp::Minus => "-",
                BinaryOp::Multiply => "*",
                BinaryOp::Divide => "/",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicOp {
    And,
    Or,
}

impl fmt::Display for LogicOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                LogicOp::And => "and",
                LogicOp::Or => "or",
            }
        )
    }
}
