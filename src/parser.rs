//! The parser.
//!
//! It parses.
//!
//! # Grammar
//!
//! ```text
//! program   → declaration* EOF ;
//! ```
//!
//! ## Statements
//!
//! We express "statement precedence" in production rules. Declaration
//! statements are not allowed everywhere other stmts are, so we have
//! to give them lower precedence, specifying them earlier in the
//! production rules. Places that disallow declarations will use the
//! later, higher-precedence rules only.
//!
//! ```text
//! declaration → varDeclStmt
//!             → funDeclStmt
//!             | statement ;
//!
//! funDeclStmt → "fun" function ;
//! function    → IDENTIFIER "(" parameters? ")" block ;
//! parameters  → IDENTIFIER ( "," IDENTIFIER )* ;
//!
//! statement → exprStmt
//!           | ifStmt
//!           | forStmt
//!           | whileStmt
//!           | printStmt
//!           | returnStmt
//!           | block ;
//!
//! exprStmt  → expr ";" ;
//! ifStmt    → "if" "(" expression ")" statement ( "else" statement )? ;
//! forStmt   → "for" "(" ( varDeclStmt | exprStmt | ";" )
//!                       expression? ";"
//!                       expression? ")" statement ;
//! whileStmt → "while" "(" expression ")" statement ;
//! printStmt → "print" expr ";" ;
//! returnStmt → "return" expression? ";" ;
//! block     → "{" declaration* "}" ;
//! ```
//!
//! ## Expressions
//!
//! We express op precedence in production rules.
//!
//! ```text
//! expression     → assignment ;
//! assignment     → identifier "=" assignment
//!                | logic_or ;
//! logic_or       → logic_and ( "or" logic_and )* ;
//! logic_and      → equality ( "and" equality )* ;
//!
//! equality       → comparison ( ( "!=" | "==" ) comparison )* ;
//! comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
//! addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
//! multiplication → unary ( ( "/" | "*" ) unary )* ;
//! unary          → ( "!" | "-" ) unary
//!                | call ;
//! call           → primary ( "(" arguments? ")" )* ;
//! primary        → NUMBER | STRING | "false" | "true" | "nil"
//!                | "(" expr ")" ;
//!
//! arguments      → expression ( "," expression )* ;
//! ```

use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::slice;

use crate::lexer::{Token, TokenValue};
use crate::reporter::Reporter;

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
    ident: String, // TODO: intern idents
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
    ident: String, // TODO: indern idents
    parameters: Vec<String>,
    body: Vec<Stmt>,
}

impl FunDeclStmt {
    pub fn new(ident: String, parameters: Vec<String>, body: Vec<Stmt>) -> Self {
        Self {
            ident,
            parameters,
            body,
        }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    // TODO: try using &[&str] as return type
    pub fn parameters(&self) -> &[String] {
        &self.parameters
    }

    pub fn body(&self) -> &[Stmt] {
        &self.body
    }
}

impl fmt::Display for FunDeclStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("(fun (parameters")?;

        for parameter in &self.parameters {
            f.write_str(" ")?;
            f.write_str(parameter)?;
        }
        f.write_str(")")?;

        for stmt in &self.body {
            f.write_str(" ")?;
            f.write_str(&stmt.to_string())?;
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
    pub fn new(cond: Expr, then: Stmt) -> Self {
        Self {
            cond,
            then: Box::new(then),
            else_: None,
        }
    }

    pub fn with_else_branch(cond: Expr, then: Stmt, else_: Stmt) -> Self {
        Self {
            cond,
            then: Box::new(then),
            else_: Some(Box::new(else_)),
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
    Assignment(AssignmentExpr),
    Call(CallExpr),
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
            Expr::Assignment(assignment) => write!(f, "{}", assignment),
            Expr::Call(call) => write!(f, "{}", call),
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
    ident: String,
}

impl VarExpr {
    pub fn new(ident: String) -> Self {
        Self { ident }
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
pub struct AssignmentExpr {
    // `target` is not called `ident`, because it doesn't need to be
    // just an identifier, but any lvalue
    target: VarExpr,
    expr: Box<Expr>,
}

impl AssignmentExpr {
    pub fn new(target: VarExpr, expr: Expr) -> Self {
        Self {
            target,
            expr: Box::new(expr),
        }
    }

    pub fn target(&self) -> &VarExpr {
        &self.target
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }
}

impl fmt::Display for AssignmentExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(assignment {} {})", self.target, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    callee: Box<Expr>,
    arguments: Vec<Expr>,
}

impl CallExpr {
    pub fn new(callee: Expr, arguments: Vec<Expr>) -> Self {
        Self {
            callee: Box::new(callee),
            arguments,
        }
    }

    pub fn callee(&self) -> &Expr {
        &self.callee
    }

    pub fn arguments(&self) -> &[Expr] {
        &self.arguments
    }
}

impl fmt::Display for CallExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(call {}", self.callee)?;

        for argument in &self.arguments {
            f.write_str(" ")?;
            f.write_str(&argument.to_string())?;
        }

        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Minus,
}

// TODO: token in error
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

// TODO: token in error
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

// TODO: implement std::error:Error
#[derive(Debug)]
pub enum ParseError {
    ExpectedSemicolonAfterExprStmt(Option<Token>),
    ExpectedSemicolonAfterPrintStmt(Option<Token>),
    ExpectedSemicolonAfterReturnStmt(Option<Token>),
    ExpectedSemicolonAfterVarDeclStmt(Option<Token>),
    ExpectedIdentAfterVarKeyword(Option<Token>),
    ExpectedIdentAfterFunKeyword(Option<Token>),
    ExpectedOpeningParenAfterFunIdent(Option<Token>),
    ExpectedIdentInFunParameters(Option<Token>),
    ExpectedBlockAfterFunHeader(Option<Token>),
    ExpectedClosingParenAfterFunParameters(Option<Token>),
    ExpectedClosingParenAfterGroupExpr(Option<Token>),
    ExpectedClosingBraceAfterBlockStmt,
    ExpectedOpeningParenAfterIf(Option<Token>),
    ExpectedOpeningParenAfterFor(Option<Token>),
    ExpectedOpeningParenAfterWhile(Option<Token>),
    ExpectedClosingParenAfterIfCond(Option<Token>),
    ExpectedClosingParenAfterWhileCond(Option<Token>),
    ExpectedSemicolonAfterForCond(Option<Token>),
    ExpectedClosingParenAfterForIncrement(Option<Token>),
    ExpectedClosingParenAfterCall(Option<Token>),
    ExpectedPrimaryExpr(Option<Token>),
    InvalidAssignmentTarget(Expr),
    TooManyCallArguments(Expr),
    TooManyFunParameters(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::ExpectedSemicolonAfterExprStmt(Some(token)) => write!(
                f,
                "Expected semicolon after expression statement but found token {}",
                token,
            ),
            ParseError::ExpectedSemicolonAfterExprStmt(None) => write!(
                f,
                "Expected semicolon after expression statement but found end of input",
            ),
            ParseError::ExpectedSemicolonAfterPrintStmt(Some(token)) => write!(
                f,
                "Expected semicolon after print statement but found token {}",
                token,
            ),
            ParseError::ExpectedSemicolonAfterPrintStmt(None) => write!(
                f,
                "Expected semicolon after print statement but found end of input",
            ),
            ParseError::ExpectedSemicolonAfterReturnStmt(Some(token)) => write!(
                f,
                "Expected semicolon after return statement but found token {}",
                token,
            ),
            ParseError::ExpectedSemicolonAfterReturnStmt(None) => write!(
                f,
                "Expected semicolon after return statement but found end of input",
            ),
            ParseError::ExpectedSemicolonAfterVarDeclStmt(Some(token)) => write!(
                f,
                "Expected semicolon after variable declaration statement but found token {}",
                token,
            ),
            ParseError::ExpectedSemicolonAfterVarDeclStmt(None) => write!(
                f,
                "Expected semicolon after variable declaration statement but found end of input",
            ),
            ParseError::ExpectedIdentAfterVarKeyword(Some(token)) => write!(
                f,
                "Expected identifier after 'var' keyword but found token {}",
                token,
            ),
            ParseError::ExpectedIdentAfterVarKeyword(None) => write!(
                f,
                "Expected identifier after 'var' keyword but found end of input",
            ),
            ParseError::ExpectedIdentAfterFunKeyword(Some(token)) => write!(
                f,
                "Expected identifier after 'fun' keyword but found token {}",
                token,
            ),
            ParseError::ExpectedIdentAfterFunKeyword(None) => write!(
                f,
                "Expected identifier after 'fun' keyword but found end of input",
            ),
            ParseError::ExpectedOpeningParenAfterFunIdent(Some(token)) => write!(
                f,
                "Expected opening parenthesis after function identifier but found {}",
                token,
            ),
            ParseError::ExpectedOpeningParenAfterFunIdent(None) => write!(
                f,
                "Expected opening parenthesis after function identifier but found end of input",
            ),
            ParseError::ExpectedIdentInFunParameters(Some(token)) => write!(
                f,
                "Expected identifier in function parameter list but found {}",
                token,
            ),
            ParseError::ExpectedIdentInFunParameters(None) => write!(
                f,
                "Expected identifier in function parameter list but found end of input",
            ),
            ParseError::ExpectedBlockAfterFunHeader(Some(token)) => write!(
                f,
                "Expected block after function header but found {}",
                token,
            ),
            ParseError::ExpectedBlockAfterFunHeader(None) => write!(
                f,
                "Expected block after function header but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterFunParameters(Some(token)) => write!(
                f,
                "Expeced closing parenthesis after function parameters but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterFunParameters(None) => write!(
                f,
                "Expeced closing parenthesis after function parameters but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterGroupExpr(Some(token)) => write!(
                f,
                "Expected closing parenthesis after group expression but found token {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterGroupExpr(None) => write!(
                f,
                "Expected closing parenthesis after group expression but found end of input",
            ),
            ParseError::ExpectedClosingBraceAfterBlockStmt => write!(
                f,
                "Expected closing brace after block statement but found end of input",
            ),
            ParseError::ExpectedOpeningParenAfterIf(Some(token)) => write!(
                f,
                "Expected opening parenthesis after 'if' keyword but found {}",
                token,
            ),
            ParseError::ExpectedOpeningParenAfterIf(None) => write!(
                f,
                "Expected opening parenthesis after 'if' keyword but found end of input",
            ),
            ParseError::ExpectedOpeningParenAfterFor(Some(token)) => write!(
                f,
                "Expected opening parenthesis after 'for' keyword but found {}",
                token,
            ),
            ParseError::ExpectedOpeningParenAfterFor(None) => write!(
                f,
                "Expected opening parenthesis after 'for' keyword but found end of input",
            ),
            ParseError::ExpectedOpeningParenAfterWhile(Some(token)) => write!(
                f,
                "Expected opening parenthesis after 'while' keyword but found {}",
                token,
            ),
            ParseError::ExpectedOpeningParenAfterWhile(None) => write!(
                f,
                "Expected opening parenthesis after 'while' keyword but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterIfCond(Some(token)) => write!(
                f,
                "Expected closing parenthesis after 'if' statement condition but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterIfCond(None) => write!(
                f,
                "Expected closing parenthesis after 'if' statement condition but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterWhileCond(Some(token)) => write!(
                f,
                "Expected closing parenthesis after 'while' statement condition but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterWhileCond(None) => write!(
                f,
                "Expected closing parenthesis after 'while' statement condition but found end of input",
            ),
            ParseError::ExpectedSemicolonAfterForCond(Some(token)) => write!(
                f,
                "Expected semicolon after 'for' condition expression but found {}",
                token,
            ),
            ParseError::ExpectedSemicolonAfterForCond(None) => write!(
                f,
                "Expected semicolon after 'for' condition expression but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterForIncrement(Some(token)) => write!(
                f,
                "Expected closing parenthesis after 'for' increment expression but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterForIncrement(None) => write!(
                f,
                "Expected closing parenthesis after 'for' increment expression but found end of input",
            ),
            ParseError::ExpectedClosingParenAfterCall(Some(token)) => write!(
                f,
                "Expected closing parenthesis after function call but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterCall(None) => write!(
                f,
                "Expected closing parenthesis after function call but found end of input",
            ),
            ParseError::ExpectedPrimaryExpr(Some(token)) => {
                write!(f, "Expected primary expression but found token {}", token)
            }
            ParseError::ExpectedPrimaryExpr(None) => {
                write!(f, "Expected primary expression but found end of input")
            }
            ParseError::InvalidAssignmentTarget(expr) => {
                write!(f, "Expression {} is not a valid assignment target", expr)
            }
            ParseError::TooManyCallArguments(expr) => {
                write!(
                    f,
                    "Function call {} has too many arguments (max allowed is {})",
                    expr,
                    MAX_FUNCTION_ARGUMENTS,
                )
            }
            ParseError::TooManyFunParameters(ident) => {
                write!(
                    f,
                    "Function declaration {} has too many parameters (max allowed is {})",
                    ident,
                    MAX_FUNCTION_ARGUMENTS,
                )
            }
        }
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

pub fn parse(reporter: &mut Reporter, tokens: &[Token]) -> Option<Program> {
    let mut ctx = ParseCtx::new(tokens);
    let mut stmts = Vec::new();

    while ctx.has_more_tokens() {
        match parse_decl_stmt(&mut ctx) {
            Ok(stmt) => stmts.push(stmt),
            Err(err) => {
                reporter.report_compile_error(err.to_string());
                ctx.synchronize();
            }
        }
    }

    if reporter.has_compile_error() {
        None
    } else {
        Some(Program::new(stmts))
    }
}

struct ParseCtx<'a> {
    tokens: Peekable<slice::Iter<'a, Token>>,
}

impl<'a> ParseCtx<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Self {
            tokens: tokens.iter().peekable(),
        }
    }

    fn check_token(&mut self, token_value: &TokenValue) -> bool {
        if let Some(token) = self.tokens.peek() {
            token.value() == token_value
        } else {
            false
        }
    }

    fn read_token_if(&mut self, token_value: &TokenValue) -> Option<Token> {
        if self.check_token(token_value) {
            return self.read_token();
        }
        None
    }

    fn read_token_if_any_of(&mut self, token_values: &[TokenValue]) -> Option<Token> {
        for token_value in token_values {
            if self.check_token(token_value) {
                return self.read_token();
            }
        }

        None
    }

    fn read_token_if_ident(&mut self) -> Option<String> {
        if let Some(token) = self.tokens.peek() {
            match token.value() {
                TokenValue::Ident(ident) => {
                    self.read_token();
                    Some(ident.to_string())
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn read_token(&mut self) -> Option<Token> {
        self.tokens.next().cloned()
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.tokens.peek().copied()
    }

    fn has_more_tokens(&mut self) -> bool {
        self.tokens.peek().is_some()
    }

    pub fn synchronize(&mut self) {
        while let Some(token) = self.tokens.peek() {
            match token.value() {
                TokenValue::Semicolon => {
                    // Next token is semicolon, consume that and the next
                    // statement can be meaningful
                    self.tokens.next();
                    return;
                }
                TokenValue::Class
                | TokenValue::Fun
                | TokenValue::Var
                | TokenValue::For
                | TokenValue::If
                | TokenValue::While
                | TokenValue::Print
                | TokenValue::Return => {
                    // Next token is a keyword. What comes after can be meaningful.
                    return;
                }
                _ => (),
            }

            self.tokens.next();
        }
    }
}

fn parse_decl_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::Var).is_some() {
        finish_parse_var_decl_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::Fun).is_some() {
        finish_parse_fun_decl_stmt(ctx)
    } else {
        parse_stmt(ctx)
    }
}

fn finish_parse_var_decl_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if let Some(ident) = ctx.read_token_if_ident() {
        let initializer = if ctx.read_token_if(&TokenValue::Equal).is_some() {
            Some(parse_expr(ctx)?)
        } else {
            None
        };

        if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
            Ok(Stmt::VarDecl(VarDeclStmt::new(ident, initializer)))
        } else {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedSemicolonAfterVarDeclStmt(token))
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedIdentAfterVarKeyword(token))
    }
}

fn finish_parse_fun_decl_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if let Some(fun_ident) = ctx.read_token_if_ident() {
        if ctx.read_token_if(&TokenValue::LeftParen).is_none() {
            let token = ctx.peek_token().cloned();
            return Err(ParseError::ExpectedOpeningParenAfterFunIdent(token));
        }

        let mut parameters = Vec::new();
        if !ctx.check_token(&TokenValue::RightParen) {
            while {
                if parameters.len() >= MAX_FUNCTION_ARGUMENTS {
                    // TODO: this unnecessarily throws the parser into
                    // panic mode, find a way not to do that. Maybe have a
                    // separate valiation pass?
                    return Err(ParseError::TooManyFunParameters(fun_ident));
                }

                if let Some(ident) = ctx.read_token_if_ident() {
                    parameters.push(ident);
                } else {
                    let token = ctx.peek_token().cloned();
                    return Err(ParseError::ExpectedIdentInFunParameters(token));
                }

                ctx.read_token_if(&TokenValue::Comma).is_some()
            } { /*This is a do-while loop*/ }
        }

        if ctx.read_token_if(&TokenValue::RightParen).is_some() {
            if ctx.read_token_if(&TokenValue::LeftBrace).is_some() {
                let body = finish_parse_block_stmt_raw(ctx)?;
                Ok(Stmt::FunDecl(FunDeclStmt::new(fun_ident, parameters, body)))
            } else {
                let token = ctx.peek_token().cloned();
                Err(ParseError::ExpectedBlockAfterFunHeader(token))
            }
        } else {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedClosingParenAfterFunParameters(token))
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedIdentAfterFunKeyword(token))
    }
}

fn parse_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::If).is_some() {
        finish_parse_if_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::For).is_some() {
        finish_parse_for_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::While).is_some() {
        finish_parse_while_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::Print).is_some() {
        finish_parse_print_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::Return).is_some() {
        finish_parse_return_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::LeftBrace).is_some() {
        finish_parse_block_stmt(ctx)
    } else {
        parse_expr_stmt(ctx)
    }
}

fn finish_parse_if_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::LeftParen).is_some() {
        let cond = parse_expr(ctx)?;
        if ctx.read_token_if(&TokenValue::RightParen).is_some() {
            let then = parse_stmt(ctx)?;
            if ctx.read_token_if(&TokenValue::Else).is_some() {
                let else_ = parse_stmt(ctx)?;
                Ok(Stmt::If(IfStmt::with_else_branch(cond, then, else_)))
            } else {
                Ok(Stmt::If(IfStmt::new(cond, then)))
            }
        } else {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedClosingParenAfterIfCond(token))
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedOpeningParenAfterIf(token))
    }
}

fn finish_parse_for_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::LeftParen).is_some() {
        let initializer_stmt = if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
            None
        } else if ctx.read_token_if(&TokenValue::Var).is_some() {
            // This also consumes the semicolon
            Some(finish_parse_var_decl_stmt(ctx)?)
        } else {
            // This also consumes the semicolon
            Some(parse_expr_stmt(ctx)?)
        };

        let cond = if ctx.check_token(&TokenValue::Semicolon) {
            None
        } else {
            Some(parse_expr(ctx)?)
        };

        if ctx.read_token_if(&TokenValue::Semicolon).is_none() {
            let token = ctx.peek_token().cloned();
            return Err(ParseError::ExpectedSemicolonAfterForCond(token));
        }

        let increment_expr = if ctx.check_token(&TokenValue::RightParen) {
            None
        } else {
            let expr = parse_expr(ctx)?;
            Some(expr)
        };

        if ctx.read_token_if(&TokenValue::RightParen).is_none() {
            let token = ctx.peek_token().cloned();
            return Err(ParseError::ExpectedClosingParenAfterForIncrement(token));
        }

        let loop_ = parse_stmt(ctx)?;

        // Now synthetize the while loop:

        // If we have `increment_expr`, replace the original
        // `loop_` with a block also containing the
        // `increment_expr`

        let mut body = if let Some(increment_expr) = increment_expr {
            // TODO: can we affort to not wrap this in additional
            // block? Would there be a hygiene problem?
            Stmt::Block(BlockStmt::new(vec![
                loop_,
                Stmt::Expr(ExprStmt::new(increment_expr)),
            ]))
        } else {
            loop_
        };

        // Generate the while loop with `cond`, or `true` if no
        // condition given

        body = if let Some(cond) = cond {
            Stmt::While(WhileStmt::new(cond, body))
        } else {
            Stmt::While(WhileStmt::new(Expr::Lit(LitExpr::Boolean(true)), body))
        };

        // If we have `initializer_stmt`, generate a block around the
        // while loop, prepending the initializer

        body = if let Some(initializer_stmt) = initializer_stmt {
            Stmt::Block(BlockStmt::new(vec![initializer_stmt, body]))
        } else {
            body
        };

        Ok(body)
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedOpeningParenAfterFor(token))
    }
}

fn finish_parse_while_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::LeftParen).is_some() {
        let cond = parse_expr(ctx)?;
        if ctx.read_token_if(&TokenValue::RightParen).is_some() {
            let loop_ = parse_stmt(ctx)?;
            Ok(Stmt::While(WhileStmt::new(cond, loop_)))
        } else {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedClosingParenAfterWhileCond(token))
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedOpeningParenAfterWhile(token))
    }
}

fn finish_parse_print_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    let expr = parse_expr(ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Print(PrintStmt::new(expr)))
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedSemicolonAfterPrintStmt(token))
    }
}

fn finish_parse_return_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Return(ReturnStmt::new(None)))
    } else {
        let expr = parse_expr(ctx)?;
        if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
            Ok(Stmt::Return(ReturnStmt::new(Some(expr))))
        } else {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedSemicolonAfterReturnStmt(token))
        }
    }
}

fn finish_parse_block_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    finish_parse_block_stmt_raw(ctx).map(|stmts| Stmt::Block(BlockStmt::new(stmts)))
}

fn finish_parse_block_stmt_raw(ctx: &mut ParseCtx) -> ParseResult<Vec<Stmt>> {
    let mut stmts = Vec::new();

    while !ctx.check_token(&TokenValue::RightBrace) && ctx.has_more_tokens() {
        let stmt = parse_decl_stmt(ctx)?;
        stmts.push(stmt);
    }

    if ctx.read_token_if(&TokenValue::RightBrace).is_some() {
        Ok(stmts)
    } else {
        Err(ParseError::ExpectedClosingBraceAfterBlockStmt)
    }
}

fn parse_expr_stmt(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    let expr = parse_expr(ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Expr(ExprStmt::new(expr)))
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedSemicolonAfterExprStmt(token))
    }
}

fn parse_expr(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    parse_assignment(ctx)
}

fn parse_assignment(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let expr = parse_logic_or(ctx)?;
    if ctx.read_token_if(&TokenValue::Equal).is_some() {
        // Instead of looping through operands like elsewhere, we
        // recurse to `parse_assignment` to emulate
        // right-associativity
        let right = parse_assignment(ctx)?;

        if let Expr::Var(var) = expr {
            Ok(Expr::Assignment(AssignmentExpr::new(var, right)))
        } else {
            Err(ParseError::InvalidAssignmentTarget(expr))
        }
    } else {
        // No assignment token, fall through to other rules
        Ok(expr)
    }
}

fn parse_logic_or(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_logic_and(ctx)?;
    while ctx.read_token_if(&TokenValue::Or).is_some() {
        let right = parse_logic_and(ctx)?;
        expr = Expr::Logic(LogicExpr::new(expr, right, LogicOp::Or));
    }

    Ok(expr)
}

fn parse_logic_and(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_equality(ctx)?;
    while ctx.read_token_if(&TokenValue::And).is_some() {
        let right = parse_equality(ctx)?;
        expr = Expr::Logic(LogicExpr::new(expr, right, LogicOp::And));
    }

    Ok(expr)
}

fn parse_equality(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_comparison(ctx)?;
    while let Some(op_token) =
        ctx.read_token_if_any_of(&[TokenValue::BangEqual, TokenValue::EqualEqual])
    {
        let right = parse_comparison(ctx)?;
        let op = BinaryOp::try_from(op_token.clone()).expect("Token should be a binary op");
        expr = Expr::Binary(BinaryExpr::new(expr, right, op));
    }

    Ok(expr)
}

fn parse_comparison(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_addition(ctx)?;
    while let Some(op_token) = ctx.read_token_if_any_of(&[
        TokenValue::Less,
        TokenValue::LessEqual,
        TokenValue::Greater,
        TokenValue::GreaterEqual,
    ]) {
        let right = parse_addition(ctx)?;
        let op =
            BinaryOp::try_from(op_token.clone()).expect("Token should be a binary comparison op");
        expr = Expr::Binary(BinaryExpr::new(expr, right, op));
    }

    Ok(expr)
}

fn parse_addition(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_multiplication(ctx)?;
    while let Some(op_token) = ctx.read_token_if_any_of(&[TokenValue::Plus, TokenValue::Minus]) {
        let right = parse_multiplication(ctx)?;
        let op = BinaryOp::try_from(op_token.clone())
            .expect("Token should be a binary plus or minus op");
        expr = Expr::Binary(BinaryExpr::new(expr, right, op));
    }

    Ok(expr)
}

fn parse_multiplication(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_unary(ctx)?;
    while let Some(op_token) = ctx.read_token_if_any_of(&[TokenValue::Star, TokenValue::Slash]) {
        let right = parse_unary(ctx)?;
        let op = BinaryOp::try_from(op_token.clone())
            .expect("Token should be a binary multiply or divide op");
        expr = Expr::Binary(BinaryExpr::new(expr, right, op));
    }

    Ok(expr)
}

fn parse_unary(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    if let Some(op_token) = ctx.read_token_if_any_of(&[TokenValue::Bang, TokenValue::Minus]) {
        let expr = parse_unary(ctx)?;
        let op = UnaryOp::try_from(op_token.clone()).expect("Token should be a unary op");
        Ok(Expr::Unary(UnaryExpr::new(expr, op)))
    } else {
        parse_call(ctx)
    }
}

fn parse_call(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let mut expr = parse_primary(ctx)?;
    while ctx.read_token_if(&TokenValue::LeftParen).is_some() {
        expr = finish_parse_call(ctx, expr)?;
    }

    Ok(expr)
}

fn finish_parse_call(ctx: &mut ParseCtx, callee: Expr) -> ParseResult<Expr> {
    let mut arguments = Vec::new();
    if !ctx.check_token(&TokenValue::RightParen) {
        while {
            if arguments.len() >= MAX_FUNCTION_ARGUMENTS {
                // TODO: this unnecessarily throws the parser into
                // panic mode, find a way not to do that. Maybe have a
                // separate valiation pass?
                return Err(ParseError::TooManyCallArguments(callee));
            }
            let expr = parse_expr(ctx)?;
            arguments.push(expr);
            ctx.read_token_if(&TokenValue::Comma).is_some()
        } { /*This is a do-while loop*/ }
    }

    if ctx.read_token_if(&TokenValue::RightParen).is_some() {
        Ok(Expr::Call(CallExpr::new(callee, arguments)))
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedClosingParenAfterCall(token))
    }
}

fn parse_primary(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    if let Some(token) = ctx.read_token() {
        match token.value() {
            TokenValue::True => Ok(Expr::Lit(LitExpr::Boolean(true))),
            TokenValue::False => Ok(Expr::Lit(LitExpr::Boolean(false))),
            TokenValue::Nil => Ok(Expr::Lit(LitExpr::Nil)),
            TokenValue::Number(number) => Ok(Expr::Lit(LitExpr::Number(*number))),
            TokenValue::String(string) => Ok(Expr::Lit(LitExpr::String(string.clone()))),
            // TODO: intern ident
            TokenValue::Ident(ident) => Ok(Expr::Var(VarExpr::new(ident.clone()))),
            TokenValue::LeftParen => {
                let expr = parse_expr(ctx)?;
                if ctx.read_token_if(&TokenValue::RightParen).is_some() {
                    Ok(Expr::Group(GroupExpr::new(expr)))
                } else {
                    Err(ParseError::ExpectedClosingParenAfterGroupExpr(
                        ctx.peek_token().cloned(),
                    ))
                }
            }
            _ => Err(ParseError::ExpectedPrimaryExpr(Some(token))),
        }
    } else {
        Err(ParseError::ExpectedPrimaryExpr(None))
    }
}

const MAX_FUNCTION_ARGUMENTS: usize = 32;
