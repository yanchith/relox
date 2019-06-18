use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::slice;

use crate::lexer::{Token, TokenValue};
use crate::reporter::Reporter;

/*

GRAMMAR

program   → declaration* EOF ;

We express "statement precedence" in production rules. Declaration
stmts are not allowed everywhere other stmts are, so we have
to give them lower precedence, specifying them earlier in the
production rules.

declaration → varDecl
            | statement ;

statement → exprStmt
          | printStmt ;

exprStmt  → expr ";" ;
printStmt → "print" expr ";" ;

We express operator precedence in production rules. Equality has the
weakest precedence, unary operators have the strongest.

expr     → equality ;
equality       → comparison ( ( "!=" | "==" ) comparison )* ;
comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
multiplication → unary ( ( "/" | "*" ) unary )* ;
unary          → ( "!" | "-" ) unary
               | primary ;
primary        → NUMBER | STRING | "false" | "true" | "nil"
               | "(" expr ")" ;

 */

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
        let mut first = true;
        for stmt in &self.stmts {
            if !first {
                writeln!(f)?;
            }
            first = false;
            write!(f, "{} ", stmt)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Expr(ExprStmt),
    Print(PrintStmt),
    VarDecl(VarDeclStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Expr(expr) => write!(f, "{}", expr),
            Stmt::Print(print) => write!(f, "{}", print),
            Stmt::VarDecl(decl) => write!(f, "{}", decl),
        }
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
pub struct VarDeclStmt {
    ident: String, // TODO: not string, plz
    initializer_expr: Option<Expr>,
}

impl VarDeclStmt {
    pub fn new(ident: String, initializer_expr: Option<Expr>) -> Self {
        Self {
            ident,
            initializer_expr,
        }
    }

    pub fn ident(&self) -> &str {
        &self.ident
    }

    pub fn initializer_expr(&self) -> Option<&Expr> {
        self.initializer_expr.as_ref()
    }
}

impl fmt::Display for VarDeclStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.initializer_expr {
            Some(expr) => write!(f, "(decl {} {})", self.ident, expr),
            None => write!(f, "(decl {})", self.ident),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Lit(LitExpr),
    Group(GroupExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Var(VarExpr),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Lit(lit) => write!(f, "{}", lit),
            Expr::Group(group) => write!(f, "{}", group),
            Expr::Unary(unary) => write!(f, "{}", unary),
            Expr::Binary(binary) => write!(f, "{}", binary),
            Expr::Var(var) => write!(f, "{}", var),
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
    operator: UnaryOperator,
}

impl UnaryExpr {
    pub fn new(expr: Expr, operator: UnaryOperator) -> Self {
        Self {
            expr: Box::new(expr),
            operator,
        }
    }

    pub fn expr(&self) -> &Expr {
        &self.expr
    }

    pub fn operator(&self) -> UnaryOperator {
        self.operator
    }
}

impl fmt::Display for UnaryExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.operator, self.expr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    left_expr: Box<Expr>,
    right_expr: Box<Expr>,
    operator: BinaryOperator,
}

impl BinaryExpr {
    pub fn new(left: Expr, right: Expr, operator: BinaryOperator) -> Self {
        Self {
            left_expr: Box::new(left),
            right_expr: Box::new(right),
            operator,
        }
    }

    pub fn left_expr(&self) -> &Expr {
        &self.left_expr
    }

    pub fn right_expr(&self) -> &Expr {
        &self.right_expr
    }

    pub fn operator(&self) -> BinaryOperator {
        self.operator
    }
}

impl fmt::Display for BinaryExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.operator, self.left_expr, self.right_expr
        )
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Not,
    Minus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryOperatorFromTokenError;

impl TryFrom<Token> for UnaryOperator {
    type Error = UnaryOperatorFromTokenError;

    fn try_from(token: Token) -> Result<UnaryOperator, Self::Error> {
        match token.value() {
            TokenValue::Bang => Ok(UnaryOperator::Not),
            TokenValue::Minus => Ok(UnaryOperator::Minus),
            _ => Err(UnaryOperatorFromTokenError),
        }
    }
}

impl fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                UnaryOperator::Not => "!",
                UnaryOperator::Minus => "-",
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryOperatorFromTokenError;

impl TryFrom<Token> for BinaryOperator {
    type Error = BinaryOperatorFromTokenError;

    fn try_from(token: Token) -> Result<BinaryOperator, Self::Error> {
        match token.value() {
            TokenValue::EqualEqual => Ok(BinaryOperator::Equal),
            TokenValue::BangEqual => Ok(BinaryOperator::NotEqual),
            TokenValue::Less => Ok(BinaryOperator::Less),
            TokenValue::LessEqual => Ok(BinaryOperator::LessEqual),
            TokenValue::Greater => Ok(BinaryOperator::Greater),
            TokenValue::GreaterEqual => Ok(BinaryOperator::GreaterEqual),
            TokenValue::Plus => Ok(BinaryOperator::Plus),
            TokenValue::Minus => Ok(BinaryOperator::Minus),
            TokenValue::Star => Ok(BinaryOperator::Multiply),
            TokenValue::Slash => Ok(BinaryOperator::Divide),
            _ => Err(BinaryOperatorFromTokenError),
        }
    }
}

impl fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinaryOperator::Equal => "==",
                BinaryOperator::NotEqual => "!=",
                BinaryOperator::Less => "<",
                BinaryOperator::LessEqual => "<=",
                BinaryOperator::Greater => ">",
                BinaryOperator::GreaterEqual => ">=",
                BinaryOperator::Plus => "+",
                BinaryOperator::Minus => "-",
                BinaryOperator::Multiply => "*",
                BinaryOperator::Divide => "/",
            }
        )
    }
}

pub struct ParseError;

pub type ParseResult<T> = Result<T, ParseError>;

pub fn parse(reporter: &mut Reporter, tokens: &[Token]) -> Option<Program> {
    let mut ctx = ParserCtx::new(tokens);

    let mut stmts = Vec::new();
    while ctx.has_more_tokens() {
        match parse_decl(reporter, &mut ctx) {
            Ok(stmt) => stmts.push(stmt),
            Err(_) => {
                return None;
            }
        }
    }

    Some(Program::new(stmts))
}

struct ParserCtx<'a> {
    tokens: Peekable<slice::Iter<'a, Token>>,
}

impl<'a> ParserCtx<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Self {
            tokens: tokens.iter().peekable(),
        }
    }

    fn check_token(&mut self, token_value: &TokenValue) -> bool {
        if let Some(token) = self.peek_token() {
            token.value() == token_value
        } else {
            false
        }
    }

    fn check_token_ident(&mut self) -> bool {
        if let Some(token) = self.peek_token() {
            if let TokenValue::Ident(_) = token.value() {
                true
            } else {
                false
            }
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

    fn read_token_if_ident(&mut self) -> Option<Token> {
        if self.check_token_ident() {
            self.read_token()
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
}

fn parse_decl(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    declaration → varDecl
                | statement ;
    */

    // TODO: synchronize on statements
    if ctx.read_token_if(&TokenValue::Var).is_some() {
        finish_parse_var_decl(reporter, ctx)
    } else {
        parse_stmt(reporter, ctx)
    }
}

fn finish_parse_var_decl(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    if let Some(ident_token) = ctx.read_token_if_ident() {
        let mut initializer_expr = None;

        if ctx.read_token_if(&TokenValue::Equal).is_some() {
            initializer_expr = Some(parse_expr(reporter, ctx)?);
        }

        if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
            match ident_token.value() {
                TokenValue::Ident(ident) => Ok(Stmt::VarDecl(VarDeclStmt::new(
                    ident.to_string(),
                    initializer_expr,
                ))),
                _ => unreachable!(),
            }
        } else {
            // TODO: won't this hurt synchronization?
            report_token(
                reporter,
                ctx.read_token(),
                "Expected a ; after variable declarationr",
            );
            Err(ParseError)
        }
    } else {
        // TODO: won't this hurt synchronization?
        report_token(reporter, ctx.read_token(), "Expected variable identifier");
        Err(ParseError)
    }
}

fn parse_stmt(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    statement → exprStmt
              | printStmt ;
    */
    if ctx.read_token_if(&TokenValue::Print).is_some() {
        finish_parse_print_stmt(reporter, ctx)
    } else {
        parse_expr_stmt(reporter, ctx)
    }
}

fn finish_parse_print_stmt(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    printStmt → "print" expr ";" ;
    */
    let expr = parse_expr(reporter, ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Print(PrintStmt::new(expr)))
    } else {
        report_token(
            reporter,
            // TODO: won't this hurt synchronization?
            ctx.read_token(),
            "Expected a ; after print statement",
        );
        Err(ParseError)
    }
}

fn parse_expr_stmt(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    exprStmt  → expr ";" ;
    */
    let expr = parse_expr(reporter, ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Expr(ExprStmt::new(expr)))
    } else {
        report_token(
            reporter,
            // TODO: won't this hurt synchronization?
            ctx.read_token(),
            "Expectex a ; after expression stmt",
        );
        Err(ParseError)
    }
}

fn parse_expr(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    expr     → equality ;
    */

    parse_equality(reporter, ctx)
}

fn parse_equality(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    */

    let mut expr = parse_comparison(reporter, ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::BangEqual, TokenValue::EqualEqual])
    {
        let right_expr = parse_comparison(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_comparison(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
    */

    let mut expr = parse_addition(reporter, ctx)?;
    while let Some(operator_token) = ctx.read_token_if_any_of(&[
        TokenValue::Less,
        TokenValue::LessEqual,
        TokenValue::Greater,
        TokenValue::GreaterEqual,
    ]) {
        let right_expr = parse_addition(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary comparison operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_addition(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
    */

    let mut expr = parse_multiplication(reporter, ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::Plus, TokenValue::Minus])
    {
        let right_expr = parse_multiplication(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary plus or minus operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_multiplication(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    multiplication → unary ( ( "/" | "*" ) unary )* ;
    */

    let mut expr = parse_unary(reporter, ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::Star, TokenValue::Slash])
    {
        let right_expr = parse_unary(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary multiply or divide operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_unary(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    unary          → ( "!" | "-" ) unary
                   | primary ;
    */

    if let Some(operator_token) = ctx.read_token_if_any_of(&[TokenValue::Bang, TokenValue::Minus]) {
        let expr = parse_unary(reporter, ctx)?;
        let operator = UnaryOperator::try_from(operator_token.clone())
            .expect("Token should be a unary operator");
        Ok(Expr::Unary(UnaryExpr::new(expr, operator)))
    } else {
        parse_primary(reporter, ctx)
    }
}

fn parse_primary(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    primary        → NUMBER | STRING | "false" | "true" | "nil"
                   | "(" expr ")" ;
    */

    if let Some(token) = ctx.read_token() {
        match token.value() {
            TokenValue::True => Ok(Expr::Lit(LitExpr::Boolean(true))),
            TokenValue::False => Ok(Expr::Lit(LitExpr::Boolean(false))),
            TokenValue::Nil => Ok(Expr::Lit(LitExpr::Nil)),
            TokenValue::Number(number) => Ok(Expr::Lit(LitExpr::Number(*number))),
            TokenValue::String(string) => Ok(Expr::Lit(LitExpr::String(string.clone()))),
            // TODO: less string cloning, more string interning
            TokenValue::Ident(ident) => Ok(Expr::Var(VarExpr::new(ident.clone()))),
            TokenValue::LeftParen => {
                let expr = parse_expr(reporter, ctx)?;
                if ctx.read_token_if(&TokenValue::RightParen).is_some() {
                    Ok(Expr::Group(GroupExpr::new(expr)))
                } else {
                    report_token(
                        reporter,
                        // TODO: won't this hurt synchronization?
                        ctx.read_token(),
                        "Expected a ')' after expression",
                    );
                    Err(ParseError)
                }
            }
            _ => {
                reporter.report_compile_error_on_span("Expected expr", token.span());
                Err(ParseError)
            }
        }
    } else {
        reporter.report_compile_error("Expected expr");
        Err(ParseError)
    }
}

fn report_token(reporter: &mut Reporter, maybe_token: Option<Token>, message: &str) {
    match maybe_token {
        Some(token) => reporter.report_compile_error_on_span(message, token.span()),
        None => reporter.report_compile_error(message),
    }
}
