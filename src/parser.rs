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
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Stmt::Expr(expr) => expr.to_string(),
                Stmt::Print(print) => print.to_string(),
            }
        )
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
        write!(f, "(stmt {})", self.expr)
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
pub enum Expr {
    Lit(LitExpr),
    Group(GroupExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Expr::Lit(lit) => lit.to_string(),
                Expr::Group(group) => group.to_string(),
                Expr::Unary(unary) => unary.to_string(),
                Expr::Binary(binary) => binary.to_string(),
            }
        )
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
        write!(
            f,
            "{}",
            match self {
                LitExpr::Number(number) => number.to_string(),
                LitExpr::String(string) => format!("\"{}\"", string),
                LitExpr::Boolean(boolean) => boolean.to_string(),
                LitExpr::Nil => "nil".to_string(),
            }
        )
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
        match parse_stmt(reporter, &mut ctx) {
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

    fn read_tokens(&mut self, token_values: &[TokenValue]) -> Option<Token> {
        for token_value in token_values {
            if self.check_token(token_value) {
                return self.read_token();
            }
        }

        None
    }

    fn read_token(&mut self) -> Option<Token> {
        self.tokens.next().cloned()
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.tokens.peek().copied()
    }

    fn check_and_skip_token(
        &mut self,
        reporter: &mut Reporter,
        token_value: &TokenValue,
        error_message: &str,
    ) -> bool {
        if self.check_token(token_value) {
            self.read_token();
            return true;
        }

        if let Some(token) = self.peek_token() {
            reporter.report_compile_error_on_line(error_message, token.line());
        } else {
            // TODO: report correct span, maybe add back the EOF token
            reporter.report_compile_error(error_message);
        }

        false
    }

    fn has_more_tokens(&mut self) -> bool {
        self.tokens.peek().is_some()
    }
}

fn parse_stmt(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    statement → exprStmt
              | printStmt ;
    */
    if ctx.read_tokens(&[TokenValue::Print]).is_some() {
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
    ctx.check_and_skip_token(
        reporter,
        &TokenValue::Semicolon,
        "Expected a ; after a print statement",
    );

    Ok(Stmt::Print(PrintStmt::new(expr)))
}

fn parse_expr_stmt(reporter: &mut Reporter, ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    exprStmt  → expr ";" ;
    */
    let expr = parse_expr(reporter, ctx)?;
    let success = ctx.check_and_skip_token(
        reporter,
        &TokenValue::Semicolon,
        "Expected a ; after a expr statement",
    );

    if success {
        Ok(Stmt::Expr(ExprStmt::new(expr)))
    } else {
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
        ctx.read_tokens(&[TokenValue::BangEqual, TokenValue::EqualEqual])
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
    while let Some(operator_token) = ctx.read_tokens(&[
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
    while let Some(operator_token) = ctx.read_tokens(&[TokenValue::Plus, TokenValue::Minus]) {
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
    while let Some(operator_token) = ctx.read_tokens(&[TokenValue::Star, TokenValue::Slash]) {
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

    if let Some(operator_token) = ctx.read_tokens(&[TokenValue::Bang, TokenValue::Minus]) {
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
            TokenValue::LeftParen => {
                let expr = parse_expr(reporter, ctx)?;
                let success = ctx.check_and_skip_token(
                    reporter,
                    &TokenValue::RightParen,
                    "Expected ')' after expr",
                );
                if success {
                    Ok(Expr::Group(GroupExpr::new(expr)))
                } else {
                    Err(ParseError)
                }
            }
            _ => {
                reporter.report_compile_error_on_line("Expected expr", token.line());
                Err(ParseError)
            }
        }
    } else {
        reporter.report_compile_error("Expected expr");
        Err(ParseError)
    }
}
