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
          | ifStmt
          | printStmt
          | block ;

exprStmt  → expr ";" ;
ifStmt    → "if" "(" expression ")" statement ( "else" statement )? ;
printStmt → "print" expr ";" ;
block     → "{" declaration* "}" ;

We express operator precedence in production rules. Equality has the
weakest precedence, unary operators have the strongest.

expression     → assignment ;
assignment     → IDENTIFIER "=" assignment
               | equality ;

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
        f.write_str("(program ")?;

        let mut first = true;
        for stmt in &self.stmts {
            if !first {
                f.write_str(" ")?;
            }
            f.write_str(&stmt.to_string())?;
            first = false;
        }

        f.write_str(")")?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Expr(ExprStmt),
    If(IfStmt),
    Print(PrintStmt),
    VarDecl(VarDeclStmt),
    Block(BlockStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Expr(expr) => write!(f, "{}", expr),
            Stmt::If(if_) => write!(f, "{}", if_),
            Stmt::Print(print) => write!(f, "{}", print),
            Stmt::VarDecl(decl) => write!(f, "{}", decl),
            Stmt::Block(block) => write!(f, "{}", block),
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
pub struct IfStmt {
    cond_expr: Expr,
    then_stmt: Box<Stmt>,
    else_stmt: Option<Box<Stmt>>,
}

impl IfStmt {
    pub fn new(cond_expr: Expr, then_stmt: Stmt) -> Self {
        Self {
            cond_expr,
            then_stmt: Box::new(then_stmt),
            else_stmt: None,
        }
    }

    pub fn with_else_branch(cond_expr: Expr, then_stmt: Stmt, else_stmt: Stmt) -> Self {
        Self {
            cond_expr,
            then_stmt: Box::new(then_stmt),
            else_stmt: Some(Box::new(else_stmt)),
        }
    }

    pub fn cond_expr(&self) -> &Expr {
        &self.cond_expr
    }

    pub fn then_stmt(&self) -> &Stmt {
        &self.then_stmt
    }

    pub fn else_stmt(&self) -> Option<&Stmt> {
        match &self.else_stmt {
            Some(else_stmt) => Some(&else_stmt),
            None => None,
        }
    }
}

impl fmt::Display for IfStmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.else_stmt {
            Some(else_stmt) => write!(
                f,
                "(if {} {} {})",
                self.cond_expr, self.then_stmt, else_stmt,
            ),
            None => write!(f, "(if {} {})", self.cond_expr, self.then_stmt),
        }
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
    ident: String, // TODO: intern idents
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
        f.write_str("(block ")?;

        let mut first = true;
        for stmt in &self.stmts {
            if !first {
                f.write_str(" ")?;
            }
            f.write_str(&stmt.to_string())?;
            first = false;
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
    Var(VarExpr),
    Assignment(AssignmentExpr),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Lit(lit) => write!(f, "{}", lit),
            Expr::Group(group) => write!(f, "{}", group),
            Expr::Unary(unary) => write!(f, "{}", unary),
            Expr::Binary(binary) => write!(f, "{}", binary),
            Expr::Var(var) => write!(f, "{}", var),
            Expr::Assignment(assignment) => write!(f, "{}", assignment),
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

// TODO: implement std::error:Error
#[derive(Debug)]
pub enum ParseError {
    ExpectedSemicolonAfterExprStmt(Option<Token>),
    ExpectedSemicolonAfterPrintStmt(Option<Token>),
    ExpectedSemicolonAfterVarDeclStmt(Option<Token>),
    ExpectedIdentAfterVarKeyword(Option<Token>),
    ExpectedClosingParenAfterGroupExpr(Option<Token>),
    ExpectedClosingBraceAfterBlockStmt,
    ExpectedOpeningParenAfterIf(Option<Token>),
    ExpectedClosingParenAfterIfCond(Option<Token>),
    ExpectedPrimaryExpr(Option<Token>),
    InvalidAssignmentTarget(Expr),
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
            ParseError::ExpectedClosingParenAfterIfCond(Some(token)) => write!(
                f,
                "Expected closing parenthesis after 'if' statement condition but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterIfCond(None) => write!(
                f,
                "Expected closing parenthesis after 'if' statement condition but found end of input",
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
        }
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

pub fn parse(reporter: &mut Reporter, tokens: &[Token]) -> Option<Program> {
    let mut ctx = ParserCtx::new(tokens);
    let mut stmts = Vec::new();

    while ctx.has_more_tokens() {
        match parse_decl(&mut ctx) {
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

fn parse_decl(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    declaration → varDecl
                | statement ;
    */

    if ctx.read_token_if(&TokenValue::Var).is_some() {
        finish_parse_var_decl(ctx)
    } else {
        parse_stmt(ctx)
    }
}

fn finish_parse_var_decl(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    if let Some(ident_token) = ctx.read_token_if_ident() {
        let initializer_expr = if ctx.read_token_if(&TokenValue::Equal).is_some() {
            Some(parse_expr(ctx)?)
        } else {
            None
        };

        if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
            match ident_token.value() {
                TokenValue::Ident(ident) => Ok(Stmt::VarDecl(VarDeclStmt::new(
                    ident.to_string(),
                    initializer_expr,
                ))),
                _ => unreachable!(),
            }
        } else {
            Err(ParseError::ExpectedSemicolonAfterVarDeclStmt(
                ctx.peek_token().cloned(),
            ))
        }
    } else {
        Err(ParseError::ExpectedIdentAfterVarKeyword(
            ctx.peek_token().cloned(),
        ))
    }
}

fn parse_stmt(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    statement → exprStmt
              | ifStmt
              | printStmt
              | block ;
     */
    if ctx.read_token_if(&TokenValue::If).is_some() {
        finish_parse_if_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::Print).is_some() {
        finish_parse_print_stmt(ctx)
    } else if ctx.read_token_if(&TokenValue::LeftBrace).is_some() {
        finish_parse_block_stmt(ctx)
    } else {
        parse_expr_stmt(ctx)
    }
}

fn finish_parse_if_stmt(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    ifStmt    → "if" "(" expression ")" statement ( "else" statement )? ;
    */
    if ctx.read_token_if(&TokenValue::LeftParen).is_some() {
        let cond_expr = parse_expr(ctx)?;
        if ctx.read_token_if(&TokenValue::RightParen).is_some() {
            let then_stmt = parse_stmt(ctx)?;
            if ctx.read_token_if(&TokenValue::Else).is_some() {
                let else_stmt = parse_stmt(ctx)?;
                Ok(Stmt::If(IfStmt::with_else_branch(
                    cond_expr,
                    then_stmt,
                    else_stmt,
                )))
            } else {
                Ok(Stmt::If(IfStmt::new(cond_expr, then_stmt)))
            }
        } else {
            Err(ParseError::ExpectedClosingParenAfterIfCond(
                ctx.peek_token().cloned(),
            ))
        }
    } else {
        Err(ParseError::ExpectedOpeningParenAfterIf(
            ctx.peek_token().cloned(),
        ))
    }
}

fn finish_parse_print_stmt(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    printStmt → "print" expr ";" ;
    */
    let expr = parse_expr(ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Print(PrintStmt::new(expr)))
    } else {
        Err(ParseError::ExpectedSemicolonAfterPrintStmt(
            ctx.peek_token().cloned(),
        ))
    }
}

fn finish_parse_block_stmt(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    block     → "{" declaration* "}" ;
     */
    let mut stmts = Vec::new();

    while !ctx.check_token(&TokenValue::RightBrace) && ctx.has_more_tokens() {
        let stmt = parse_decl(ctx)?;
        stmts.push(stmt);
    }

    if ctx.read_token_if(&TokenValue::RightBrace).is_some() {
        Ok(Stmt::Block(BlockStmt::new(stmts)))
    } else {
        Err(ParseError::ExpectedClosingBraceAfterBlockStmt)
    }
}

fn parse_expr_stmt(ctx: &mut ParserCtx) -> ParseResult<Stmt> {
    /*
    exprStmt  → expr ";" ;
    */
    let expr = parse_expr(ctx)?;
    if ctx.read_token_if(&TokenValue::Semicolon).is_some() {
        Ok(Stmt::Expr(ExprStmt::new(expr)))
    } else {
        Err(ParseError::ExpectedSemicolonAfterExprStmt(
            ctx.peek_token().cloned(),
        ))
    }
}

fn parse_expr(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    expression → assignment ;
    */

    parse_assignment(ctx)
}

fn parse_assignment(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    assignment → IDENTIFIER "=" assignment
               | equality ;
     */

    let expr = parse_equality(ctx)?;
    if ctx.read_token_if(&TokenValue::Equal).is_some() {
        // Instead of looping through operands like elsewhere, we
        // recurse to `parse_assignment` to emulate
        // right-associativity
        let right_expr = parse_assignment(ctx)?;

        if let Expr::Var(var) = expr {
            Ok(Expr::Assignment(AssignmentExpr::new(var, right_expr)))
        } else {
            Err(ParseError::InvalidAssignmentTarget(expr))
        }
    } else {
        // No assignment token, fall through to other rules
        Ok(expr)
    }
}

fn parse_equality(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    */

    let mut expr = parse_comparison(ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::BangEqual, TokenValue::EqualEqual])
    {
        let right_expr = parse_comparison(ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_comparison(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
    */

    let mut expr = parse_addition(ctx)?;
    while let Some(operator_token) = ctx.read_token_if_any_of(&[
        TokenValue::Less,
        TokenValue::LessEqual,
        TokenValue::Greater,
        TokenValue::GreaterEqual,
    ]) {
        let right_expr = parse_addition(ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary comparison operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_addition(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
    */

    let mut expr = parse_multiplication(ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::Plus, TokenValue::Minus])
    {
        let right_expr = parse_multiplication(ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary plus or minus operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_multiplication(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    multiplication → unary ( ( "/" | "*" ) unary )* ;
    */

    let mut expr = parse_unary(ctx)?;
    while let Some(operator_token) =
        ctx.read_token_if_any_of(&[TokenValue::Star, TokenValue::Slash])
    {
        let right_expr = parse_unary(ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary multiply or divide operator");
        expr = Expr::Binary(BinaryExpr::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_unary(ctx: &mut ParserCtx) -> ParseResult<Expr> {
    /*
    unary          → ( "!" | "-" ) unary
                   | primary ;
    */

    if let Some(operator_token) = ctx.read_token_if_any_of(&[TokenValue::Bang, TokenValue::Minus]) {
        let expr = parse_unary(ctx)?;
        let operator = UnaryOperator::try_from(operator_token.clone())
            .expect("Token should be a unary operator");
        Ok(Expr::Unary(UnaryExpr::new(expr, operator)))
    } else {
        parse_primary(ctx)
    }
}

fn parse_primary(ctx: &mut ParserCtx) -> ParseResult<Expr> {
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
