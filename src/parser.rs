use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::slice;

use crate::lexer::{Token, TokenValue};
use crate::reporter::Reporter;

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Literal(LiteralExpression),
    Grouping(GroupingExpression),
    Unary(UnaryExpression),
    Binary(BinaryExpression),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Expression::Literal(literal) => literal.to_string(),
                Expression::Grouping(grouping) => grouping.to_string(),
                Expression::Unary(unary) => unary.to_string(),
                Expression::Binary(binary) => binary.to_string(),
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpression {
    Number(f64),
    String(String),
    Boolean(bool),
    Nil,
}

impl fmt::Display for LiteralExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                LiteralExpression::Number(number) => number.to_string(),
                LiteralExpression::String(string) => format!("\"{}\"", string),
                LiteralExpression::Boolean(boolean) => boolean.to_string(),
                LiteralExpression::Nil => "nil".to_string(),
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GroupingExpression {
    expression: Box<Expression>,
}

impl GroupingExpression {
    pub fn new(expression: Expression) -> Self {
        Self {
            expression: Box::new(expression),
        }
    }

    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

impl fmt::Display for GroupingExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(group {})", self.expression)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpression {
    expression: Box<Expression>,
    operator: UnaryOperator,
}

impl UnaryExpression {
    pub fn new(expression: Expression, operator: UnaryOperator) -> Self {
        Self {
            expression: Box::new(expression),
            operator,
        }
    }

    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    pub fn operator(&self) -> UnaryOperator {
        self.operator
    }
}

impl fmt::Display for UnaryExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.operator, self.expression)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpression {
    left_expression: Box<Expression>,
    right_expression: Box<Expression>,
    operator: BinaryOperator,
}

impl BinaryExpression {
    pub fn new(left: Expression, right: Expression, operator: BinaryOperator) -> Self {
        Self {
            left_expression: Box::new(left),
            right_expression: Box::new(right),
            operator,
        }
    }

    pub fn left_expression(&self) -> &Expression {
        &self.left_expression
    }

    pub fn right_expression(&self) -> &Expression {
        &self.right_expression
    }

    pub fn operator(&self) -> BinaryOperator {
        self.operator
    }
}

impl fmt::Display for BinaryExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.operator, self.left_expression, self.right_expression
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
                BinaryOperator::Equal => "=",
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

/*

We express operator precedence in production rules. Equality has the
weakest precedence, unary operators have the strongest.

expression     → equality ;
equality       → comparison ( ( "!=" | "==" ) comparison )* ;
comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
multiplication → unary ( ( "/" | "*" ) unary )* ;
unary          → ( "!" | "-" ) unary
               | primary ;
primary        → NUMBER | STRING | "false" | "true" | "nil"
               | "(" expression ")" ;

*/

pub struct ParseError;

pub fn parse(reporter: &mut Reporter, tokens: &[Token]) -> Option<Expression> {
    let mut ctx = ParserCtx::new(tokens);
    parse_expression(reporter, &mut ctx).ok()
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

    fn match_tokens(&mut self, token_values: &[TokenValue]) -> Option<Token> {
        for token_value in token_values {
            if self.check_token(token_value) {
                return self.read_token();
            }
        }

        None
    }

    fn check_token(&mut self, token_value: &TokenValue) -> bool {
        if let Some(token) = self.peek_token() {
            token.value() == token_value
        } else {
            false
        }
    }

    fn read_token(&mut self) -> Option<Token> {
        self.tokens.next().cloned()
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.tokens.peek().copied()
    }

    fn consume(
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
            reporter.report_on_line(error_message, token.line());
        } else {
            // TODO: report correct span, maybe add back the EOF token
            reporter.report(error_message);
        }

        false
    }
}

fn parse_expression(
    reporter: &mut Reporter,
    ctx: &mut ParserCtx,
) -> Result<Expression, ParseError> {
    /*
    expression     → equality ;
     */

    parse_equality(reporter, ctx)
}

fn parse_equality(reporter: &mut Reporter, ctx: &mut ParserCtx) -> Result<Expression, ParseError> {
    /*
    equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    */

    let mut expr = parse_comparison(reporter, ctx)?;
    while let Some(operator_token) =
        ctx.match_tokens(&[TokenValue::BangEqual, TokenValue::EqualEqual])
    {
        let right_expr = parse_comparison(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expression::Binary(BinaryExpression::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_comparison(
    reporter: &mut Reporter,
    ctx: &mut ParserCtx,
) -> Result<Expression, ParseError> {
    /*
    comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
    */

    let mut expr = parse_addition(reporter, ctx)?;
    while let Some(operator_token) = ctx.match_tokens(&[
        TokenValue::Less,
        TokenValue::LessEqual,
        TokenValue::Greater,
        TokenValue::GreaterEqual,
    ]) {
        let right_expr = parse_addition(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expression::Binary(BinaryExpression::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_addition(reporter: &mut Reporter, ctx: &mut ParserCtx) -> Result<Expression, ParseError> {
    /*
    addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
    */

    let mut expr = parse_multiplication(reporter, ctx)?;
    while let Some(operator_token) = ctx.match_tokens(&[TokenValue::Plus, TokenValue::Minus]) {
        let right_expr = parse_multiplication(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expression::Binary(BinaryExpression::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_multiplication(
    reporter: &mut Reporter,
    ctx: &mut ParserCtx,
) -> Result<Expression, ParseError> {
    /*
    multiplication → unary ( ( "/" | "*" ) unary )* ;
    */

    let mut expr = parse_unary(reporter, ctx)?;
    while let Some(operator_token) = ctx.match_tokens(&[TokenValue::Star, TokenValue::Slash]) {
        let right_expr = parse_unary(reporter, ctx)?;
        let operator = BinaryOperator::try_from(operator_token.clone())
            .expect("Token should be a binary operator");
        expr = Expression::Binary(BinaryExpression::new(expr, right_expr, operator));
    }

    Ok(expr)
}

fn parse_unary(reporter: &mut Reporter, ctx: &mut ParserCtx) -> Result<Expression, ParseError> {
    /*
    unary          → ( "!" | "-" ) unary
                   | primary ;
    */

    if let Some(operator_token) = ctx.match_tokens(&[TokenValue::Bang, TokenValue::Minus]) {
        let expr = parse_unary(reporter, ctx)?;
        let operator = UnaryOperator::try_from(operator_token.clone())
            .expect("Token should be a unary operator");
        Ok(Expression::Unary(UnaryExpression::new(expr, operator)))
    } else {
        parse_primary(reporter, ctx)
    }
}

fn parse_primary(reporter: &mut Reporter, ctx: &mut ParserCtx) -> Result<Expression, ParseError> {
    /*
    primary        → NUMBER | STRING | "false" | "true" | "nil"
                   | "(" expression ")" ;
    */

    if let Some(token) = ctx.read_token() {
        match token.value() {
            TokenValue::True => Ok(Expression::Literal(LiteralExpression::Boolean(true))),
            TokenValue::False => Ok(Expression::Literal(LiteralExpression::Boolean(false))),
            TokenValue::Nil => Ok(Expression::Literal(LiteralExpression::Nil)),
            TokenValue::Number(number) => {
                Ok(Expression::Literal(LiteralExpression::Number(*number)))
            }
            TokenValue::String(string) => Ok(Expression::Literal(LiteralExpression::String(
                string.clone(),
            ))),
            TokenValue::LeftParen => {
                let expr = parse_expression(reporter, ctx)?;
                let success = ctx.consume(
                    reporter,
                    &TokenValue::RightParen,
                    "Expected ')' after expression",
                );
                if success {
                    Ok(Expression::Grouping(GroupingExpression::new(expr)))
                } else {
                    Err(ParseError)
                }
            }
            _ => {
                reporter.report_on_line("Expected expression", token.line());
                Err(ParseError)
            }
        }
    } else {
        reporter.report("Expected expression");
        Err(ParseError)
    }
}
