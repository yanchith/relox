//! The parser.
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
//! declaration → varDecl
//!             → funDecl
//!             → classDecl
//!             | statement ;
//!
//! funDecl     → "fun" function ;
//! classDecl   → "class" IDENTIFIER "{" function* "}" ;
//! function    → IDENTIFIER "(" params? ")" block ;
//! params      → IDENTIFIER ( "," IDENTIFIER )* ;
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
//! forStmt   → "for" "(" ( varDecl | exprStmt | ";" )
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
//! expression     → assign ;
//! assign         → ( call "." )? IDENTIFIER "=" assignment
//!                | logic_or;
//! logic_or       → logic_and ( "or" logic_and )* ;
//! logic_and      → equality ( "and" equality )* ;
//!
//! equality       → comparison ( ( "!=" | "==" ) comparison )* ;
//! comparison     → addition ( ( ">" | ">=" | "<" | "<=" ) addition )* ;
//! addition       → multiplication ( ( "-" | "+" ) multiplication )* ;
//! multiplication → unary ( ( "/" | "*" ) unary )* ;
//! unary          → ( "!" | "-" ) unary
//!                | call ;
//! call           → primary ( "(" arguments? ")" | "." IDENTIFIER )* ;
//! primary        → NUMBER | STRING | "false" | "true" | "nil"
//!                | "(" expr ")" ;
//!
//! args           → expression ( "," expression )* ;
//! ```

use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::slice;

use crate::ast::*;
use crate::reporter::Reporter;
use crate::token::{Token, TokenValue};

// FIXME(yanchith): implement std::error:Error
#[derive(Debug)]
pub enum ParseError {
    ExpectedSemicolonAfterExprStmt(Option<Token>),
    ExpectedSemicolonAfterPrintStmt(Option<Token>),
    ExpectedSemicolonAfterReturnStmt(Option<Token>),
    ExpectedSemicolonAfterVarDeclStmt(Option<Token>),
    ExpectedIdentAfterVarKeyword(Option<Token>),
    ExpectedFunToStartWithIdent(Option<Token>),
    ExpectedOpeningParenAfterFunIdent(Option<Token>),
    ExpectedIdentInFunParams(Option<Token>),
    ExpectedBlockAfterFunHeader(Option<Token>),
    ExpectedClosingParenAfterFunParams(Option<Token>),
    ExpectedIdentAfterClassKeyword(Option<Token>),
    ExpectedOpeningBraceAfterClassIdent(Option<Token>),
    ExpectedClosingBraceAfterClassDecl,
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
    ExpectedIdentAfterDot(Option<Token>),
    ExpectedPrimaryExpr(Option<Token>),
    InvalidAssignTarget(Expr),
    TooManyCallArgs(Expr),
    TooManyFunParams(String),
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
            ParseError::ExpectedFunToStartWithIdent(Some(token)) => write!(
                f,
                "Expected identifier after 'fun' keyword but found token {}",
                token,
            ),
            ParseError::ExpectedFunToStartWithIdent(None) => write!(
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
            ParseError::ExpectedIdentInFunParams(Some(token)) => write!(
                f,
                "Expected identifier in function parameter list but found {}",
                token,
            ),
            ParseError::ExpectedIdentInFunParams(None) => write!(
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
            ParseError::ExpectedClosingParenAfterFunParams(Some(token)) => write!(
                f,
                "Expeced closing parenthesis after function params but found {}",
                token,
            ),
            ParseError::ExpectedClosingParenAfterFunParams(None) => write!(
                f,
                "Expeced closing parenthesis after function params but found end of input",
            ),
            ParseError::ExpectedIdentAfterClassKeyword(Some(token)) => write!(
                f,
                "Expected identifier after class keyword but found {}",
                token,
            ),
            ParseError::ExpectedIdentAfterClassKeyword(None) => write!(
                f,
                "Expected identifier after class keyword but found end of input",
            ),
            ParseError::ExpectedOpeningBraceAfterClassIdent(Some(token)) => write!(
                f,
                "Expected opening brace after class identifier but found {}",
                token,
            ),
            ParseError::ExpectedOpeningBraceAfterClassIdent(None) => write!(
                f,
                "Expected opening brace after class identifier but found end of input",
            ),
            ParseError::ExpectedClosingBraceAfterClassDecl => write!(
                f,
                "Expected closing brace after class declaration but found end of input"
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
            ParseError::ExpectedIdentAfterDot(Some(token)) => write!(
                f,
                "Expected identifier after dot but found {}",
                token,
            ),
            ParseError::ExpectedIdentAfterDot(None) => write!(
                f,
                "Expected identifier after dot but found end of input",
            ),
            ParseError::ExpectedPrimaryExpr(Some(token)) => {
                write!(f, "Expected primary expression but found token {}", token)
            }
            ParseError::ExpectedPrimaryExpr(None) => {
                write!(f, "Expected primary expression but found end of input")
            }
            ParseError::InvalidAssignTarget(expr) => {
                write!(f, "Expression {} is not a valid assignment target", expr)
            }
            ParseError::TooManyCallArgs(expr) => {
                write!(
                    f,
                    "Function call {} has too many args (max allowed is {})",
                    expr,
                    MAX_FUNCTION_ARGS,
                )
            }
            ParseError::TooManyFunParams(ident) => {
                write!(
                    f,
                    "Function declaration {} has too many params (max allowed is {})",
                    ident,
                    MAX_FUNCTION_ARGS,
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

struct ParseCtx<'a> {
    next_id: u64,
    tokens: Peekable<slice::Iter<'a, Token>>,
}

impl<'a> ParseCtx<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Self {
            next_id: 0,
            tokens: tokens.iter().peekable(),
        }
    }

    fn next_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;

        id
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

fn parse_decl(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if ctx.read_token_if(&TokenValue::Var).is_some() {
        finish_parse_var_decl(ctx)
    } else if ctx.read_token_if(&TokenValue::Fun).is_some() {
        finish_parse_fun_decl(ctx)
    } else if ctx.read_token_if(&TokenValue::Class).is_some() {
        finish_parse_class_decl(ctx)
    } else {
        parse_stmt(ctx)
    }
}

fn finish_parse_var_decl(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
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

fn finish_parse_fun_decl(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    parse_fun(ctx).map(Stmt::FunDecl)
}

fn finish_parse_class_decl(ctx: &mut ParseCtx) -> ParseResult<Stmt> {
    if let Some(class_ident) = ctx.read_token_if_ident() {
        if ctx.read_token_if(&TokenValue::LeftBrace).is_none() {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedOpeningBraceAfterClassIdent(token))
        } else {
            let mut methods = Vec::new();
            while !ctx.check_token(&TokenValue::RightBrace) && ctx.has_more_tokens() {
                let method = parse_fun(ctx)?;
                methods.push(method);
            }
            if ctx.read_token_if(&TokenValue::RightBrace).is_some() {
                Ok(Stmt::ClassDecl(ClassDeclStmt::new(class_ident, methods)))
            } else {
                Err(ParseError::ExpectedClosingBraceAfterClassDecl)
            }
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedIdentAfterClassKeyword(token))
    }
}

fn parse_fun(ctx: &mut ParseCtx) -> ParseResult<FunDeclStmt> {
    if let Some(fun_ident) = ctx.read_token_if_ident() {
        if ctx.read_token_if(&TokenValue::LeftParen).is_none() {
            let token = ctx.peek_token().cloned();
            Err(ParseError::ExpectedOpeningParenAfterFunIdent(token))
        } else {
            let mut params = Vec::new();
            if !ctx.check_token(&TokenValue::RightParen) {
                while {
                    if params.len() >= MAX_FUNCTION_ARGS {
                        // FIXME(yanchith): this unnecessarily throws the parser into
                        // panic mode, find a way not to do that. Maybe have a
                        // separate valiation pass?
                        return Err(ParseError::TooManyFunParams(fun_ident));
                    }

                    if let Some(ident) = ctx.read_token_if_ident() {
                        params.push(ident);
                    } else {
                        let token = ctx.peek_token().cloned();
                        return Err(ParseError::ExpectedIdentInFunParams(token));
                    }

                    ctx.read_token_if(&TokenValue::Comma).is_some()
                } { /*This is a do-while loop*/ }
            }

            if ctx.read_token_if(&TokenValue::RightParen).is_some() {
                if ctx.read_token_if(&TokenValue::LeftBrace).is_some() {
                    let body = finish_parse_block_stmt_raw(ctx)?;
                    Ok(FunDeclStmt::new(fun_ident, params, body))
                } else {
                    let token = ctx.peek_token().cloned();
                    Err(ParseError::ExpectedBlockAfterFunHeader(token))
                }
            } else {
                let token = ctx.peek_token().cloned();
                Err(ParseError::ExpectedClosingParenAfterFunParams(token))
            }
        }
    } else {
        let token = ctx.peek_token().cloned();
        Err(ParseError::ExpectedFunToStartWithIdent(token))
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
                Ok(Stmt::If(IfStmt::new(cond, then, Some(else_))))
            } else {
                Ok(Stmt::If(IfStmt::new(cond, then, None)))
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
            Some(finish_parse_var_decl(ctx)?)
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
            // FIXME(yanchith): can we afford to not wrap this in additional
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
        let stmt = parse_decl(ctx)?;
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
    parse_assign(ctx)
}

fn parse_assign(ctx: &mut ParseCtx) -> ParseResult<Expr> {
    let expr = parse_logic_or(ctx)?;
    if ctx.read_token_if(&TokenValue::Equal).is_some() {
        // Instead of looping through operands like elsewhere, we
        // recurse to `parse_assign` to have right-associativity
        let right = parse_assign(ctx)?;

        if let Expr::Var(var) = expr {
            Ok(Expr::Assign(AssignExpr::new(
                ctx.next_id(),
                var.ident().to_string(),
                right,
            )))
        } else if let Expr::Get(get) = expr {
            Ok(Expr::Set(SetExpr::new(
                get.object().clone(),
                get.field().to_string(),
                right,
            )))
        } else {
            Err(ParseError::InvalidAssignTarget(expr))
        }
    } else {
        // No assign token, fall through to other rules
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

    loop {
        if ctx.read_token_if(&TokenValue::LeftParen).is_some() {
            expr = finish_parse_call(ctx, expr)?;
        } else if ctx.read_token_if(&TokenValue::Dot).is_some() {
            if let Some(field_ident) = ctx.read_token_if_ident() {
                expr = Expr::Get(GetExpr::new(expr, field_ident));
            } else {
                let token = ctx.peek_token().cloned();
                return Err(ParseError::ExpectedIdentAfterDot(token));
            }
        } else {
            break;
        }
    }

    Ok(expr)
}

fn finish_parse_call(ctx: &mut ParseCtx, callee: Expr) -> ParseResult<Expr> {
    let mut args = Vec::new();
    if !ctx.check_token(&TokenValue::RightParen) {
        while {
            if args.len() >= MAX_FUNCTION_ARGS {
                // FIXME(yanchith): this unnecessarily throws the parser into
                // panic mode, find a way not to do that. Maybe have a
                // separate valiation pass?
                return Err(ParseError::TooManyCallArgs(callee));
            }
            let expr = parse_expr(ctx)?;
            args.push(expr);
            ctx.read_token_if(&TokenValue::Comma).is_some()
        } { /*This is a do-while loop*/ }
    }

    if ctx.read_token_if(&TokenValue::RightParen).is_some() {
        Ok(Expr::Call(CallExpr::new(callee, args)))
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
            TokenValue::This => Ok(Expr::This(ThisExpr::new(ctx.next_id()))),
            // FIXME(yanchith): intern ident
            TokenValue::Ident(ident) => Ok(Expr::Var(VarExpr::new(ctx.next_id(), ident.clone()))),
            TokenValue::LeftParen => {
                let expr = parse_expr(ctx)?;
                if ctx.read_token_if(&TokenValue::RightParen).is_some() {
                    Ok(Expr::Group(GroupExpr::new(expr)))
                } else {
                    let token = ctx.peek_token().cloned();
                    Err(ParseError::ExpectedClosingParenAfterGroupExpr(token))
                }
            }
            _ => Err(ParseError::ExpectedPrimaryExpr(Some(token))),
        }
    } else {
        Err(ParseError::ExpectedPrimaryExpr(None))
    }
}

const MAX_FUNCTION_ARGS: usize = 32;
