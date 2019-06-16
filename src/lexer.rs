use std::collections::HashMap;
use std::f64;
use std::fmt;
use std::iter::Peekable;
use std::str::{Chars, FromStr};

use crate::reporter::Reporter;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    value: TokenValue,
    line: u32,
}

impl Token {
    // TODO: replace line with Span
    pub fn new(value: TokenValue, line: u32) -> Self {
        Self { value, line }
    }

    pub fn value(&self) -> &TokenValue {
        &self.value
    }

    pub fn line(&self) -> u32 {
        self.line
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenValue {
    // Single-character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier(String),
    String(String),
    Number(f64),

    // Keywords
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

impl fmt::Display for TokenValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                // TODO: allocate less here (to_stirng())
                TokenValue::LeftParen => "LEFT_PAREN".to_string(),
                TokenValue::RightParen => "RIGHT_PAREN".to_string(),
                TokenValue::LeftBrace => "LEFT_BRACE".to_string(),
                TokenValue::RightBrace => "RIGHT_BRACE".to_string(),
                TokenValue::Comma => "COMMA".to_string(),
                TokenValue::Dot => "DOT".to_string(),
                TokenValue::Minus => "MINUS".to_string(),
                TokenValue::Plus => "PLUS".to_string(),
                TokenValue::Semicolon => "SEMICOLON".to_string(),
                TokenValue::Slash => "SLASH".to_string(),
                TokenValue::Star => "STAR".to_string(),
                TokenValue::Bang => "BANG".to_string(),
                TokenValue::BangEqual => "BANG_EQUAL".to_string(),
                TokenValue::Equal => "EQUAL".to_string(),
                TokenValue::EqualEqual => "EQUAL_EQUAL".to_string(),
                TokenValue::Greater => "GREATER".to_string(),
                TokenValue::GreaterEqual => "GREATER_EQUAKL".to_string(),
                TokenValue::Less => "LESS".to_string(),
                TokenValue::LessEqual => "LESS_EQUAL".to_string(),
                TokenValue::Identifier(identifier) => format!("IDENTIFIER({})", identifier),
                TokenValue::String(string) => format!("STRING({})", string),
                TokenValue::Number(number) => format!("NUMBER({})", number),
                TokenValue::And => "AND".to_string(),
                TokenValue::Class => "CLASS".to_string(),
                TokenValue::Else => "ELSE".to_string(),
                TokenValue::False => "FALSE".to_string(),
                TokenValue::Fun => "FUN".to_string(),
                TokenValue::For => "FOR".to_string(),
                TokenValue::If => "IF".to_string(),
                TokenValue::Nil => "NIL".to_string(),
                TokenValue::Or => "OR".to_string(),
                TokenValue::Print => "PRINT".to_string(),
                TokenValue::Return => "RETURN".to_string(),
                TokenValue::Super => "SUPER".to_string(),
                TokenValue::This => "THIS".to_string(),
                TokenValue::True => "TRUE".to_string(),
                TokenValue::Var => "VAR".to_string(),
                TokenValue::While => "WHILE".to_string(),
            }
        )
    }
}

pub fn scan(reporter: &mut Reporter, source: &str) -> Vec<Token> {
    let keyword_map = init_keyword_map();
    let mut ctx = LexerCtx::new(source);
    let mut tokens = Vec::new();

    while let Some(c) = ctx.read_char() {
        let maybe_token = match c {
            // Always single character tokens
            CHAR_LEFT_PAREN => Some(TokenValue::LeftParen),
            CHAR_RIGHT_PAREN => Some(TokenValue::RightParen),
            CHAR_LEFT_BRACE => Some(TokenValue::LeftBrace),
            CHAR_RIGHT_BRACE => Some(TokenValue::RightBrace),
            CHAR_COMMA => Some(TokenValue::Comma),
            CHAR_DOT => Some(TokenValue::Dot),
            CHAR_MINUS => Some(TokenValue::Minus),
            CHAR_PLUS => Some(TokenValue::Plus),
            CHAR_SEMICOLON => Some(TokenValue::Semicolon),
            CHAR_STAR => Some(TokenValue::Star),

            // One or two character tokens
            CHAR_BANG => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    ctx.read_char();
                    Some(TokenValue::BangEqual)
                } else {
                    Some(TokenValue::Bang)
                }
            }
            CHAR_EQUAL => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    ctx.read_char();
                    Some(TokenValue::EqualEqual)
                } else {
                    Some(TokenValue::Equal)
                }
            }
            CHAR_LESS => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    ctx.read_char();
                    Some(TokenValue::LessEqual)
                } else {
                    Some(TokenValue::Less)
                }
            }
            CHAR_GREATER => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    ctx.read_char();
                    Some(TokenValue::GreaterEqual)
                } else {
                    Some(TokenValue::Greater)
                }
            }

            // Slash token and comments
            CHAR_SLASH => {
                if let Some(CHAR_SLASH) = ctx.peek_char() {
                    ctx.consume_until_eol();
                    None
                } else {
                    Some(TokenValue::Slash)
                }
            }

            CHAR_DOUBLE_QUOTE => {
                if let Some(string) = ctx.read_string() {
                    Some(TokenValue::String(string))
                } else {
                    let message = format!("Unterminated string");
                    reporter.report_on_line(&message, ctx.curr_line);
                    break;
                }
            }

            CHAR_EOL => {
                ctx.curr_line += 1;
                None
            }

            CHAR_WHITESPACE | CHAR_CARRIAGE_RETURN | CHAR_TAB => None,

            digit if is_digit(digit) => {
                if let Some(number) = ctx.read_number(digit) {
                    Some(TokenValue::Number(number))
                } else {
                    let message = format!("Invalid number");
                    reporter.report_on_line(&message, ctx.curr_line);
                    break;
                }
            }

            alpha if is_alpha(alpha) => {
                let identifier = ctx.read_identifier(alpha);
                let token = keyword_map
                    .get(&identifier)
                    .cloned()
                    .unwrap_or_else(|| TokenValue::Identifier(identifier));

                Some(token)
            }

            unexpected => {
                let message = format!("Unexpected character {}", unexpected);
                reporter.report_on_line(&message, ctx.curr_line);
                break;
            }
        };

        if let Some(token) = maybe_token {
            tokens.push(Token::new(token, ctx.curr_line));
        }
    }

    tokens
}

struct LexerCtx<'a> {
    source: Peekable<Chars<'a>>,
    curr_char: u32,
    curr_line: u32,
}

impl<'a> LexerCtx<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source: source.chars().peekable(),
            curr_char: 0,
            curr_line: 1,
        }
    }

    fn consume_until_eol(&mut self) {
        while let Some(c) = self.source.next() {
            self.curr_char += 1;
            if c == CHAR_EOL {
                self.curr_line += 1;
                break;
            }
        }
    }

    fn read_string(&mut self) -> Option<String> {
        let mut buffer = String::new();
        let mut string_terminated = false;
        while let Some(c) = self.source.next() {
            self.curr_char += 1;
            if c == CHAR_EOL {
                self.curr_line += 1;
            }

            if c == CHAR_DOUBLE_QUOTE {
                string_terminated = true;
                break;
            }

            buffer.push(c);
        }

        if string_terminated {
            Some(buffer)
        } else {
            None
        }
    }

    fn read_number(&mut self, first_digit: char) -> Option<f64> {
        let mut buffer = format!("{}", first_digit);

        // TODO: float parsing
        while let Some(maybe_digit) = self.peek_char() {
            if is_digit(maybe_digit) {
                buffer.push(maybe_digit);
                self.read_char();
            } else {
                break;
            }
        }

        f64::from_str(&buffer).ok()
    }

    fn read_identifier(&mut self, first_alpha: char) -> String {
        let mut buffer = format!("{}", first_alpha);

        while let Some(maybe_alphanumeric) = self.peek_char() {
            if is_alphanumeric(maybe_alphanumeric) {
                buffer.push(maybe_alphanumeric);
                self.read_char();
            } else {
                break;
            }
        }

        buffer
    }

    fn read_char(&mut self) -> Option<char> {
        self.curr_char += 1;
        self.source.next()
    }

    fn peek_char(&mut self) -> Option<char> {
        self.source.peek().copied()
    }
}

fn is_digit(c: char) -> bool {
    c >= CHAR_0 && c <= CHAR_9
}

fn is_alpha(c: char) -> bool {
    c >= CHAR_LOWERCASE_A && c <= CHAR_LOWERCASE_Z
        || c >= CHAR_UPPERCASE_A && c <= CHAR_UPPERCASE_Z
        || c == CHAR_UNDERSCORE
}

fn is_alphanumeric(c: char) -> bool {
    is_alpha(c) || is_digit(c)
}

fn init_keyword_map() -> HashMap<String, TokenValue> {
    let mut map = HashMap::with_capacity(16);

    map.insert(KEYWORD_AND.to_string(), TokenValue::And);
    map.insert(KEYWORD_CLASS.to_string(), TokenValue::Class);
    map.insert(KEYWORD_ELSE.to_string(), TokenValue::Else);
    map.insert(KEYWORD_FALSE.to_string(), TokenValue::False);
    map.insert(KEYWORD_FUN.to_string(), TokenValue::Fun);
    map.insert(KEYWORD_FOR.to_string(), TokenValue::For);
    map.insert(KEYWORD_IF.to_string(), TokenValue::If);
    map.insert(KEYWORD_NIL.to_string(), TokenValue::Nil);
    map.insert(KEYWORD_OR.to_string(), TokenValue::Or);
    map.insert(KEYWORD_PRINT.to_string(), TokenValue::Print);
    map.insert(KEYWORD_RETURN.to_string(), TokenValue::Return);
    map.insert(KEYWORD_SUPER.to_string(), TokenValue::Super);
    map.insert(KEYWORD_THIS.to_string(), TokenValue::This);
    map.insert(KEYWORD_TRUE.to_string(), TokenValue::True);
    map.insert(KEYWORD_VAR.to_string(), TokenValue::Var);
    map.insert(KEYWORD_WHILE.to_string(), TokenValue::While);

    map
}

const CHAR_LEFT_PAREN: char = '(';
const CHAR_RIGHT_PAREN: char = ')';
const CHAR_LEFT_BRACE: char = '{';
const CHAR_RIGHT_BRACE: char = '}';
const CHAR_COMMA: char = ',';
const CHAR_DOT: char = '.';
const CHAR_MINUS: char = '-';
const CHAR_PLUS: char = '+';
const CHAR_SEMICOLON: char = ';';
const CHAR_SLASH: char = '/';
const CHAR_STAR: char = '*';

const CHAR_BANG: char = '!';
const CHAR_EQUAL: char = '=';
const CHAR_LESS: char = '<';
const CHAR_GREATER: char = '>';

const CHAR_DOUBLE_QUOTE: char = '"';

const CHAR_EOL: char = '\n';
const CHAR_WHITESPACE: char = ' ';
const CHAR_CARRIAGE_RETURN: char = '\r';
const CHAR_TAB: char = '\t';

const CHAR_0: char = '0';
const CHAR_9: char = '9';
const CHAR_LOWERCASE_A: char = 'a';
const CHAR_LOWERCASE_Z: char = 'z';
const CHAR_UPPERCASE_A: char = 'A';
const CHAR_UPPERCASE_Z: char = 'Z';
const CHAR_UNDERSCORE: char = '_';

const KEYWORD_AND: &str = "and";
const KEYWORD_CLASS: &str = "class";
const KEYWORD_ELSE: &str = "else";
const KEYWORD_FALSE: &str = "false";
const KEYWORD_FUN: &str = "fun";
const KEYWORD_FOR: &str = "for";
const KEYWORD_IF: &str = "if";
const KEYWORD_NIL: &str = "nil";
const KEYWORD_OR: &str = "or";
const KEYWORD_PRINT: &str = "print";
const KEYWORD_RETURN: &str = "return";
const KEYWORD_SUPER: &str = "super";
const KEYWORD_THIS: &str = "this";
const KEYWORD_TRUE: &str = "true";
const KEYWORD_VAR: &str = "var";
const KEYWORD_WHILE: &str = "while";
