use std::f64;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    value: TokenValue,
    span: Span,
}

impl Token {
    pub fn new(value: TokenValue, span: Span) -> Self {
        Self { value, span }
    }

    pub fn value(&self) -> &TokenValue {
        &self.value
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// A span of text. It starts on `line` and `column` and ending on
/// `line_end` and `column_end` (inclusive). Lines are 1-indexed,
/// columns are 0-indexed,
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub line: u32,
    pub line_end: u32,
    pub column: u32,
    pub column_end: u32,
}

impl Span {
    pub fn new(line: u32, line_end: u32, column: u32, column_end: u32) -> Span {
        Self {
            line,
            line_end,
            column,
            column_end,
        }
    }

    pub fn merge(left: &Self, right: &Self) -> Self {
        Self {
            line: left.line,
            line_end: right.line_end,
            column: left.column,
            column_end: right.column_end,
        }
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
    Ident(String),
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
        match self {
            TokenValue::LeftParen => write!(f, "LEFT_PAREN"),
            TokenValue::RightParen => write!(f, "RIGHT_PAREN"),
            TokenValue::LeftBrace => write!(f, "LEFT_BRACE"),
            TokenValue::RightBrace => write!(f, "RIGHT_BRACE"),
            TokenValue::Comma => write!(f, "COMMA"),
            TokenValue::Dot => write!(f, "DOT"),
            TokenValue::Minus => write!(f, "MINUS"),
            TokenValue::Plus => write!(f, "PLUS"),
            TokenValue::Semicolon => write!(f, "SEMICOLON"),
            TokenValue::Slash => write!(f, "SLASH"),
            TokenValue::Star => write!(f, "STAR"),
            TokenValue::Bang => write!(f, "BANG"),
            TokenValue::BangEqual => write!(f, "BANG_EQUAL"),
            TokenValue::Equal => write!(f, "EQUAL"),
            TokenValue::EqualEqual => write!(f, "EQUAL_EQUAL"),
            TokenValue::Greater => write!(f, "GREATER"),
            TokenValue::GreaterEqual => write!(f, "GREATER_EQUAKL"),
            TokenValue::Less => write!(f, "LESS"),
            TokenValue::LessEqual => write!(f, "LESS_EQUAL"),
            TokenValue::Ident(ident) => write!(f, "IDENT({})", ident),
            TokenValue::String(string) => write!(f, "STRING({})", string),
            TokenValue::Number(number) => write!(f, "NUMBER({})", number),
            TokenValue::And => write!(f, "AND"),
            TokenValue::Class => write!(f, "CLASS"),
            TokenValue::Else => write!(f, "ELSE"),
            TokenValue::False => write!(f, "FALSE"),
            TokenValue::Fun => write!(f, "FUN"),
            TokenValue::For => write!(f, "FOR"),
            TokenValue::If => write!(f, "IF"),
            TokenValue::Nil => write!(f, "NIL"),
            TokenValue::Or => write!(f, "OR"),
            TokenValue::Print => write!(f, "PRINT"),
            TokenValue::Return => write!(f, "RETURN"),
            TokenValue::Super => write!(f, "SUPER"),
            TokenValue::This => write!(f, "THIS"),
            TokenValue::True => write!(f, "TRUE"),
            TokenValue::Var => write!(f, "VAR"),
            TokenValue::While => write!(f, "WHILE"),
        }
    }
}
