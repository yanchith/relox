use std::f64;
use std::fmt;
use std::iter::Peekable;
use std::str::{Chars, FromStr};

pub enum Token {
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

    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            // TODO: allocate less here (to_stirng())
            Token::LeftParen => "LEFT_PAREN".to_string(),
            Token::RightParen => "RIGHT_PAREN".to_string(),
            Token::LeftBrace => "LEFT_BRACE".to_string(),
            Token::RightBrace => "RIGHT_BRACE".to_string(),
            Token::Comma => "COMMA".to_string(),
            Token::Dot => "DOT".to_string(),
            Token::Minus => "MINUS".to_string(),
            Token::Plus => "PLUS".to_string(),
            Token::Semicolon => "SEMICOLON".to_string(),
            Token::Slash => "SLASH".to_string(),
            Token::Star => "STAR".to_string(),
            Token::Bang => "BANG".to_string(),
            Token::BangEqual => "BANG_EQUAL".to_string(),
            Token::Equal => "EQUAL".to_string(),
            Token::EqualEqual => "EQUAL_EQUAL".to_string(),
            Token::Greater => "GREATER".to_string(),
            Token::GreaterEqual => "GREATER_EQUAKL".to_string(),
            Token::Less => "LESS".to_string(),
            Token::LessEqual => "LESS_EQUAL".to_string(),
            Token::Identifier(identifier) => format!("IDENTIFIER({})", identifier),
            Token::String(string) => format!("STRING({})", string),
            Token::Number(number) => format!("NUMBER({})", number),
            Token::And => "AND".to_string(),
            Token::Class => "CLASS".to_string(),
            Token::Else => "ELSE".to_string(),
            Token::False => "FALSE".to_string(),
            Token::Fun => "FUN".to_string(),
            Token::For => "FOR".to_string(),
            Token::If => "IF".to_string(),
            Token::Nil => "NIL".to_string(),
            Token::Or => "OR".to_string(),
            Token::Print => "PRINT".to_string(),
            Token::Return => "RETURN".to_string(),
            Token::Super => "SUPER".to_string(),
            Token::This => "THIS".to_string(),
            Token::True => "TRUE".to_string(),
            Token::Var => "VAR".to_string(),
            Token::While => "WHILE".to_string(),
            Token::Eof => "EOF".to_string(),
        })
    }
}

pub fn scan_tokens(source: &str, report: Box<dyn Fn(usize, &str, &str)>) -> Vec<Token> {
    let mut ctx = LexerCtx::new(source);
    let mut tokens = Vec::new();

    while let Some(c) = ctx.read() {
        let maybe_token = match c {

            // Always single character tokens
            CHAR_LEFT_PAREN => Some(Token::LeftParen),
            CHAR_RIGHT_PAREN => Some(Token::RightParen),
            CHAR_LEFT_BRACE => Some(Token::LeftBrace),
            CHAR_RIGHT_BRACE => Some(Token::RightBrace),
            CHAR_COMMA => Some(Token::Comma),
            CHAR_MINUS => Some(Token::Minus),
            CHAR_PLUS => Some(Token::Plus),
            CHAR_SEMICOLON => Some(Token::Semicolon),
            CHAR_STAR => Some(Token::Star),

            // One or two character tokens
            CHAR_BANG => {
                if let Some(CHAR_EQUAL) = ctx.peek() {
                    ctx.read();
                    Some(Token::BangEqual)
                } else {
                    Some(Token::Bang)
                }
            },
            CHAR_EQUAL => {
                if let Some(CHAR_EQUAL) = ctx.peek() {
                    ctx.read();
                    Some(Token::EqualEqual)
                } else {
                    Some(Token::Equal)
                }
            },
            CHAR_LESS => {
                if let Some(CHAR_EQUAL) = ctx.peek() {
                    ctx.read();
                    Some(Token::LessEqual)
                } else {
                    Some(Token::Less)
                }
            },
            CHAR_GREATER => {
                if let Some(CHAR_EQUAL) = ctx.peek() {
                    ctx.read();
                    Some(Token::GreaterEqual)
                } else {
                    Some(Token::Greater)
                }
            },

            // Slash token and comments

            CHAR_SLASH => {
                if let Some(CHAR_SLASH) = ctx.peek() {
                    ctx.consume_until_eol();
                    None
                } else {
                    Some(Token::Slash)
                }
            }

            CHAR_DOUBLE_QUOTE => {
                if let Some(string) = ctx.read_string() {
                    Some(Token::String(string))
                } else {
                    let message = format!("Unterminated string");
                    report(ctx.curr_line, "", &message);
                    break;
                }
            }

            CHAR_EOL => {
                ctx.curr_line += 1;
                None
            }

            CHAR_WHITESPACE | CHAR_CARRIAGE_RETURN | CHAR_TAB => {
                None
            }

            digit if is_digit(digit) => {
                if let Some(number) = ctx.read_number(digit) {
                    Some(Token::Number(number))
                } else {
                    let message = format!("Invalid number");
                    report(ctx.curr_line, "", &message);
                    break;
                }
            }

            unexpected_char => {
                let message = format!("Unexpected character {}", unexpected_char);
                report(ctx.curr_line, "", &message);
                break;
            }
        };

        if let Some(token) = maybe_token {
            tokens.push(token);
        }
    }

    tokens
}

struct LexerCtx<'a> {
    source: Peekable<Chars<'a>>,
    curr_char: usize,
    curr_line: usize,
}

impl<'a> LexerCtx<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source: source.chars().peekable(),
            curr_char: 0,
            curr_line: 1,
        }
    }

    fn read(&mut self) -> Option<char> {
        self.curr_char += 1;
        self.source.next()
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
        while let Some(maybe_digit) = self.peek() {
            if is_digit(maybe_digit) {
                buffer.push(maybe_digit);
                self.read();
            } else {
                break;
            }
        }

        f64::from_str(&buffer).ok()
    }

    fn peek(&mut self) -> Option<char> {
        self.source.peek().copied()
    }
}

fn is_digit(c: char) -> bool {
    c >= CHAR_0 && c <= CHAR_9
}

const CHAR_LEFT_PAREN: char = '(';
const CHAR_RIGHT_PAREN: char = ')';
const CHAR_LEFT_BRACE: char = '{';
const CHAR_RIGHT_BRACE: char = '}';
const CHAR_COMMA: char = ',';
const CHAR_MINUS: char = '-';
const CHAR_PLUS: char = '+';
const CHAR_SEMICOLON: char = ';';
const CHAR_SLASH: char = '/';
const CHAR_STAR: char = '*';

const CHAR_BANG: char = '!';
const CHAR_EQUAL: char = '=';
const CHAR_LESS: char = '<';
const CHAR_GREATER: char= '>';

const CHAR_DOUBLE_QUOTE: char = '"';

const CHAR_EOL: char = '\n';
const CHAR_WHITESPACE: char = ' ';
const CHAR_CARRIAGE_RETURN: char = '\r';
const CHAR_TAB: char = '\t';

const CHAR_0: char = '0';
const CHAR_9: char = '9';
