use std::iter::Peekable;
use std::str::{Chars, FromStr};

use crate::reporter::Reporter;
use crate::token::{Token, TokenValue, Span};

// FIXME(yanchith): return a result and add a error type

pub fn lex(reporter: &mut Reporter, source: &str) -> Vec<Token> {
    let mut ctx = LexCtx::new(source);
    let mut tokens = Vec::new();

    while let Some((c, span)) = ctx.read_char() {
        let maybe_token = match c {
            // Always single character tokens
            CHAR_LEFT_PAREN => Some(Token::new(TokenValue::LeftParen, span)),
            CHAR_RIGHT_PAREN => Some(Token::new(TokenValue::RightParen, span)),
            CHAR_LEFT_BRACE => Some(Token::new(TokenValue::LeftBrace, span)),
            CHAR_RIGHT_BRACE => Some(Token::new(TokenValue::RightBrace, span)),
            CHAR_COMMA => Some(Token::new(TokenValue::Comma, span)),
            CHAR_DOT => Some(Token::new(TokenValue::Dot, span)),
            CHAR_MINUS => Some(Token::new(TokenValue::Minus, span)),
            CHAR_PLUS => Some(Token::new(TokenValue::Plus, span)),
            CHAR_SEMICOLON => Some(Token::new(TokenValue::Semicolon, span)),
            CHAR_STAR => Some(Token::new(TokenValue::Star, span)),

            // One or two character tokens
            CHAR_BANG => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    let (_, span_end) = ctx.read_char().unwrap();
                    Some(Token::new(
                        TokenValue::BangEqual,
                        Span::merge(&span, &span_end),
                    ))
                } else {
                    Some(Token::new(TokenValue::Bang, span))
                }
            }
            CHAR_EQUAL => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    let (_, span_end) = ctx.read_char().unwrap();
                    Some(Token::new(
                        TokenValue::EqualEqual,
                        Span::merge(&span, &span_end),
                    ))
                } else {
                    Some(Token::new(TokenValue::Equal, span))
                }
            }
            CHAR_LESS => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    let (_, span_end) = ctx.read_char().unwrap();
                    Some(Token::new(
                        TokenValue::LessEqual,
                        Span::merge(&span, &span_end),
                    ))
                } else {
                    Some(Token::new(TokenValue::Less, span))
                }
            }
            CHAR_GREATER => {
                if let Some(CHAR_EQUAL) = ctx.peek_char() {
                    let (_, span_end) = ctx.read_char().unwrap();
                    Some(Token::new(
                        TokenValue::GreaterEqual,
                        Span::merge(&span, &span_end),
                    ))
                } else {
                    Some(Token::new(TokenValue::Greater, span))
                }
            }

            // Slash token and comments
            CHAR_SLASH => {
                if let Some(CHAR_SLASH) = ctx.peek_char() {
                    ctx.read_line_finish();
                    None
                } else {
                    Some(Token::new(TokenValue::Slash, span))
                }
            }

            CHAR_DOUBLE_QUOTE => {
                if let Some((string, string_span)) = ctx.read_string_finish() {
                    Some(Token::new(TokenValue::String(string), string_span))
                } else {
                    // FIXME(yanchith): get span of unterminated string and report that!
                    reporter.report_compile_error(format!(
                        "Unterminated string starting on line: {}",
                        span.line,
                    ));
                    break;
                }
            }

            CHAR_NEWLINE => None,

            CHAR_WHITESPACE | CHAR_CARRIAGE_RETURN | CHAR_TAB => None,

            digit if is_digit(digit) => {
                if let Some((number, number_span)) = ctx.read_number_finish(digit) {
                    Some(Token::new(TokenValue::Number(number), number_span))
                } else {
                    // FIXME(yanchith): get span of number we were trying to parse and report that!
                    reporter.report_compile_error(format!("Invalid number on line: {}", span.line));
                    break;
                }
            }

            alpha if is_alpha(alpha) => {
                let (ident, ident_span) = ctx.read_ident_finish(alpha);

                let search_result = KEYWORDS.binary_search_by_key(&ident.as_str(), |&(k, _)| k);
                let token_value = match search_result {
                    Ok(index) => KEYWORDS[index].1.clone(),
                    Err(_) => TokenValue::Ident(ident),
                };

                Some(Token::new(token_value, ident_span))
            }

            unexpected => {
                reporter.report_compile_error(format!(
                    "Unexpected character {} on line {}",
                    unexpected, span.line,
                ));
                break;
            }
        };

        if let Some(token) = maybe_token {
            tokens.push(token);
        }
    }

    tokens
}

struct LexCtx<'a> {
    source: Peekable<Chars<'a>>,
    curr_line: u32,
    curr_column: u32,
}

impl<'a> LexCtx<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source: source.chars().peekable(),
            curr_line: 1,
            curr_column: 0,
        }
    }

    pub fn read_line_finish(&mut self) {
        while let Some(c) = self.source.next() {
            self.curr_column += 1;
            if c == CHAR_NEWLINE {
                self.curr_line += 1;
                self.curr_column = 0;
                break;
            }
        }
    }

    pub fn read_string_finish(&mut self) -> Option<(String, Span)> {
        let line_start = self.curr_line; // Strings can be multiline, need to track where it started

        // FIXME(yanchith): track this properly... The string could have started
        // as the last character of the previous
        // line. `saturating_sub()` is used to prevent underflow if it
        // did.
        let column_start = self.curr_column.saturating_sub(1);

        let mut buffer = String::new();
        let mut string_terminated = false;
        while let Some(c) = self.source.next() {
            self.curr_column += 1;
            if c == CHAR_NEWLINE {
                self.curr_line += 1;
                self.curr_column = 0;
            }

            if c == CHAR_DOUBLE_QUOTE {
                string_terminated = true;
                break;
            }

            buffer.push(c);
        }

        if string_terminated {
            let span = Span::new(line_start, self.curr_line, column_start, self.curr_column);
            Some((buffer, span))
        } else {
            None
        }
    }

    /// A number literal is a series of digits optionally followed by
    /// a "." and one or more digits
    pub fn read_number_finish(&mut self, first_digit: char) -> Option<(f64, Span)> {
        // First char is already read. Should be safe to do unchecked
        // sub, numbers can not span multiple lines.
        let column_start = self.curr_column - 1;
        let mut buffer = format!("{}", first_digit);

        // Read leading digits
        while let Some(maybe_digit) = self.source.peek().copied() {
            if is_digit(maybe_digit) {
                buffer.push(maybe_digit);
                self.read_char();
            } else {
                break;
            }
        }

        // Try reading "." and the rest of the digits
        if let Some(maybe_dot) = self.source.peek().copied() {
            if maybe_dot == CHAR_DOT {
                buffer.push(maybe_dot);
                self.read_char();

                let mut read_additional_digits = false;

                while let Some(maybe_digit) = self.source.peek().copied() {
                    if is_digit(maybe_digit) {
                        buffer.push(maybe_digit);
                        self.read_char();
                        read_additional_digits = true;
                    } else {
                        break;
                    }
                }

                // Lox does not support leading or trailing dot in
                // number literals. This is not a valid number
                // literal, if we encountered no digits after ".".
                // Also note: we have to error here, because we
                // already consumed at least the "." from the input
                // and would have to "return" it if we didn't match
                // something. Fortunately there is nothing in Lox yet
                // that would require us to recover (e.g. methods on
                // numbers -> "4.sqrt()")
                if !read_additional_digits {
                    return None;
                }
            }
        }

        if let Ok(number) = f64::from_str(&buffer) {
            let span = Span::new(
                self.curr_line,
                self.curr_line,
                column_start,
                self.curr_column,
            );
            Some((number, span))
        } else {
            None
        }
    }

    pub fn read_ident_finish(&mut self, first_alpha: char) -> (String, Span) {
        // First char is already read. Should be safe to do unchecked
        // sub, idents can not span multiple lines.
        let column_start = self.curr_column - 1;
        let mut buffer = format!("{}", first_alpha);

        while let Some(maybe_alphanumeric) = self.source.peek() {
            if is_alphanumeric(*maybe_alphanumeric) {
                buffer.push(*maybe_alphanumeric);
                self.read_char();
            } else {
                break;
            }
        }

        let span = Span::new(
            self.curr_line,
            self.curr_line,
            column_start,
            self.curr_column,
        );
        (buffer, span)
    }

    pub fn read_char(&mut self) -> Option<(char, Span)> {
        if let Some(c) = self.source.next() {
            let column_start = self.curr_column;
            let line_start = self.curr_line;
            self.curr_column += 1;
            if c == CHAR_NEWLINE {
                self.curr_line += 1;
                self.curr_column = 0;
            }
            let span = Span::new(line_start, self.curr_line, column_start, self.curr_column);

            Some((c, span))
        } else {
            None
        }
    }

    pub fn peek_char(&mut self) -> Option<char> {
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

// The keyword strings to token mapping. Must ALWAYS be sorted as
// binary search is performed.
static KEYWORDS: &[(&str, TokenValue)] = &[
    (KEYWORD_AND, TokenValue::And),
    (KEYWORD_CLASS, TokenValue::Class),
    (KEYWORD_ELSE, TokenValue::Else),
    (KEYWORD_FALSE, TokenValue::False),
    (KEYWORD_FOR, TokenValue::For),
    (KEYWORD_FUN, TokenValue::Fun),
    (KEYWORD_IF, TokenValue::If),
    (KEYWORD_NIL, TokenValue::Nil),
    (KEYWORD_OR, TokenValue::Or),
    (KEYWORD_PRINT, TokenValue::Print),
    (KEYWORD_RETURN, TokenValue::Return),
    (KEYWORD_SUPER, TokenValue::Super),
    (KEYWORD_THIS, TokenValue::This),
    (KEYWORD_TRUE, TokenValue::True),
    (KEYWORD_VAR, TokenValue::Var),
    (KEYWORD_WHILE, TokenValue::While),
];

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

const CHAR_NEWLINE: char = '\n';
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
const KEYWORD_FOR: &str = "for";
const KEYWORD_FUN: &str = "fun";
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
