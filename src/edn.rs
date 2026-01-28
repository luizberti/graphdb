//! # EDN Parser
//!
//! Implements the EDN spec from https://github.com/edn-format/edn

#![allow(unused_assignments)] // miette's #[label] macro triggers false positive

use std::fmt;
use std::hash::{Hash, Hasher};

use miette::{Diagnostic, SourceSpan};

// ================================================================================================
// DATA MODEL =====================================================================================
// ================================================================================================

#[derive(Clone, Debug)]
pub enum EDN {
    Nil,
    Bool(bool),
    Int(i64),
    BigInt(String),
    Float(f64),
    Decimal(String),
    String(String),
    Char(char),
    Symbol(Option<String>, String), // (namespace, name)
    Keyword(Option<String>, String),
    List(Vec<EDN>),
    Vector(Vec<EDN>),
    Map(Vec<(EDN, EDN)>),
    Set(Vec<EDN>),
    Tagged(String, Box<EDN>),
}

impl PartialEq for EDN {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (EDN::Nil, EDN::Nil) => true,
            (EDN::Bool(a), EDN::Bool(b)) => a == b,
            (EDN::Int(a), EDN::Int(b)) => a == b,
            (EDN::BigInt(a), EDN::BigInt(b)) => a == b,
            (EDN::Float(a), EDN::Float(b)) => a.to_bits() == b.to_bits(),
            (EDN::Decimal(a), EDN::Decimal(b)) => a == b,
            (EDN::String(a), EDN::String(b)) => a == b,
            (EDN::Char(a), EDN::Char(b)) => a == b,
            (EDN::Symbol(ns1, n1), EDN::Symbol(ns2, n2)) => ns1 == ns2 && n1 == n2,
            (EDN::Keyword(ns1, n1), EDN::Keyword(ns2, n2)) => ns1 == ns2 && n1 == n2,
            (EDN::List(a), EDN::List(b)) => a == b,
            (EDN::Vector(a), EDN::Vector(b)) => a == b,
            (EDN::Map(a), EDN::Map(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter()
                    .all(|(k, v)| b.iter().any(|(k2, v2)| k == k2 && v == v2))
            }
            (EDN::Set(a), EDN::Set(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter().all(|x| b.iter().any(|y| x == y))
            }
            (EDN::Tagged(t1, v1), EDN::Tagged(t2, v2)) => t1 == t2 && v1 == v2,
            _ => false,
        }
    }
}

impl Eq for EDN {}

impl Hash for EDN {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            EDN::Nil => {}
            EDN::Bool(b) => b.hash(state),
            EDN::Int(n) => n.hash(state),
            EDN::BigInt(s) => s.hash(state),
            EDN::Float(f) => f.to_bits().hash(state),
            EDN::Decimal(s) => s.hash(state),
            EDN::String(s) => s.hash(state),
            EDN::Char(c) => c.hash(state),
            EDN::Symbol(ns, n) => {
                ns.hash(state);
                n.hash(state);
            }
            EDN::Keyword(ns, n) => {
                ns.hash(state);
                n.hash(state);
            }
            EDN::List(v) | EDN::Vector(v) | EDN::Set(v) => v.hash(state),
            EDN::Map(m) => m.len().hash(state),
            EDN::Tagged(t, v) => {
                t.hash(state);
                v.hash(state);
            }
        }
    }
}

impl fmt::Display for EDN {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EDN::Nil => write!(f, "nil"),
            EDN::Bool(b) => write!(f, "{}", b),
            EDN::Int(n) => write!(f, "{}", n),
            EDN::BigInt(s) => write!(f, "{}N", s),
            EDN::Float(n) => write!(f, "{}", n),
            EDN::Decimal(s) => write!(f, "{}M", s),
            EDN::String(s) => write!(f, "\"{}\"", escape_string(s)),
            EDN::Char(c) => write!(f, "\\{}", format_char(*c)),
            EDN::Symbol(ns, name) => match ns {
                Some(ns) => write!(f, "{}/{}", ns, name),
                None => write!(f, "{}", name),
            },
            EDN::Keyword(ns, name) => match ns {
                Some(ns) => write!(f, ":{}/{}", ns, name),
                None => write!(f, ":{}", name),
            },
            EDN::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
            EDN::Vector(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
            EDN::Map(pairs) => {
                write!(f, "{{")?;
                for (i, (k, v)) in pairs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} {}", k, v)?;
                }
                write!(f, "}}")
            }
            EDN::Set(items) => {
                write!(f, "#{{")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "}}")
            }
            EDN::Tagged(tag, value) => write!(f, "#{} {}", tag, value),
        }
    }
}

fn escape_string(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out
}

fn format_char(c: char) -> String {
    match c {
        '\n' => "newline".to_string(),
        '\r' => "return".to_string(),
        ' ' => "space".to_string(),
        '\t' => "tab".to_string(),
        c => c.to_string(),
    }
}

// ================================================================================================
// PARSER =========================================================================================
// ================================================================================================

#[derive(Debug, Diagnostic, thiserror::Error)]
#[error("{mesg}")]
pub struct ParseError {
    pub mesg: String,
    #[label("{mesg}")]
    pub span: SourceSpan,
}

pub struct Parser<'a> {
    string: &'a str,
    offset: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            string: input,
            offset: 0,
        }
    }

    fn remaining(&self) -> &str {
        &self.string[self.offset..]
    }

    fn peek(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.offset += c.len_utf8();
        Some(c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while let Some(c) = self.peek() {
                if c.is_whitespace() || c == ',' {
                    self.advance();
                } else {
                    break;
                }
            }

            if self.peek() == Some(';') {
                while let Some(c) = self.advance() {
                    if c == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        let len = self.peek().map(|c| c.len_utf8()).unwrap_or(1);
        ParseError {
            mesg: message.into(),
            span: (self.offset, len).into(),
        }
    }

    fn error_at(&self, offset: usize, len: usize, message: impl Into<String>) -> ParseError {
        ParseError {
            mesg: message.into(),
            span: (offset, len).into(),
        }
    }

    fn expect(&mut self, expected: char) -> Result<(), ParseError> {
        match self.advance() {
            Some(c) if c == expected => Ok(()),
            Some(c) => Err(self.error(format!("expected '{}', got '{}'", expected, c))),
            None => Err(self.error(format!("expected '{}', got EOF", expected))),
        }
    }

    pub fn parse(&mut self) -> Result<EDN, ParseError> {
        self.skip_whitespace_and_comments();

        let c = self.peek().ok_or_else(|| self.error("unexpected EOF"))?;

        match c {
            '"' => self.parse_string(),
            '\\' => self.parse_char(),
            ':' => self.parse_keyword(),
            '(' => self.parse_list(),
            '[' => self.parse_vector(),
            '{' => self.parse_map(),
            '#' => self.parse_dispatch(),
            _ if c == '-' || c == '+' || c.is_ascii_digit() => self.parse_number(),
            _ if is_symbol_start(c) => self.parse_symbol(),
            _ => Err(self.error(format!("unexpected character: '{}'", c))),
        }
    }

    pub fn parse_all(&mut self) -> Result<Vec<EDN>, ParseError> {
        let mut values = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek().is_none() {
                break;
            }
            values.push(self.parse()?);
        }
        Ok(values)
    }

    fn parse_string(&mut self) -> Result<EDN, ParseError> {
        let start = self.offset;
        self.expect('"')?;
        let mut s = String::new();

        loop {
            match self.advance() {
                Some('"') => break,
                Some('\\') => {
                    let esc_start = self.offset - 1;
                    let escaped = self
                        .advance()
                        .ok_or_else(|| self.error("unexpected EOF in string escape"))?;
                    match escaped {
                        't' => s.push('\t'),
                        'r' => s.push('\r'),
                        'n' => s.push('\n'),
                        '\\' => s.push('\\'),
                        '"' => s.push('"'),
                        'u' => {
                            let hex = self.take_while(|c| c.is_ascii_hexdigit(), 4);
                            if hex.len() != 4 {
                                return Err(self.error_at(
                                    esc_start,
                                    self.offset - esc_start,
                                    "invalid unicode escape",
                                ));
                            }
                            let cp = u32::from_str_radix(&hex, 16).map_err(|_| {
                                self.error_at(esc_start, self.offset - esc_start, "invalid unicode")
                            })?;
                            let ch = char::from_u32(cp).ok_or_else(|| {
                                self.error_at(
                                    esc_start,
                                    self.offset - esc_start,
                                    "invalid unicode codepoint",
                                )
                            })?;
                            s.push(ch);
                        }
                        _ => {
                            return Err(self.error_at(
                                esc_start,
                                2,
                                format!("invalid escape: \\{}", escaped),
                            ));
                        }
                    }
                }
                Some(c) => s.push(c),
                None => {
                    return Err(self.error_at(start, self.offset - start, "unterminated string"));
                }
            }
        }

        Ok(EDN::String(s))
    }

    fn parse_char(&mut self) -> Result<EDN, ParseError> {
        self.expect('\\')?;

        for (name, ch) in [
            ("newline", '\n'),
            ("return", '\r'),
            ("space", ' '),
            ("tab", '\t'),
        ] {
            if self.remaining().starts_with(name) {
                let after = self.remaining().chars().nth(name.len());
                if after.is_none() || is_delimiter(after.unwrap()) {
                    self.offset += name.len();
                    return Ok(EDN::Char(ch));
                }
            }
        }

        if self.remaining().starts_with('u') {
            self.advance();
            let hex = self.take_while(|c| c.is_ascii_hexdigit(), 4);
            if hex.len() != 4 {
                return Err(self.error("invalid unicode character escape"));
            }
            let cp =
                u32::from_str_radix(&hex, 16).map_err(|_| self.error("invalid unicode escape"))?;
            let ch = char::from_u32(cp).ok_or_else(|| self.error("invalid unicode codepoint"))?;
            return Ok(EDN::Char(ch));
        }

        let c = self
            .advance()
            .ok_or_else(|| self.error("expected character after \\"))?;
        Ok(EDN::Char(c))
    }

    fn parse_keyword(&mut self) -> Result<EDN, ParseError> {
        self.expect(':')?;
        let sym = self.read_symbol_string()?;
        let (ns, name) = split_namespace(&sym);
        Ok(EDN::Keyword(ns, name))
    }

    fn parse_symbol(&mut self) -> Result<EDN, ParseError> {
        let sym = self.read_symbol_string()?;

        match sym.as_str() {
            "nil" => Ok(EDN::Nil),
            "true" => Ok(EDN::Bool(true)),
            "false" => Ok(EDN::Bool(false)),
            _ => {
                let (ns, name) = split_namespace(&sym);
                Ok(EDN::Symbol(ns, name))
            }
        }
    }

    fn read_symbol_string(&mut self) -> Result<String, ParseError> {
        let mut s = String::new();

        if let Some(c) = self.peek() {
            if is_symbol_start(c) {
                s.push(c);
                self.advance();
            } else {
                return Err(self.error("invalid symbol start"));
            }
        }

        while let Some(c) = self.peek() {
            if is_symbol_char(c) {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if s.is_empty() {
            return Err(self.error("empty symbol"));
        }

        Ok(s)
    }

    fn parse_number(&mut self) -> Result<EDN, ParseError> {
        let start = self.offset;
        let mut s = String::new();

        if let Some(c @ ('+' | '-')) = self.peek() {
            s.push(c);
            self.advance();
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if s.len() == 1 && (s == "+" || s == "-") {
            if let Some(c) = self.peek() {
                if is_symbol_char(c) && !c.is_ascii_digit() {
                    self.offset = start;
                    return self.parse_symbol();
                }
            }
            if self.peek().is_none() || is_delimiter(self.peek().unwrap()) {
                return Ok(EDN::Symbol(None, s));
            }
        }

        let mut is_float = false;

        if self.peek() == Some('.') {
            if let Some(next) = self.remaining().chars().nth(1) {
                if next.is_ascii_digit() {
                    is_float = true;
                    s.push('.');
                    self.advance();
                    while let Some(c) = self.peek() {
                        if c.is_ascii_digit() {
                            s.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
            }
        }

        if let Some(c @ ('e' | 'E')) = self.peek() {
            is_float = true;
            s.push(c);
            self.advance();
            if let Some(c @ ('+' | '-')) = self.peek() {
                s.push(c);
                self.advance();
            }
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    s.push(c);
                    self.advance();
                } else {
                    break;
                }
            }
        }

        match self.peek() {
            Some('N') => {
                self.advance();
                Ok(EDN::BigInt(s))
            }
            Some('M') => {
                self.advance();
                Ok(EDN::Decimal(s))
            }
            _ => {
                if is_float {
                    let f: f64 = s
                        .parse()
                        .map_err(|_| self.error_at(start, self.offset - start, "invalid float"))?;
                    Ok(EDN::Float(f))
                } else {
                    let n: i64 = s.parse().map_err(|_| {
                        self.error_at(start, self.offset - start, "invalid integer")
                    })?;
                    Ok(EDN::Int(n))
                }
            }
        }
    }

    fn parse_list(&mut self) -> Result<EDN, ParseError> {
        self.expect('(')?;
        let items = self.parse_sequence(')')?;
        Ok(EDN::List(items))
    }

    fn parse_vector(&mut self) -> Result<EDN, ParseError> {
        self.expect('[')?;
        let items = self.parse_sequence(']')?;
        Ok(EDN::Vector(items))
    }

    fn parse_map(&mut self) -> Result<EDN, ParseError> {
        let start = self.offset;
        self.expect('{')?;
        let mut pairs = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some('}') {
                self.advance();
                break;
            }

            let key = self.parse()?;
            self.skip_whitespace_and_comments();

            if self.peek() == Some('}') {
                return Err(self.error_at(
                    start,
                    self.offset - start,
                    "map has odd number of elements",
                ));
            }

            let value = self.parse()?;
            pairs.push((key, value));
        }

        Ok(EDN::Map(pairs))
    }

    fn parse_set(&mut self) -> Result<EDN, ParseError> {
        self.expect('{')?;
        let items = self.parse_sequence('}')?;
        Ok(EDN::Set(items))
    }

    fn parse_sequence(&mut self, end: char) -> Result<Vec<EDN>, ParseError> {
        let mut items = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some(end) {
                self.advance();
                break;
            }

            items.push(self.parse()?);
        }

        Ok(items)
    }

    fn parse_dispatch(&mut self) -> Result<EDN, ParseError> {
        self.expect('#')?;

        match self.peek() {
            Some('{') => self.parse_set(),
            Some('_') => {
                self.advance();
                self.skip_whitespace_and_comments();
                self.parse()?;
                self.parse()
            }
            Some(_) => {
                let tag = self.read_symbol_string()?;
                self.skip_whitespace_and_comments();
                let value = self.parse()?;
                Ok(EDN::Tagged(tag, Box::new(value)))
            }
            None => Err(self.error("unexpected EOF after #")),
        }
    }

    fn take_while(&mut self, pred: impl Fn(char) -> bool, max: usize) -> String {
        let mut s = String::new();
        for _ in 0..max {
            if let Some(c) = self.peek() {
                if pred(c) {
                    s.push(c);
                    self.advance();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        s
    }
}

fn is_delimiter(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | '"' | ';' | ',') || c.is_whitespace()
}

fn is_symbol_start(c: char) -> bool {
    c.is_alphabetic()
        || matches!(
            c,
            '.' | '*' | '+' | '!' | '-' | '_' | '?' | '$' | '%' | '&' | '=' | '<' | '>'
        )
}

fn is_symbol_char(c: char) -> bool {
    is_symbol_start(c) || c.is_ascii_digit() || matches!(c, ':' | '#' | '/')
}

fn split_namespace(s: &str) -> (Option<String>, String) {
    if let Some(idx) = s.rfind('/') {
        if idx > 0 && idx < s.len() - 1 {
            return (Some(s[..idx].to_string()), s[idx + 1..].to_string());
        }
    }
    (None, s.to_string())
}

// ================================================================================================
// CONVENIENCE METHODS ============================================================================
// ================================================================================================

impl EDN {
    pub fn is_nil(&self) -> bool {
        matches!(self, EDN::Nil)
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            EDN::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            EDN::Int(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<f64> {
        match self {
            EDN::Float(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            EDN::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<(&Option<String>, &String)> {
        match self {
            EDN::Symbol(ns, name) => Some((ns, name)),
            _ => None,
        }
    }

    pub fn as_keyword(&self) -> Option<(&Option<String>, &String)> {
        match self {
            EDN::Keyword(ns, name) => Some((ns, name)),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<&[EDN]> {
        match self {
            EDN::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_vector(&self) -> Option<&[EDN]> {
        match self {
            EDN::Vector(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_map(&self) -> Option<&[(EDN, EDN)]> {
        match self {
            EDN::Map(m) => Some(m),
            _ => None,
        }
    }

    pub fn as_set(&self) -> Option<&[EDN]> {
        match self {
            EDN::Set(v) => Some(v),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> Result<EDN, ParseError> {
        Parser::new(s).parse()
    }

    fn parse_all(s: &str) -> Result<Vec<EDN>, ParseError> {
        Parser::new(s).parse_all()
    }

    #[test]
    fn test_nil() {
        assert_eq!(parse("nil").unwrap(), EDN::Nil);
    }

    #[test]
    fn test_bools() {
        assert_eq!(parse("true").unwrap(), EDN::Bool(true));
        assert_eq!(parse("false").unwrap(), EDN::Bool(false));
    }

    #[test]
    fn test_integers() {
        assert_eq!(parse("42").unwrap(), EDN::Int(42));
        assert_eq!(parse("-17").unwrap(), EDN::Int(-17));
        assert_eq!(parse("+5").unwrap(), EDN::Int(5));
        assert_eq!(parse("0").unwrap(), EDN::Int(0));
    }

    #[test]
    fn test_bigint() {
        assert_eq!(parse("42N").unwrap(), EDN::BigInt("42".to_string()));
    }

    #[test]
    fn test_floats() {
        assert_eq!(parse("3.14").unwrap(), EDN::Float(3.14));
        assert_eq!(parse("-2.5").unwrap(), EDN::Float(-2.5));
        assert_eq!(parse("1e10").unwrap(), EDN::Float(1e10));
        assert_eq!(parse("1.5e-3").unwrap(), EDN::Float(1.5e-3));
    }

    #[test]
    fn test_decimal() {
        assert_eq!(parse("3.14M").unwrap(), EDN::Decimal("3.14".to_string()));
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            parse(r#""hello""#).unwrap(),
            EDN::String("hello".to_string())
        );
        assert_eq!(
            parse(r#""hello\nworld""#).unwrap(),
            EDN::String("hello\nworld".to_string())
        );
        assert_eq!(
            parse(r#""tab\there""#).unwrap(),
            EDN::String("tab\there".to_string())
        );
        assert_eq!(
            parse(r#""quote\"here""#).unwrap(),
            EDN::String("quote\"here".to_string())
        );
    }

    #[test]
    fn test_chars() {
        assert_eq!(parse(r"\a").unwrap(), EDN::Char('a'));
        assert_eq!(parse(r"\newline").unwrap(), EDN::Char('\n'));
        assert_eq!(parse(r"\space").unwrap(), EDN::Char(' '));
        assert_eq!(parse(r"\tab").unwrap(), EDN::Char('\t'));
        assert_eq!(parse(r"\return").unwrap(), EDN::Char('\r'));
    }

    #[test]
    fn test_symbols() {
        assert_eq!(parse("foo").unwrap(), EDN::Symbol(None, "foo".to_string()));
        assert_eq!(
            parse("my.ns/bar").unwrap(),
            EDN::Symbol(Some("my.ns".to_string()), "bar".to_string())
        );
        assert_eq!(parse("+").unwrap(), EDN::Symbol(None, "+".to_string()));
        assert_eq!(parse("-").unwrap(), EDN::Symbol(None, "-".to_string()));
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            parse(":foo").unwrap(),
            EDN::Keyword(None, "foo".to_string())
        );
        assert_eq!(
            parse(":my.ns/bar").unwrap(),
            EDN::Keyword(Some("my.ns".to_string()), "bar".to_string())
        );
    }

    #[test]
    fn test_lists() {
        assert_eq!(parse("()").unwrap(), EDN::List(vec![]));
        assert_eq!(
            parse("(1 2 3)").unwrap(),
            EDN::List(vec![EDN::Int(1), EDN::Int(2), EDN::Int(3)])
        );
        assert_eq!(
            parse("(+ 1 2)").unwrap(),
            EDN::List(vec![
                EDN::Symbol(None, "+".to_string()),
                EDN::Int(1),
                EDN::Int(2)
            ])
        );
    }

    #[test]
    fn test_vectors() {
        assert_eq!(parse("[]").unwrap(), EDN::Vector(vec![]));
        assert_eq!(
            parse("[1 2 3]").unwrap(),
            EDN::Vector(vec![EDN::Int(1), EDN::Int(2), EDN::Int(3)])
        );
    }

    #[test]
    fn test_maps() {
        assert_eq!(parse("{}").unwrap(), EDN::Map(vec![]));
        assert_eq!(
            parse("{:a 1 :b 2}").unwrap(),
            EDN::Map(vec![
                (EDN::Keyword(None, "a".to_string()), EDN::Int(1)),
                (EDN::Keyword(None, "b".to_string()), EDN::Int(2)),
            ])
        );
    }

    #[test]
    fn test_sets() {
        assert_eq!(parse("#{}").unwrap(), EDN::Set(vec![]));
        assert_eq!(
            parse("#{1 2 3}").unwrap(),
            EDN::Set(vec![EDN::Int(1), EDN::Int(2), EDN::Int(3)])
        );
    }

    #[test]
    fn test_tagged() {
        assert_eq!(
            parse("#inst \"2024-01-01\"").unwrap(),
            EDN::Tagged(
                "inst".to_string(),
                Box::new(EDN::String("2024-01-01".to_string()))
            )
        );
    }

    #[test]
    fn test_discard() {
        assert_eq!(
            parse("#_ foo bar").unwrap(),
            EDN::Symbol(None, "bar".to_string())
        );
        assert_eq!(
            parse("[1 #_ 2 3]").unwrap(),
            EDN::Vector(vec![EDN::Int(1), EDN::Int(3)])
        );
    }

    #[test]
    fn test_comments() {
        assert_eq!(parse("; comment\n42").unwrap(), EDN::Int(42));
        assert_eq!(
            parse("[1 ; inline comment\n 2]").unwrap(),
            EDN::Vector(vec![EDN::Int(1), EDN::Int(2)])
        );
    }

    #[test]
    fn test_commas_as_whitespace() {
        assert_eq!(
            parse("[1, 2, 3]").unwrap(),
            EDN::Vector(vec![EDN::Int(1), EDN::Int(2), EDN::Int(3)])
        );
        assert_eq!(
            parse("{:a 1, :b 2}").unwrap(),
            EDN::Map(vec![
                (EDN::Keyword(None, "a".to_string()), EDN::Int(1)),
                (EDN::Keyword(None, "b".to_string()), EDN::Int(2)),
            ])
        );
    }

    #[test]
    fn test_nested() {
        let result = parse("(run* [q] (== q 1))").unwrap();
        assert!(matches!(result, EDN::List(_)));
        if let EDN::List(items) = result {
            assert_eq!(items.len(), 3);
            assert_eq!(items[0], EDN::Symbol(None, "run*".to_string()));
        }
    }

    #[test]
    fn test_display() {
        let edn = parse("[1 :foo \"bar\" (+ 1 2)]").unwrap();
        let s = edn.to_string();
        assert!(s.contains("1"));
        assert!(s.contains(":foo"));
        assert!(s.contains("\"bar\""));
    }

    #[test]
    fn test_parse_all() {
        let results = parse_all("1 2 3").unwrap();
        assert_eq!(results, vec![EDN::Int(1), EDN::Int(2), EDN::Int(3)]);
    }
}
