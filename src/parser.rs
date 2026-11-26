use std::fmt;

use crate::syntax::{Declaration, Span, Term, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub col: usize,
    pub message: String,
}

impl ParseError {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            line: span.line,
            col: span.col,
            message: message.into(),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parse error at line {}, column {}: {}",
            self.line, self.col, self.message
        )
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Ident(String),
    Theorem,
    Lemma,
    Fn,
    Fst,
    Snd,
    Inl,
    Inr,
    Case,
    Of,
    Absurd,
    UnitKw,
    Not,
    Top,
    Bot,
    Lambda,
    Dot,
    Colon,
    Eq,
    Semi,
    Comma,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Arrow,
    FatArrow,
    Star,
    And,
    Plus,
    Or,
    Pipe,
    Tilde,
    Eof,
}

impl TokenKind {
    fn describe(&self) -> String {
        match self {
            TokenKind::Ident(s) => format!("identifier '{}'", s),
            TokenKind::Theorem => "'theorem'".to_string(),
            TokenKind::Lemma => "'lemma'".to_string(),
            TokenKind::Fn => "'fn'".to_string(),
            TokenKind::Fst => "'fst'".to_string(),
            TokenKind::Snd => "'snd'".to_string(),
            TokenKind::Inl => "'inl'".to_string(),
            TokenKind::Inr => "'inr'".to_string(),
            TokenKind::Case => "'case'".to_string(),
            TokenKind::Of => "'of'".to_string(),
            TokenKind::Absurd => "'absurd'".to_string(),
            TokenKind::UnitKw => "'unit'".to_string(),
            TokenKind::Not => "'not'".to_string(),
            TokenKind::Top => "'Top'".to_string(),
            TokenKind::Bot => "'Bot'".to_string(),
            TokenKind::Lambda => "'\\'".to_string(),
            TokenKind::Dot => "'.'".to_string(),
            TokenKind::Colon => "':'".to_string(),
            TokenKind::Eq => "'='".to_string(),
            TokenKind::Semi => "';'".to_string(),
            TokenKind::Comma => "','".to_string(),
            TokenKind::LParen => "'('".to_string(),
            TokenKind::RParen => "')'".to_string(),
            TokenKind::LBracket => "'['".to_string(),
            TokenKind::RBracket => "']'".to_string(),
            TokenKind::Arrow => "'->'".to_string(),
            TokenKind::FatArrow => "'=>'".to_string(),
            TokenKind::Star => "'*'".to_string(),
            TokenKind::And => "'/\\'".to_string(),
            TokenKind::Plus => "'+'".to_string(),
            TokenKind::Or => "'\\/'".to_string(),
            TokenKind::Pipe => "'|'".to_string(),
            TokenKind::Tilde => "'~'".to_string(),
            TokenKind::Eof => "end of input".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    span: Span,
}

struct Lexer {
    chars: Vec<char>,
    pos: usize,
    line: usize,
    col: usize,
}

impl Lexer {
    fn new(input: &str) -> Self {
        Self {
            chars: input.chars().collect(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_next(&self) -> Option<char> {
        self.chars.get(self.pos + 1).copied()
    }

    fn span(&self) -> Span {
        Span::new(self.line, self.col)
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.chars.get(self.pos).copied()?;
        self.pos += 1;
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else if ch != '\r' {
            self.col += 1;
        }
        Some(ch)
    }

    fn skip_line(&mut self) {
        while let Some(ch) = self.peek() {
            self.advance();
            if ch == '\n' {
                break;
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) -> Result<(), ParseError> {
        loop {
            while let Some(ch) = self.peek() {
                if ch.is_whitespace() {
                    self.advance();
                } else {
                    break;
                }
            }
            let Some(ch) = self.peek() else {
                return Ok(());
            };
            if ch == '-' && self.peek_next() == Some('-') {
                self.advance();
                self.advance();
                self.skip_line();
                continue;
            }
            if ch == '/' && self.peek_next() == Some('/') {
                self.advance();
                self.advance();
                self.skip_line();
                continue;
            }
            if ch == '/' && self.peek_next() == Some('*') {
                let start = self.span();
                self.advance();
                self.advance();
                let mut closed = false;
                while let Some(c) = self.peek() {
                    if c == '*' && self.peek_next() == Some('/') {
                        self.advance();
                        self.advance();
                        closed = true;
                        break;
                    }
                    self.advance();
                }
                if !closed {
                    return Err(ParseError::new(start, "unclosed block comment"));
                }
                continue;
            }
            return Ok(());
        }
    }

    fn read_ident(&mut self) -> String {
        let mut s = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'' {
                s.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    fn tokenize(&mut self) -> Result<Vec<Token>, ParseError> {
        let mut tokens = Vec::new();
        loop {
            self.skip_whitespace_and_comments()?;
            let span = self.span();
            let Some(ch) = self.peek() else {
                tokens.push(Token {
                    kind: TokenKind::Eof,
                    span,
                });
                return Ok(tokens);
            };
            let kind = if ch.is_ascii_alphabetic() || ch == '_' {
                let word = self.read_ident();
                match word.as_str() {
                    "theorem" => TokenKind::Theorem,
                    "lemma" => TokenKind::Lemma,
                    "fn" => TokenKind::Fn,
                    "fst" => TokenKind::Fst,
                    "snd" => TokenKind::Snd,
                    "inl" => TokenKind::Inl,
                    "inr" => TokenKind::Inr,
                    "case" => TokenKind::Case,
                    "of" => TokenKind::Of,
                    "absurd" => TokenKind::Absurd,
                    "unit" => TokenKind::UnitKw,
                    "not" => TokenKind::Not,
                    "Top" | "Unit" | "True" => TokenKind::Top,
                    "Bot" | "Void" | "False" => TokenKind::Bot,
                    _ => TokenKind::Ident(word),
                }
            } else {
                match ch {
                    '-' if self.peek_next() == Some('>') => {
                        self.advance();
                        self.advance();
                        TokenKind::Arrow
                    }
                    '=' if self.peek_next() == Some('>') => {
                        self.advance();
                        self.advance();
                        TokenKind::FatArrow
                    }
                    '/' if self.peek_next() == Some('\\') => {
                        self.advance();
                        self.advance();
                        TokenKind::And
                    }
                    '\\' if self.peek_next() == Some('/') => {
                        self.advance();
                        self.advance();
                        TokenKind::Or
                    }
                    '→' => {
                        self.advance();
                        TokenKind::Arrow
                    }
                    '∧' | '&' => {
                        self.advance();
                        TokenKind::And
                    }
                    '∨' => {
                        self.advance();
                        TokenKind::Or
                    }
                    'λ' | '\\' => {
                        self.advance();
                        TokenKind::Lambda
                    }
                    '¬' | '~' | '!' => {
                        self.advance();
                        TokenKind::Tilde
                    }
                    '.' => {
                        self.advance();
                        TokenKind::Dot
                    }
                    ':' => {
                        self.advance();
                        TokenKind::Colon
                    }
                    '=' => {
                        self.advance();
                        TokenKind::Eq
                    }
                    ';' => {
                        self.advance();
                        TokenKind::Semi
                    }
                    ',' => {
                        self.advance();
                        TokenKind::Comma
                    }
                    '(' => {
                        self.advance();
                        TokenKind::LParen
                    }
                    ')' => {
                        self.advance();
                        TokenKind::RParen
                    }
                    '[' => {
                        self.advance();
                        TokenKind::LBracket
                    }
                    ']' => {
                        self.advance();
                        TokenKind::RBracket
                    }
                    '*' => {
                        self.advance();
                        TokenKind::Star
                    }
                    '+' => {
                        self.advance();
                        TokenKind::Plus
                    }
                    '|' => {
                        self.advance();
                        TokenKind::Pipe
                    }
                    other => {
                        return Err(ParseError::new(
                            span,
                            format!("unexpected character '{}'", other),
                        ));
                    }
                }
            };
            tokens.push(Token { kind, span });
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn at_eof(&self) -> bool {
        matches!(self.current().kind, TokenKind::Eof)
    }

    fn bump(&mut self) -> Token {
        let tok = self.tokens[self.pos].clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, expected: &TokenKind) -> bool {
        if &self.current().kind == expected {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParseError> {
        if self.current().kind == expected {
            Ok(self.bump())
        } else {
            let cur = self.current();
            Err(ParseError::new(
                cur.span,
                format!("expected {}, found {}", expected.describe(), cur.kind.describe()),
            ))
        }
    }

    fn expect_ident(&mut self) -> Result<(String, Span), ParseError> {
        let cur = self.current().clone();
        match cur.kind {
            TokenKind::Ident(name) => {
                self.bump();
                Ok((name, cur.span))
            }
            other => Err(ParseError::new(
                cur.span,
                format!("expected identifier, found {}", other.describe()),
            )),
        }
    }

    fn error_here(&self, message: impl Into<String>) -> ParseError {
        let cur = self.current();
        ParseError::new(
            cur.span,
            format!("{}, found {}", message.into(), cur.kind.describe()),
        )
    }

    fn parse_type_expr(&mut self) -> Result<Type, ParseError> {
        self.parse_arrow()
    }

    fn parse_arrow(&mut self) -> Result<Type, ParseError> {
        let left = self.parse_sum()?;
        if self.eat(&TokenKind::Arrow) {
            let right = self.parse_arrow()?;
            Ok(Type::arrow(left, right))
        } else {
            Ok(left)
        }
    }

    fn parse_sum(&mut self) -> Result<Type, ParseError> {
        let mut acc = self.parse_prod()?;
        while self.eat(&TokenKind::Plus) || self.eat(&TokenKind::Or) {
            let rhs = self.parse_prod()?;
            acc = Type::sum(acc, rhs);
        }
        Ok(acc)
    }

    fn parse_prod(&mut self) -> Result<Type, ParseError> {
        let mut acc = self.parse_unary_ty()?;
        while self.eat(&TokenKind::Star) || self.eat(&TokenKind::And) {
            let rhs = self.parse_unary_ty()?;
            acc = Type::prod(acc, rhs);
        }
        Ok(acc)
    }

    fn parse_unary_ty(&mut self) -> Result<Type, ParseError> {
        if self.eat(&TokenKind::Tilde) || self.eat(&TokenKind::Not) {
            let inner = self.parse_unary_ty()?;
            Ok(Type::not(inner))
        } else {
            self.parse_atom_ty()
        }
    }

    fn parse_atom_ty(&mut self) -> Result<Type, ParseError> {
        match &self.current().kind {
            TokenKind::Top => {
                self.bump();
                Ok(Type::Top)
            }
            TokenKind::Bot => {
                self.bump();
                Ok(Type::Bot)
            }
            TokenKind::Ident(_) => {
                let (name, _) = self.expect_ident()?;
                Ok(Type::Atom(name))
            }
            TokenKind::LParen => {
                self.bump();
                let inner = self.parse_type_expr()?;
                self.expect(TokenKind::RParen)?;
                Ok(inner)
            }
            _ => Err(self.error_here("expected type")),
        }
    }

    fn parse_binder(&mut self) -> Result<(String, Option<Type>), ParseError> {
        if self.eat(&TokenKind::LParen) {
            let (name, _) = self.expect_ident()?;
            let ty = if self.eat(&TokenKind::Colon) {
                Some(self.parse_type_expr()?)
            } else {
                None
            };
            self.expect(TokenKind::RParen)?;
            Ok((name, ty))
        } else {
            let (name, _) = self.expect_ident()?;
            let ty = if self.eat(&TokenKind::Colon) {
                Some(self.parse_type_expr()?)
            } else {
                None
            };
            Ok((name, ty))
        }
    }

    fn starts_binder(&self) -> bool {
        matches!(self.current().kind, TokenKind::Ident(_) | TokenKind::LParen)
    }

    fn parse_term_expr(&mut self) -> Result<Term, ParseError> {
        if self.eat(&TokenKind::Lambda) || self.eat(&TokenKind::Fn) {
            if !self.starts_binder() {
                return Err(self.error_here("expected parameter after lambda"));
            }
            let mut binders = Vec::new();
            while self.starts_binder() {
                binders.push(self.parse_binder()?);
            }
            if !self.eat(&TokenKind::Dot) && !self.eat(&TokenKind::FatArrow) {
                return Err(self.error_here("expected '.' or '=>' after lambda parameters"));
            }
            let mut body = self.parse_term_expr()?;
            for (param, param_ty) in binders.into_iter().rev() {
                body = Term::lam(param, param_ty, body);
            }
            return Ok(body);
        }

        if self.eat(&TokenKind::Case) {
            let scrutinee = self.parse_term_expr()?;
            self.expect(TokenKind::Of)?;
            let _ = self.eat(&TokenKind::Pipe);
            self.expect(TokenKind::Inl)?;
            let (left_var, _) = self.expect_ident()?;
            self.expect(TokenKind::FatArrow)?;
            let left_body = self.parse_term_expr()?;
            self.expect(TokenKind::Pipe)?;
            self.expect(TokenKind::Inr)?;
            let (right_var, _) = self.expect_ident()?;
            self.expect(TokenKind::FatArrow)?;
            let right_body = self.parse_term_expr()?;
            return Ok(Term::Case {
                scrutinee: Box::new(scrutinee),
                left_var,
                left_body: Box::new(left_body),
                right_var,
                right_body: Box::new(right_body),
            });
        }

        self.parse_app()
    }

    fn starts_atom_term(&self) -> bool {
        matches!(
            self.current().kind,
            TokenKind::Ident(_) | TokenKind::UnitKw | TokenKind::LParen
        )
    }

    fn parse_app(&mut self) -> Result<Term, ParseError> {
        let mut acc = self.parse_prefix_term()?;
        while self.starts_atom_term() {
            let arg = self.parse_atom_term()?;
            acc = Term::app(acc, arg);
        }
        Ok(acc)
    }

    fn parse_prefix_term(&mut self) -> Result<Term, ParseError> {
        if self.eat(&TokenKind::Fst) {
            let inner = self.parse_atom_term()?;
            return Ok(Term::fst(inner));
        }
        if self.eat(&TokenKind::Snd) {
            let inner = self.parse_atom_term()?;
            return Ok(Term::snd(inner));
        }
        if self.eat(&TokenKind::Inl) {
            let inner = self.parse_atom_term()?;
            return Ok(Term::inl(inner));
        }
        if self.eat(&TokenKind::Inr) {
            let inner = self.parse_atom_term()?;
            return Ok(Term::inr(inner));
        }
        if self.eat(&TokenKind::Absurd) {
            let ty = if self.eat(&TokenKind::LBracket) {
                let t = self.parse_type_expr()?;
                self.expect(TokenKind::RBracket)?;
                Some(t)
            } else {
                None
            };
            let inner = self.parse_atom_term()?;
            return Ok(Term::absurd(inner, ty));
        }
        self.parse_atom_term()
    }

    fn parse_atom_term(&mut self) -> Result<Term, ParseError> {
        match &self.current().kind {
            TokenKind::Ident(_) => {
                let (name, _) = self.expect_ident()?;
                Ok(Term::Var(name))
            }
            TokenKind::UnitKw => {
                self.bump();
                Ok(Term::Unit)
            }
            TokenKind::LParen => {
                self.bump();
                if self.eat(&TokenKind::RParen) {
                    return Ok(Term::Unit);
                }
                let first = self.parse_term_expr()?;
                if self.eat(&TokenKind::Colon) {
                    let ty = self.parse_type_expr()?;
                    self.expect(TokenKind::RParen)?;
                    Ok(Term::ann(first, ty))
                } else if self.eat(&TokenKind::Comma) {
                    let second = self.parse_term_expr()?;
                    self.expect(TokenKind::RParen)?;
                    Ok(Term::pair(first, second))
                } else {
                    self.expect(TokenKind::RParen)?;
                    Ok(first)
                }
            }
            _ => Err(self.error_here("expected term")),
        }
    }

    fn parse_program(&mut self) -> Result<Vec<Declaration>, ParseError> {
        let mut decls = Vec::new();
        while !self.at_eof() {
            let span = self.current().span;
            if !self.eat(&TokenKind::Theorem) && !self.eat(&TokenKind::Lemma) {
                return Err(self.error_here("expected 'theorem' or 'lemma'"));
            }
            let (name, _) = self.expect_ident()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type_expr()?;
            self.expect(TokenKind::Eq)?;
            let proof = self.parse_term_expr()?;
            let _ = self.eat(&TokenKind::Semi);
            decls.push(Declaration {
                name,
                ty,
                proof,
                span,
            });
        }
        Ok(decls)
    }
}

pub fn parse_type(input: &str) -> Result<Type, ParseError> {
    let tokens = Lexer::new(input).tokenize()?;
    let mut parser = Parser::new(tokens);
    let ty = parser.parse_type_expr()?;
    if !parser.at_eof() {
        return Err(parser.error_here("unexpected trailing token in type"));
    }
    Ok(ty)
}

pub fn parse_term(input: &str) -> Result<Term, ParseError> {
    let tokens = Lexer::new(input).tokenize()?;
    let mut parser = Parser::new(tokens);
    let term = parser.parse_term_expr()?;
    if !parser.at_eof() {
        return Err(parser.error_here("unexpected trailing token in term"));
    }
    Ok(term)
}

pub fn parse_program(input: &str) -> Result<Vec<Declaration>, ParseError> {
    let tokens = Lexer::new(input).tokenize()?;
    let mut parser = Parser::new(tokens);
    parser.parse_program()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_precedence_and_associativity() {
        let ty = parse_type("A * B + C -> D -> E").unwrap();
        let expected = Type::arrow(
            Type::sum(
                Type::prod(Type::Atom("A".into()), Type::Atom("B".into())),
                Type::Atom("C".into()),
            ),
            Type::arrow(Type::Atom("D".into()), Type::Atom("E".into())),
        );
        assert_eq!(ty, expected);
        assert_eq!(ty.to_string(), "A * B + C -> D -> E");
        assert_eq!(parse_type(&ty.to_string()).unwrap(), ty);
    }

    #[test]
    fn negation_syntax_sugar() {
        let ty = parse_type("~A * ~B -> ¬(A + B)").unwrap();
        let expected = Type::arrow(
            Type::prod(
                Type::not(Type::Atom("A".into())),
                Type::not(Type::Atom("B".into())),
            ),
            Type::not(Type::sum(Type::Atom("A".into()), Type::Atom("B".into()))),
        );
        assert_eq!(ty, expected);
        assert_eq!(parse_type(&ty.to_string()).unwrap(), ty);
    }

    #[test]
    fn term_application_and_lambdas() {
        let t = parse_term("\\(f : A -> B) x. f x").unwrap();
        let expected = Term::lam(
            "f",
            Some(Type::arrow(
                Type::Atom("A".into()),
                Type::Atom("B".into()),
            )),
            Term::lam("x", None, Term::app(Term::var("f"), Term::var("x"))),
        );
        assert_eq!(t, expected);

        let left_app = parse_term("f x y").unwrap();
        assert_eq!(
            left_app,
            Term::app(Term::app(Term::var("f"), Term::var("x")), Term::var("y"))
        );

        let proj_app = parse_term("fst p a").unwrap();
        assert_eq!(
            proj_app,
            Term::app(Term::fst(Term::var("p")), Term::var("a"))
        );
    }

    #[test]
    fn program_with_comments_and_multiline() {
        let src = "-- line comment\ntheorem mp : A -> (A -> B) -> B =\n  \\a f. f a\n\nlemma unit_id : Top -> Top =\n  \\u. ()\n";
        let decls = parse_program(src).unwrap();
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "mp");
        assert_eq!(decls[1].name, "unit_id");
        assert_eq!(parse_program(&decls[0].to_string()).unwrap().len(), 1);
    }

    #[test]
    fn error_reporting_has_line_and_column() {
        let err = parse_type("A -> \n  (B * )").unwrap_err();
        assert_eq!(err.line, 2);
        assert_eq!(err.col, 8);

        let err2 = parse_program("theorem t : A -> A = \\x.\n  (x").unwrap_err();
        assert_eq!(err2.line, 2);
        assert_eq!(err2.col, 5);
    }
}
