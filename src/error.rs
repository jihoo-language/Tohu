use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub span: Option<Span>,
    pub msg: String,
}

impl Error {
    pub fn at(span: Span, msg: impl Into<String>) -> Error {
        Error { span: Some(span), msg: msg.into() }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(s) => write!(f, "{}: {}", s, self.msg),
            None => write!(f, "{}", self.msg),
        }
    }
}
