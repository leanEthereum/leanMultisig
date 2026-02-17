use std::fmt;

// ── Trait-based API (used by stack_trace.rs) ──

#[derive(Debug)]
pub struct Styled<T> {
    value: T,
    prefix: String,
}

impl<T: fmt::Display> fmt::Display for Styled<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.prefix.is_empty() {
            write!(f, "{}", self.value)
        } else {
            write!(f, "{}{}\x1b[0m", self.prefix, self.value)
        }
    }
}

impl<T: fmt::Display> Styled<T> {
    fn push(mut self, code: &str) -> Self {
        if self.prefix.is_empty() {
            self.prefix = format!("\x1b[{code}m");
        } else {
            self.prefix.push_str(&format!("\x1b[{code}m"));
        }
        self
    }
}

pub trait Colorize: fmt::Display + Sized {
    fn red(self) -> Styled<Self> {
        styled(self).push("31")
    }
    fn green(self) -> Styled<Self> {
        styled(self).push("32")
    }
    fn blue(self) -> Styled<Self> {
        styled(self).push("34")
    }
    fn magenta(self) -> Styled<Self> {
        styled(self).push("35")
    }
    fn yellow(self) -> Styled<Self> {
        styled(self).push("33")
    }
    fn bold(self) -> Styled<Self> {
        styled(self).push("1")
    }
    fn dimmed(self) -> Styled<Self> {
        styled(self).push("2")
    }
}

impl<T: fmt::Display> Colorize for Styled<T> {
    fn red(self) -> Styled<Self> {
        styled(self).push("31")
    }
    fn green(self) -> Styled<Self> {
        styled(self).push("32")
    }
    fn blue(self) -> Styled<Self> {
        styled(self).push("34")
    }
    fn magenta(self) -> Styled<Self> {
        styled(self).push("35")
    }
    fn yellow(self) -> Styled<Self> {
        styled(self).push("33")
    }
    fn bold(self) -> Styled<Self> {
        styled(self).push("1")
    }
    fn dimmed(self) -> Styled<Self> {
        styled(self).push("2")
    }
}

impl Colorize for &str {}
impl Colorize for String {}

fn styled<T: fmt::Display>(value: T) -> Styled<T> {
    Styled {
        value,
        prefix: String::new(),
    }
}

// ── Constant-based API (used by benchmark.rs) ──

pub const R: &str = "\x1b[0m";
pub const B: &str = "\x1b[1m";
pub const D: &str = "\x1b[2m";
pub const GRN: &str = "\x1b[38;5;114m";
pub const RED: &str = "\x1b[38;5;167m";
pub const ORG: &str = "\x1b[38;5;215m";
pub const CYN: &str = "\x1b[38;5;117m";
pub const PUR: &str = "\x1b[38;5;141m";
pub const GRY: &str = "\x1b[38;5;242m";
pub const WHT: &str = "\x1b[38;5;252m";
pub const DRK: &str = "\x1b[38;5;238m";
