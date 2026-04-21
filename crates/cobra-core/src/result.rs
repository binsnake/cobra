
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CobraError {
    ParseError,
    NonLinearInput,
    TooManyVariables,
    NoReduction,
    VerificationFailed,
}

impl fmt::Display for CobraError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::ParseError => "parse error",
            Self::NonLinearInput => "non-linear input",
            Self::TooManyVariables => "too many variables",
            Self::NoReduction => "no reduction",
            Self::VerificationFailed => "verification failed",
        };
        f.write_str(name)
    }
}

#[derive(Clone, Debug, thiserror::Error)]
#[error("{code}: {message}")]
pub struct ErrorInfo {
    pub code: CobraError,
    pub message: String,
}

impl ErrorInfo {
    pub fn new(code: CobraError, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }
}

pub type Result<T> = std::result::Result<T, ErrorInfo>;

/// Short-circuit helper for producing errors: `Err(err(kind, "msg"))`.
pub fn err(code: CobraError, message: impl Into<String>) -> ErrorInfo {
    ErrorInfo::new(code, message)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        fn produce() -> Result<u32> {
            Err(err(CobraError::ParseError, "bad token '%'"))
        }
        let e = produce().unwrap_err();
        assert_eq!(e.code, CobraError::ParseError);
        assert_eq!(e.message, "bad token '%'");
        assert_eq!(e.to_string(), "parse error: bad token '%'");
    }

    #[test]
    fn question_mark_compiles() {
        fn inner() -> Result<u32> {
            let x: Result<u32> = Ok(7);
            let y = x?;
            Ok(y + 1)
        }
        assert_eq!(inner().unwrap(), 8);
    }
}
