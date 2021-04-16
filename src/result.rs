/// Enumeration for errors related to big integer arithmetic
#[derive(Debug, PartialEq)]
pub enum Error
{
    /// Invalid number denotation
    InvalidNumber,
    /// Underflow when subtracting big numbers
    Underflow,
    /// Attempt to divide by zero
    DivisionByZero,
    /// Not enough space to store a result
    NoSpace
}

impl std::fmt::Display for Error
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        match self
        {
            Error::InvalidNumber  => write!(f, "Invalid number"),
            Error::Underflow      => write!(f, "Underflow"),
            Error::DivisionByZero => write!(f, "Division by zero"),
            Error::NoSpace        => write!(f, "Not enough space to store the result")
        }
    }
}

/// Result type alias with error type for big integer errors
pub type Result<T> = std::result::Result<T, Error>;
