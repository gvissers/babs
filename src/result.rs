/// Enumeration for errors related to big integer arithmetic
#[derive(Debug, PartialEq)]
pub enum Error
{
    /// Invalid number denotation
    InvalidNumber
}

/// Result type alias with error type for big integer errors
pub type Result<T> = std::result::Result<T, Error>;
