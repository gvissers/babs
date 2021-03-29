// Clippy does not like Allman indentation.
#![allow(clippy::suspicious_else_formatting)]

mod digit;
mod result;
mod ubig;

pub use ubig::UBig;

pub type UBigBin<T> = UBig<digit::BinaryDigit<T>>;
pub type UBigBin32 = UBigBin<u32>;

pub type UBigDec<T> = UBig<digit::DecimalDigit<T>>;
pub type UBigDec32 = UBigDec<u32>;
