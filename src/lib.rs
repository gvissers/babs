// Clippy does not like Allman indentation.
#![allow(clippy::suspicious_else_formatting)]

mod digit;
mod result;
mod ubig;

pub use digit::{BinaryDigit, DecimalDigit};
pub use ubig::UBig;

pub type UBigBin<T> = UBig<BinaryDigit<T>>;
pub type UBigBin8 = UBigBin<u8>;
pub type UBigBin16 = UBigBin<u16>;
pub type UBigBin32 = UBigBin<u32>;
pub type UBigBin64 = UBigBin<u64>;

pub type UBigDec<T> = UBig<DecimalDigit<T>>;
pub type UBigDec8 = UBigDec<u8>;
pub type UBigDec16 = UBigDec<u16>;
pub type UBigDec32 = UBigDec<u32>;
pub type UBigDec64 = UBigDec<u64>;
