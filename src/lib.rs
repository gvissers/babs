// Copyright, 2021, Gé Vissers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
