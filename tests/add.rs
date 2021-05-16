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

use babs::{UBigBin32, UBigDec32};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_add_assign_digit_binary()
{
    let mut n = UBigBin32::zero();
    n += 0x32;
    assert_eq!(format!("{:#x}", n), "0x32");

    let mut n = UBigBin32::from_str("0x12345678").unwrap();
    n += 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0x112345677");

    let mut n = UBigBin32::from_str("0xffffffffffffffff").unwrap();
    n += 1;
    assert_eq!(format!("{:#x}", n), "0x10000000000000000");
}

#[test]
fn test_add_assign_digit_decimal()
{
    let mut n = UBigDec32::zero();
    n += 101;
    assert_eq!(format!("{}", n), "101");

    let mut n = UBigDec32::zero();
    n += 2_000_000_000;
    assert_eq!(format!("{}", n), "2000000000");

    let mut n = UBigDec32::from_str("123456789").unwrap();
    n += 0xffffffff;
    assert_eq!(format!("{}", n), "4418424084");

    let mut n = UBigDec32::from_str("999999999999999999").unwrap();
    n += 1;
    assert_eq!(format!("{}", n), "1000000000000000000");
}

#[test]
fn test_add_digit_binary()
{
    let n = UBigBin32::zero() + 0x32;
    assert_eq!(format!("{:#x}", n), "0x32");

    let n = UBigBin32::from_str("0x12345678").unwrap() + 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0x112345677");

    let n = UBigBin32::from_str("0xffffffffffffffff").unwrap() + 1;
    assert_eq!(format!("{:#x}", n), "0x10000000000000000");
}

#[test]
fn test_add_digit_decimal()
{
    let n = UBigDec32::zero() + 101;
    assert_eq!(format!("{}", n), "101");

    let n = UBigDec32::zero() + 2_000_000_000;
    assert_eq!(format!("{}", n), "2000000000");

    let n = UBigDec32::from_str("123456789").unwrap() + 0xffffffff;
    assert_eq!(format!("{}", n), "4418424084");

    let n = UBigDec32::from_str("999999999999999999").unwrap() + 1;
    assert_eq!(format!("{}", n), "1000000000000000000");
}

#[test]
fn test_add_assign_big_binary()
{
    let mut n = UBigBin32::zero();
    n += UBigBin32::zero();
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0x12345678").unwrap();
    n += UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x99999999");

    let mut n = UBigBin32::from_str("0x1234567890abcdef").unwrap();
    n += UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567918111110");

    let mut n = UBigBin32::from_str("0x87654321").unwrap();
    n += UBigBin32::from_str("0x1234567890abcdef").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567918111110");

    let mut n = UBigBin32::from_str("0xffffffffffffffff").unwrap();
    n += UBigBin32::from_str("0xa").unwrap();
    assert_eq!(format!("{:#x}", n), "0x10000000000000009");
}

#[test]
fn test_add_assign_big_decimal()
{
    let mut n = UBigDec32::zero();
    n += UBigDec32::zero();
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("12345678").unwrap();
    n += UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "99999999");

    let mut n = UBigDec32::from_str("1234567890123456").unwrap();
    n += UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "1234567977777777");

    let mut n = UBigDec32::from_str("87654321").unwrap();
    n += UBigDec32::from_str("1234567890123456").unwrap();
    assert_eq!(format!("{}", n), "1234567977777777");

    let mut n = UBigDec32::from_str("999999999999999999").unwrap();
    n += UBigDec32::from_str("10").unwrap();
    assert_eq!(format!("{}", n), "1000000000000000009");
}

#[test]
fn test_add_big_binary()
{
    let n = UBigBin32::zero() + UBigBin32::zero();
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0x12345678").unwrap() + UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x99999999");

    let n = UBigBin32::from_str("0x1234567890abcdef").unwrap() + UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567918111110");

    let n = UBigBin32::from_str("0x87654321").unwrap() + UBigBin32::from_str("0x1234567890abcdef").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567918111110");

    let n = UBigBin32::from_str("0xffffffffffffffff").unwrap() + UBigBin32::from_str("0xa").unwrap();
    assert_eq!(format!("{:#x}", n), "0x10000000000000009");
}

#[test]
fn test_add_big_decimal()
{
    let n = UBigDec32::zero() + UBigDec32::zero();
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::from_str("12345678").unwrap() + UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "99999999");

    let n = UBigDec32::from_str("1234567890123456").unwrap() + UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "1234567977777777");

    let n = UBigDec32::from_str("87654321").unwrap() + UBigDec32::from_str("1234567890123456").unwrap();
    assert_eq!(format!("{}", n), "1234567977777777");

    let n = UBigDec32::from_str("999999999999999999").unwrap() + UBigDec32::from_str("10").unwrap();
    assert_eq!(format!("{}", n), "1000000000000000009");
}
