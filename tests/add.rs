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

