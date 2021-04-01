use babs::{UBigBin32, UBigDec32};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_sub_assign_digit_binary()
{
    let mut n = UBigBin32::from_str("0x32").unwrap();
    n -= 0;
    assert_eq!(format!("{:#x}", n), "0x32");

    let mut n = UBigBin32::from_str("0x112345677").unwrap();
    n -= 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0x12345678");

    let mut n = UBigBin32::from_str("0x10000000000000000").unwrap();
    n -= 1;
    assert_eq!(format!("{:#x}", n), "0xffffffffffffffff");
}

#[test]
#[should_panic]
fn test_sub_assign_digit_binary_underflow()
{
    let mut n = UBigBin32::from_str("0x32").unwrap();
    n -= 0x64;
}

#[test]
fn test_sub_assign_digit_decimal()
{
    let mut n = UBigDec32::from_str("101").unwrap();
    n -= 0;
    assert_eq!(format!("{}", n), "101");

    let mut n = UBigDec32::from_str("2000000000").unwrap();
    n -= 2_000_000_000;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("4418424084").unwrap();
    n -= 0xffffffff;
    assert_eq!(format!("{}", n), "123456789");

    let mut n = UBigDec32::from_str("1000000000000000000").unwrap();
    n -= 1;
    assert_eq!(format!("{}", n), "999999999999999999");
}

#[test]
#[should_panic]
fn test_sub_assign_digit_decimal_underflow()
{
    let mut n = UBigDec32::from_str("101").unwrap();
    n -= 1003;
}

#[test]
fn test_sub_digit_binary()
{
    let n = UBigBin32::from_str("0x32").unwrap() - 0;
    assert_eq!(format!("{:#x}", n), "0x32");

    let n = UBigBin32::from_str("0x112345677").unwrap() - 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0x12345678");

    let n = UBigBin32::from_str("0x10000000000000000").unwrap() - 1;
    assert_eq!(format!("{:#x}", n), "0xffffffffffffffff");
}

#[test]
#[should_panic]
fn test_sub_digit_binary_underflow()
{
    let _n = UBigBin32::from_str("0x32").unwrap() - 0x64;
}

#[test]
fn test_sub_digit_decimal()
{
    let n = UBigDec32::from_str("101").unwrap() - 0;
    assert_eq!(format!("{}", n), "101");

    let n = UBigDec32::from_str("2000000000").unwrap() - 2_000_000_000;
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::from_str("4418424084").unwrap() - 0xffffffff;
    assert_eq!(format!("{}", n), "123456789");

    let n = UBigDec32::from_str("1000000000000000000").unwrap() - 1;
    assert_eq!(format!("{}", n), "999999999999999999");
}

#[test]
#[should_panic]
fn test_sub_digit_decimal_underflow()
{
    let _n = UBigDec32::from_str("101").unwrap() - 1003;
}

#[test]
fn test_sub_assign_big_binary()
{
    let mut n = UBigBin32::zero();
    n -= UBigBin32::zero();
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0x99999999").unwrap();
    n -= UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x12345678");

    let mut n = UBigBin32::from_str("0x1234567918111110").unwrap();
    n -= UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567890abcdef");

    let mut n = UBigBin32::from_str("0x1234567918111110").unwrap();
    n -= UBigBin32::from_str("0x1234567890abcdef").unwrap();
    assert_eq!(format!("{:#x}", n), "0x87654321");

    let mut n = UBigBin32::from_str("0x10000000000000009").unwrap();
    n -= UBigBin32::from_str("0xa").unwrap();
    assert_eq!(format!("{:#x}", n), "0xffffffffffffffff");
}

#[test]
#[should_panic]
fn test_sub_assign_big_binary_underflow()
{
    let mut n = UBigBin32::from_str("0x1234567890123456").unwrap();
    n -= UBigBin32::from_str("0x1234567890123457").unwrap();
}

#[test]
fn test_sub_assign_big_decimal()
{
    let mut n = UBigDec32::zero();
    n -= UBigDec32::zero();
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("99999999").unwrap();
    n -= UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "12345678");

    let mut n = UBigDec32::from_str("1234567977777777").unwrap();
    n -= UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "1234567890123456");

    let mut n = UBigDec32::from_str("1234567977777777").unwrap();
    n -= UBigDec32::from_str("1234567890123456").unwrap();
    assert_eq!(format!("{}", n), "87654321");

    let mut n = UBigDec32::from_str("1000000000000000009").unwrap();
    n -= UBigDec32::from_str("10").unwrap();
    assert_eq!(format!("{}", n), "999999999999999999");
}

#[test]
#[should_panic]
fn test_sub_assign_big_decimal_underflow()
{
    let mut n = UBigBin32::from_str("123456789012345678").unwrap();
    n -= UBigBin32::from_str("123456789012345679").unwrap();
}

#[test]
fn test_sub_big_binary()
{
    let n = UBigBin32::zero() - UBigBin32::zero();
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0x99999999").unwrap() - UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x12345678");

    let n = UBigBin32::from_str("0x1234567918111110").unwrap() - UBigBin32::from_str("0x87654321").unwrap();
    assert_eq!(format!("{:#x}", n), "0x1234567890abcdef");

    let n = UBigBin32::from_str("0x1234567918111110").unwrap()
        - UBigBin32::from_str("0x1234567890abcdef").unwrap();
    assert_eq!(format!("{:#x}", n), "0x87654321");

    let n = UBigBin32::from_str("0x10000000000000009").unwrap() - UBigBin32::from_str("0xa").unwrap();
    assert_eq!(format!("{:#x}", n), "0xffffffffffffffff");
}

#[test]
#[should_panic]
fn test_sub_big_binary_underflow()
{
    let _n = UBigBin32::from_str("0x1234567890123456").unwrap()
        - UBigBin32::from_str("0x1234567890123457").unwrap();
}

#[test]
fn test_sub_big_decimal()
{
    let n = UBigDec32::zero() - UBigDec32::zero();
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::from_str("99999999").unwrap() - UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "12345678");

    let n = UBigDec32::from_str("1234567977777777").unwrap() - UBigDec32::from_str("87654321").unwrap();
    assert_eq!(format!("{}", n), "1234567890123456");

    let n = UBigDec32::from_str("1234567977777777").unwrap()
        - UBigDec32::from_str("1234567890123456").unwrap();
    assert_eq!(format!("{}", n), "87654321");

    let n = UBigDec32::from_str("1000000000000000009").unwrap() - UBigDec32::from_str("10").unwrap();
    assert_eq!(format!("{}", n), "999999999999999999");
}

#[test]
#[should_panic]
fn test_sub_big_decimal_underflow()
{
    let _n = UBigBin32::from_str("123456789012345678").unwrap()
        - UBigBin32::from_str("123456789012345679").unwrap();
}
