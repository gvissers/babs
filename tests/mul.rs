use babs::{UBigBin32, UBigDec32};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_mul_assign_digit_binary()
{
    let mut n = UBigBin32::zero();
    n *= 0x12345678;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0xaabbccddeeff00998877665544332211").unwrap();
    n *= 0x12345678;
    assert_eq!(format!("{:#x}", n), "0xc241c3856bd10289c83f942dc760fa942ddadf8");

    let mut n = UBigBin32::from_str("0xffffffffffffffffffffffffffffffffffffffff").unwrap();
    n *= 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0xfffffffeffffffffffffffffffffffffffffffff00000001");
}

#[test]
fn test_mul_assign_digit_decimal()
{
    let mut n = UBigDec32::zero();
    n *= 12_345_678;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::zero();
    n *= 0xffffffff;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("11223344556677889900998877665544332211").unwrap();
    n *= 12_345_678;
    assert_eq!(format!("{}", n), "138559797979797978437184022020202020202034058");

    let mut n = UBigDec32::from_str("11223344556677889900998877665544332211").unwrap();
    n *= 0xffffffff;
    assert_eq!(format!("{}", n), "48203897811447810974400967405218855218860039245");

    let mut n = UBigDec32::from_str("9999999999999999999999999999999999999999999999").unwrap();
    n *= 999_999_999;
    assert_eq!(format!("{}", n), "9999999989999999999999999999999999999999999999000000001");

    let mut n = UBigDec32::from_str("9999999999999999999999999999999999999999999999").unwrap();
    n *= 0xffffffff;
    assert_eq!(format!("{}", n), "42949672949999999999999999999999999999999999995705032705");
}

#[test]
fn test_mul_digit_binary()
{
    let n = UBigBin32::zero() * 0x12345678;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0xaabbccddeeff00998877665544332211").unwrap() * 0x12345678;
    assert_eq!(format!("{:#x}", n), "0xc241c3856bd10289c83f942dc760fa942ddadf8");

    let n = UBigBin32::from_str("0xffffffffffffffffffffffffffffffffffffffff").unwrap() * 0xffffffff;
    assert_eq!(format!("{:#x}", n), "0xfffffffeffffffffffffffffffffffffffffffff00000001");
}

#[test]
fn test_mul_digit_decimal()
{
    let n = UBigDec32::zero() * 12_345_678;
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::zero() * 0xffffffff;
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::from_str("11223344556677889900998877665544332211").unwrap() * 12_345_678;
    assert_eq!(format!("{}", n), "138559797979797978437184022020202020202034058");

    let n = UBigDec32::from_str("11223344556677889900998877665544332211").unwrap() *  0xffffffff;
    assert_eq!(format!("{}", n), "48203897811447810974400967405218855218860039245");

    let n = UBigDec32::from_str("9999999999999999999999999999999999999999999999").unwrap() *  999_999_999;
    assert_eq!(format!("{}", n), "9999999989999999999999999999999999999999999999000000001");

    let n = UBigDec32::from_str("9999999999999999999999999999999999999999999999").unwrap() * 0xffffffff;
    assert_eq!(format!("{}", n), "42949672949999999999999999999999999999999999995705032705");
}
