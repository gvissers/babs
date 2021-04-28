use babs::{UBigBin32, UBigBin64, UBigDec32, UBigDec64};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_shl_assign_binary()
{
    let mut n = UBigBin32::zero();
    n <<= 15;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n <<= 15;
    assert_eq!(format!("{:#x}", n), "0x38c8cfe394f00f9a68990000");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n <<= 73;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69a264000000000000000000");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n <<= 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let mut n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
    n <<= 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000");

    let mut n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap();
    n <<= 73;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69a264000000000000000000");

    let mut n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
    n <<= 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000");

    let mut n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
    n <<= 0;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffffffffffffffffffffffffffffff");
}

#[test]
fn test_shl_assign_decimal()
{
    let mut n = UBigDec32::zero();
    n <<= 15;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("71919437299019348132").unwrap();
    n <<= 15;
    assert_eq!(format!("{}", n), "2356656121414265999589376");

    let mut n = UBigDec32::from_str("71919437299019348132").unwrap();
    n <<= 73;
    assert_eq!(format!("{}", n), "679259880335467951013695731362983516831744");

    let mut n = UBigDec32::from_str("71919437299019348132").unwrap();
    n <<= 0;
    assert_eq!(format!("{}", n), "71919437299019348132");

    let mut n = UBigDec32::from_str("999999999999999999999999999999999999999").unwrap();
    n <<= 128;
    assert_eq!(format!("{}", n), "340282366920938463463374607431768211455659717633079061536536625392568231788544");

    let mut n = UBigDec64::from_str("71919437299019348132").unwrap();
    n <<= 73;
    assert_eq!(format!("{}", n), "679259880335467951013695731362983516831744");

    let mut n = UBigDec64::from_str("71919437299019348132").unwrap();
    n <<= 0;
    assert_eq!(format!("{}", n), "71919437299019348132");

    let mut n = UBigDec64::from_str("999999999999999999999999999999999999999").unwrap();
    n <<= 128;
    assert_eq!(format!("{}", n), "340282366920938463463374607431768211455659717633079061536536625392568231788544");
}

#[test]
fn test_shl_binary()
{
    let n = UBigBin32::zero() << 15;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() << 15;
    assert_eq!(format!("{:#x}", n), "0x38c8cfe394f00f9a68990000");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() << 73;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69a264000000000000000000");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() << 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap() << 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000");

    let n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap() << 73;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69a264000000000000000000");

    let n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap() << 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap() << 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000");
}

#[test]
fn test_shl_decimal()
{
    let n = UBigDec32::zero() << 15;
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec32::from_str("71919437299019348132").unwrap() << 15;
    assert_eq!(format!("{}", n), "2356656121414265999589376");

    let n = UBigDec32::from_str("71919437299019348132").unwrap() << 73;
    assert_eq!(format!("{}", n), "679259880335467951013695731362983516831744");

    let n = UBigDec32::from_str("71919437299019348132").unwrap() << 0;
    assert_eq!(format!("{}", n), "71919437299019348132");

    let n = UBigDec32::from_str("999999999999999999999999999999999999999").unwrap() << 128;
    assert_eq!(format!("{}", n), "340282366920938463463374607431768211455659717633079061536536625392568231788544");

    let n = UBigDec64::from_str("71919437299019348132").unwrap() << 73;
    assert_eq!(format!("{}", n), "679259880335467951013695731362983516831744");

    let n = UBigDec64::from_str("71919437299019348132").unwrap() << 0;
    assert_eq!(format!("{}", n), "71919437299019348132");

    let n = UBigDec64::from_str("999999999999999999999999999999999999999").unwrap() << 128;
    assert_eq!(format!("{}", n), "340282366920938463463374607431768211455659717633079061536536625392568231788544");
}
