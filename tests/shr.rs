use babs::{UBigBin32, UBigDec32};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_shr_assign_binary()
{
    let mut n = UBigBin32::zero();
    n >>= 15;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n >>= 15;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n >>= 73;
    assert_eq!(format!("{:#x}", n), "0x38");

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n >>= 82;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
    n >>= 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffff");
}

#[test]
fn test_shr_binary()
{
    let n = UBigBin32::zero() >> 15;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() >> 15;
    assert_eq!(format!("{:#x}", n), "0xe3233f8e53c03e69");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() >> 73;
    assert_eq!(format!("{:#x}", n), "0x38");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() >> 82;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap() >> 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffff");
}
