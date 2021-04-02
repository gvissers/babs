use babs::{UBigBin8, UBigDec8, UBigBin32, UBigDec32};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_pow_binary()
{
    let n = UBigBin8::zero();
    let m = n.pow(0);
    assert_eq!(format!("{:#x}", m), "0x1");

    let n = UBigBin8::zero();
    let m = n.pow(13);
    assert_eq!(format!("{:#x}", m), "0x0");

    let n = UBigBin8::from_str("0xfedcba98").unwrap();
    let m = n.pow(1);
    assert_eq!(format!("{:#x}", m), "0xfedcba98");

    let n = UBigBin8::from_str("0xfedcba98").unwrap();
    let m = n.pow(2);
    assert_eq!(format!("{:#x}", m), "0xfdbac096dd413a40");

    let n = UBigBin8::from_str("0xfedcba98").unwrap();
    let m = n.pow(13);
    assert_eq!(format!("{:#x}", m), "0xf198d2747a110de9256ef6e6084ab7b9fd88abb07e0b7af71db30ef0f458076de8eb6ed7ffe5050e7715a6ddafedf18000000000");

    let n = UBigBin32::from_str("0xfedcba98").unwrap();
    let m = n.pow(13);
    assert_eq!(format!("{:#x}", m), "0xf198d2747a110de9256ef6e6084ab7b9fd88abb07e0b7af71db30ef0f458076de8eb6ed7ffe5050e7715a6ddafedf18000000000");

    let n = UBigBin32::from_str("0x1").unwrap();
    let m = n.pow(356);
    assert_eq!(format!("{:#x}", m), "0x1");

    let n = UBigBin32::from_str("0x2").unwrap();
    let m = n.pow(356);
    assert_eq!(format!("{:#x}", m), "0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
}

#[test]
fn test_pow_decimal()
{
    let n = UBigDec8::zero();
    let m = n.pow(0);
    assert_eq!(format!("{}", m), "1");

    let n = UBigDec8::zero();
    let m = n.pow(13);
    assert_eq!(format!("{}", m), "0");

    let n = UBigDec8::from_str("982282810").unwrap();
    let m = n.pow(1);
    assert_eq!(format!("{}", m), "982282810");

    let n = UBigDec8::from_str("982282810").unwrap();
    let m = n.pow(2);
    assert_eq!(format!("{}", m), "964879518821496100");

    let n = UBigDec8::from_str("982282810").unwrap();
    let m = n.pow(13);
    assert_eq!(format!("{}", m), "792638332352224578622119426724922794977683169682171995983750988396136915147220543547941320563348899948410000000000000");

    let n = UBigDec32::from_str("982282810").unwrap();
    let m = n.pow(13);
    assert_eq!(format!("{}", m), "792638332352224578622119426724922794977683169682171995983750988396136915147220543547941320563348899948410000000000000");

    let n = UBigDec32::from_str("1").unwrap();
    let m = n.pow(356);
    assert_eq!(format!("{}", m), "1");

    let n = UBigDec32::from_str("2").unwrap();
    let m = n.pow(356);
    assert_eq!(format!("{}", m), "146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936");
}
