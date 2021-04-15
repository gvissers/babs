use babs::{UBigBin8, UBigDec8, UBigBin32, UBigDec32};
use std::str::FromStr;

#[test]
fn test_div_assign_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n /= 0x87;
    assert_eq!(format!("{:#x}", n), "0x1b6d2aba029e5998aa");

    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n /= 1;
    assert_eq!(format!("{:#x}", n), "0xe7691881761813f81a7");

    let mut n = UBigBin32::from_str("0x829ef171ac352f24a9dbb827c").unwrap();
    n /= 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0xf6b424a056a70a431");

    let mut n = UBigBin32::from_str("0x829ef171").unwrap();
    n /= 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x0");
}

#[test]
fn test_div_assign_decimal()
{
    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n /= 87;
    assert_eq!(format!("{}", n), "103473792906593638884");

    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n /= 1;
    assert_eq!(format!("{}", n), "9002219982873646582917");

    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n /= 123;
    assert_eq!(format!("{}", n), "73188780348566232381");

    let mut n = UBigDec32::from_str("93081309173747392873837475872").unwrap();
    n /= 91_829_892;
    assert_eq!(format!("{}", n), "1013627557938839706724");

    let mut n = UBigDec32::from_str("93081309173747392873837475872").unwrap();
    n /= 2_891_829_892;
    assert_eq!(format!("{}", n), "32187684839709580287");

    let mut n = UBigDec32::from_str("982198881").unwrap();
    n /= 982198882;
    assert_eq!(format!("{}", n), "0");
}

#[test]
#[should_panic]
fn test_div_assign_by_zero_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n /= 0;
}

#[test]
#[should_panic]
fn test_div_assign_by_zero_decimal()
{
    let mut n = UBigDec8::from_str("39103919881210219921").unwrap();
    n /= 0;
}

#[test]
fn test_div_binary()
{
    let n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() / 0x87;
    assert_eq!(format!("{:#x}", n), "0x1b6d2aba029e5998aa");

    let n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() / 1;
    assert_eq!(format!("{:#x}", n), "0xe7691881761813f81a7");

    let n = UBigBin32::from_str("0x829ef171ac352f24a9dbb827c").unwrap() / 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0xf6b424a056a70a431");

    let n = UBigBin32::from_str("0x829ef171").unwrap() / 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x0");
}

#[test]
fn test_div_decimal()
{
    let n = UBigDec8::from_str("9002219982873646582917").unwrap() / 87;
    assert_eq!(format!("{}", n), "103473792906593638884");

    let n = UBigDec8::from_str("9002219982873646582917").unwrap() / 1;
    assert_eq!(format!("{}", n), "9002219982873646582917");

    let n = UBigDec8::from_str("9002219982873646582917").unwrap() / 123;
    assert_eq!(format!("{}", n), "73188780348566232381");

    let n = UBigDec32::from_str("93081309173747392873837475872").unwrap() / 91_829_892;
    assert_eq!(format!("{}", n), "1013627557938839706724");

    let n = UBigDec32::from_str("93081309173747392873837475872").unwrap() / 2_891_829_892;
    assert_eq!(format!("{}", n), "32187684839709580287");

    let n = UBigDec32::from_str("982198881").unwrap() / 982198882;
    assert_eq!(format!("{}", n), "0");
}

#[test]
#[should_panic]
fn test_div_by_zero_binary()
{
    let _n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() / 0;
}

#[test]
#[should_panic]
fn test_div_by_zero_decimal()
{
    let _n = UBigDec8::from_str("39103919881210219921").unwrap() / 0;
}

