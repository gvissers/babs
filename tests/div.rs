use babs::{UBigBin8, UBigDec8, UBigBin16, UBigBin32, UBigDec32, UBigBin64, UBigDec64};
use num_traits::{Zero, One};
use std::str::FromStr;

#[test]
fn test_div_assign_digit_binary()
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
fn test_div_assign_digit_decimal()
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
fn test_div_assign_by_digit_zero_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n /= 0;
}

#[test]
#[should_panic]
fn test_div_assign_by_digit_zero_decimal()
{
    let mut n = UBigDec8::from_str("39103919881210219921").unwrap();
    n /= 0;
}

#[test]
fn test_div_assign_big_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a798af534").unwrap();
    let m = UBigBin8::from_str("0x827df251fd1919f").unwrap();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0x1c5fb8fa79d9");

    let mut n = UBigBin16::from_str("0xe7691881761813f81a7").unwrap();
    let m = UBigBin16::one();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0xe7691881761813f81a7");

    let mut n = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin32::from_str("0x4df8982fd526aaac45").unwrap();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0x1acdba0651bcf9c842d70578f");

    let mut n = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827d").unwrap();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin64::from_str("0xe7691881761813f81a798af53482fd526aaac45829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin64::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827d").unwrap();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0x1c58a60ae96e6206a9c9394ea075e5988ff78dd9");

    let mut n = UBigBin64::from_str("0xe7691881761813f81a798af53482fd526aaac45829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin64::from_str("0xffffffffffffffffffffffffffffff").unwrap();
    n /= m;
    assert_eq!(format!("{:#x}", n), "0xe7691881761813f81a798af53482fe39d3c345ce41fc275fb8b");
}

#[test]
fn test_div_assign_big_decimal()
{
    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    let m = UBigDec8::from_str("937486293").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "9602508378086");

    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    let m = UBigDec8::one();
    n /= m;
    assert_eq!(format!("{}", n), "9002219982873646582917");

    let mut n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("9374894284708131986293").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "99287849655359182589853179");

    let mut n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("930813094274987073019737146173747392873837475873").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "1");

    let mut n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198881").unwrap();
    let m = UBigDec64::from_str("930813094274987073146173747392873837475872").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "10555209321988205425269567");

    let mut n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    let m = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198883").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    let m = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    n /= m;
    assert_eq!(format!("{}", n), "1");
}



#[test]
fn test_div_digit_binary()
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
fn test_div_digit_decimal()
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
fn test_div_by_digit_zero_binary()
{
    let _n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() / 0;
}

#[test]
#[should_panic]
fn test_div_by_digit_zero_decimal()
{
    let _n = UBigDec8::from_str("39103919881210219921").unwrap() / 0;
}

#[test]
fn test_div_big_binary()
{
    let n = UBigBin8::from_str("0xe7691881761813f81a798af534").unwrap();
    let m = UBigBin8::from_str("0x827df251fd1919f").unwrap();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0x1c5fb8fa79d9");

    let n = UBigBin16::from_str("0xe7691881761813f81a7").unwrap();
    let m = UBigBin16::one();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0xe7691881761813f81a7");

    let n = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin32::from_str("0x4df8982fd526aaac45").unwrap();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0x1acdba0651bcf9c842d70578f");

    let n = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin32::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827d").unwrap();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0x0");

    let n = UBigBin64::from_str("0xe7691881761813f81a798af53482fd526aaac45829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin64::from_str("0x829e82f453f2613f2092ff171ac352f24a9dbb827d").unwrap();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0x1c58a60ae96e6206a9c9394ea075e5988ff78dd9");

    let n = UBigBin64::from_str("0xe7691881761813f81a798af53482fd526aaac45829e82f453f2613f2092ff171ac352f24a9dbb827c").unwrap();
    let m = UBigBin64::from_str("0xffffffffffffffffffffffffffffff").unwrap();
    let q = n / m;
    assert_eq!(format!("{:#x}", q), "0xe7691881761813f81a798af53482fe39d3c345ce41fc275fb8b");
}

#[test]
fn test_div_big_decimal()
{
    let n = UBigDec8::from_str("9002219982873646582917").unwrap();
    let m = UBigDec8::from_str("937486293").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "9602508378086");

    let n = UBigDec8::from_str("9002219982873646582917").unwrap();
    let m = UBigDec8::one();
    let q = n / m;
    assert_eq!(format!("{}", q), "9002219982873646582917");

    let n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("9374894284708131986293").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "99287849655359182589853179");

    let n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("930813094274987073019737146173747392873837475873").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "0");

    let n = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let m = UBigDec32::from_str("930813094274987073019737146173747392873837475872").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "1");

    let n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198881").unwrap();
    let m = UBigDec64::from_str("930813094274987073146173747392873837475872").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "10555209321988205425269567");

    let n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    let m = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198883").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "0");

    let n = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    let m = UBigDec64::from_str("9824927049720029841301497204970192193810497583965928748296429198882").unwrap();
    let q = n / m;
    assert_eq!(format!("{}", q), "1");
}

#[test]
#[should_panic]
fn test_div_big_zero_binary()
{
    let n = UBigBin64::from_str("23740928407201749107429489127").unwrap();
    let m = UBigBin64::zero();
    let _q = n / m;
}

#[test]
#[should_panic]
fn test_div_big_zero_decimal()
{
    let n = UBigDec64::from_str("23740928407201749107429489127").unwrap();
    let m = UBigDec64::zero();
    let _q = n / m;
}

