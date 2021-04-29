use babs::{UBigBin8, UBigDec8, UBigBin16, UBigDec16, UBigBin32, UBigDec32, UBigBin64, UBigDec64};
use num_traits::Zero;
use std::str::FromStr;

#[test]
fn test_rem_assign_digit_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n %= 0x87;
    assert_eq!(format!("{:#x}", n), "0x1");

    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n %= 1;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin16::from_str("0x3275ea9937d3dfe1543def144aaacf24").unwrap();
    n %= 0xf365;
    assert_eq!(format!("{:#x}", n), "0xdd93");

    let mut n = UBigBin32::from_str("0x829ef171ac352f24a9dbb827c").unwrap();
    n %= 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x7acf340b");

    let mut n = UBigBin32::from_str("0x829ef171").unwrap();
    n %= 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x829ef171");

    let mut n = UBigBin64::from_str("0x829ef171f5353cf273828fd667372fd6242ade1983ddfffe").unwrap();
    n %= 0x81fe4178465fd736;
    assert_eq!(format!("{:#x}", n), "0x6e5c25b8c68d5924");
}

#[test]
fn test_rem_assign_digit_decimal()
{
    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n %= 87;
    assert_eq!(format!("{}", n), "9");

    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n %= 1;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec8::from_str("9002219982873646582917").unwrap();
    n %= 123;
    assert_eq!(format!("{}", n), "54");

    let mut n = UBigDec16::from_str("90022199828736465829179002219982873646582917").unwrap();
    n %= 8_345;
    assert_eq!(format!("{}", n), "5572");

    let mut n = UBigDec32::from_str("93081309173747392873837475872").unwrap();
    n %= 91_829_892;
    assert_eq!(format!("{}", n), "60882064");

    let mut n = UBigDec32::from_str("93081309173747392873837475872").unwrap();
    n %= 2_891_829_892;
    assert_eq!(format!("{}", n), "1116936868");

    let mut n = UBigDec32::from_str("982198881").unwrap();
    n %= 982_198_882;
    assert_eq!(format!("{}", n), "982198881");

    let mut n = UBigDec64::from_str("498274927462984759874294867203710386146272569189313981").unwrap();
    n %= 3_958_234_847_986_999_123;
    assert_eq!(format!("{}", n), "864138130113784515");
}

#[test]
#[should_panic]
fn test_rem_assign_by_digit_zero_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n %= 0;
}

#[test]
#[should_panic]
fn test_rem_assign_by_digit_zero_decimal()
{
    let mut n = UBigDec8::from_str("39103919881210219921").unwrap();
    n %= 0;
}

#[test]
fn test_rem_assign_big_binary()
{
    let mut n = UBigBin8::from_str("0x272fddae3514e1414ffe52717dfe717").unwrap();
    let m = UBigBin8::from_str("0xffe72718933fe9").unwrap();
    n %= m;
    assert_eq!(format!("{:#x}", n), "0xa612ddc004b82c");

    let mut n = UBigBin16::from_str("0x30177230ab15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin16::from_str("0x3728289281").unwrap();
    n %= m;
    assert_eq!(format!("{:#x}", n), "0x0");

    let mut n = UBigBin32::from_str("0x30177230a30177230ab15e5d8ae22f6ab1e8ed7db15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin32::from_str("0x368dff2535ddf342462efefff34").unwrap();
    n %= m;
    assert_eq!(format!("{:#x}", n), "0x82046ee442d49005bc6bb70529");

    let mut n = UBigBin64::from_str("0x30177230a30177230ab15e6d8ae22f6ab1e8ed7db15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin64::from_str("0x368dff2535d4676dfefe646efdf342552efefff34").unwrap();
    n %= m;
    assert_eq!(format!("{:#x}", n), "0xbb68f67da829880d3695b52744a1227fcf93a95d");
}

#[test]
fn test_rem_assign_big_decimal()
{
    let mut n = UBigDec8::from_str("7849374978203198420749827429").unwrap();
    let m = UBigDec8::from_str("274097309742780").unwrap();
    n %= m;
    assert_eq!(format!("{}", n), "147172302973209");

    let mut n = UBigDec16::from_str("77427309730270207042742749648729740935793246297832").unwrap();
    let m = UBigDec16::from_str("972498704274092492174970279").unwrap();
    n %= m;
    assert_eq!(format!("{}", n), "95061865451716395454014970");

    let mut n = UBigDec32::from_str("457787921314029600398699209789811884151080151838812560337357067840").unwrap();
    let m = UBigDec32::from_str("48274807097205970972097520").unwrap();
    n %= m;
    assert_eq!(format!("{}", n), "0");

    let mut n = UBigDec64::from_str("409274097205720582757338649279470129742085692846502857029472095729856928").unwrap();
    let m = UBigDec64::from_str("924874928740274085620847057805692759326592").unwrap();
    n %= m;
    assert_eq!(format!("{}", n), "579494661511233909925933152107839265085216");
}

#[test]
#[should_panic]
fn test_rem_assign_by_big_zero_binary()
{
    let mut n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap();
    n %= UBigBin8::zero();
}

#[test]
#[should_panic]
fn test_rem_assign_by_big_zero_decimal()
{
    let mut n = UBigDec8::from_str("39103919881210219921").unwrap();
    n %= UBigDec8::zero();
}


#[test]
fn test_rem_digit_binary()
{
    let n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() % 0x87;
    assert_eq!(format!("{:#x}", n), "0x1");

    let n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() % 1;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin16::from_str("0x3275ea9937d3dfe1543def144aaacf24").unwrap() % 0xf365;
    assert_eq!(format!("{:#x}", n), "0xdd93");

    let n = UBigBin32::from_str("0x829ef171ac352f24a9dbb827c").unwrap() % 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x7acf340b");

    let n = UBigBin32::from_str("0x829ef171").unwrap() % 0x878afe41;
    assert_eq!(format!("{:#x}", n), "0x829ef171");

    let n = UBigBin64::from_str("0x829ef171f5353cf273828fd667372fd6242ade1983ddfffe").unwrap() % 0x81fe4178465fd736;
    assert_eq!(format!("{:#x}", n), "0x6e5c25b8c68d5924");
}

#[test]
fn test_rem_digit_decimal()
{
    let n = UBigDec8::from_str("9002219982873646582917").unwrap() % 87;
    assert_eq!(format!("{}", n), "9");

    let n = UBigDec8::from_str("9002219982873646582917").unwrap() % 1;
    assert_eq!(format!("{}", n), "0");

    let n = UBigDec8::from_str("9002219982873646582917").unwrap() % 123;
    assert_eq!(format!("{}", n), "54");

    let n = UBigDec16::from_str("90022199828736465829179002219982873646582917").unwrap() % 8_345;
    assert_eq!(format!("{}", n), "5572");

    let n = UBigDec32::from_str("93081309173747392873837475872").unwrap() % 91_829_892;
    assert_eq!(format!("{}", n), "60882064");

    let n = UBigDec32::from_str("93081309173747392873837475872").unwrap() % 2_891_829_892;
    assert_eq!(format!("{}", n), "1116936868");

    let n = UBigDec32::from_str("982198881").unwrap() % 982_198_882;
    assert_eq!(format!("{}", n), "982198881");

    let n = UBigDec64::from_str("498274927462984759874294867203710386146272569189313981").unwrap() % 3_958_234_847_986_999_123;
    assert_eq!(format!("{}", n), "864138130113784515");
}

#[test]
#[should_panic]
fn test_rem_by_digit_zero_binary()
{
    let _n = UBigBin8::from_str("0xe7691881761813f81a7").unwrap() % 0;
}

#[test]
#[should_panic]
fn test_rem_by_digit_zero_decimal()
{
    let _n = UBigDec8::from_str("39103919881210219921").unwrap() % 0;
}

#[test]
fn test_rem_big_binary()
{
    let n = UBigBin8::from_str("0x272fddae3514e1414ffe52717dfe717").unwrap();
    let m = UBigBin8::from_str("0xffe72718933fe9").unwrap();
    let r = n % m;
    assert_eq!(format!("{:#x}", r), "0xa612ddc004b82c");

    let n = UBigBin16::from_str("0x30177230ab15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin16::from_str("0x3728289281").unwrap();
    let r = n % m;
    assert_eq!(format!("{:#x}", r), "0x0");

    let n = UBigBin32::from_str("0x30177230a30177230ab15e5d8ae22f6ab1e8ed7db15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin32::from_str("0x368dff2535ddf342462efefff34").unwrap();
    let r = n % m;
    assert_eq!(format!("{:#x}", r), "0x82046ee442d49005bc6bb70529");

    let n = UBigBin64::from_str("0x30177230a30177230ab15e6d8ae22f6ab1e8ed7db15e5d8ae22f6ab1e8ed7d").unwrap();
    let m = UBigBin64::from_str("0x368dff2535d4676dfefe646efdf342552efefff34").unwrap();
    let r = n % m;
    assert_eq!(format!("{:#x}", r), "0xbb68f67da829880d3695b52744a1227fcf93a95d");
}

#[test]
fn test_rem_big_decimal()
{
    let n = UBigDec8::from_str("7849374978203198420749827429").unwrap();
    let m = UBigDec8::from_str("274097309742780").unwrap();
    let r = n % m;
    assert_eq!(format!("{}", r), "147172302973209");

    let n = UBigDec16::from_str("77427309730270207042742749648729740935793246297832").unwrap();
    let m = UBigDec16::from_str("972498704274092492174970279").unwrap();
    let r = n % m;
    assert_eq!(format!("{}", r), "95061865451716395454014970");

    let n = UBigDec32::from_str("457787921314029600398699209789811884151080151838812560337357067840").unwrap();
    let m = UBigDec32::from_str("48274807097205970972097520").unwrap();
    let r = n % m;
    assert_eq!(format!("{}", r), "0");

    let n = UBigDec64::from_str("409274097205720582757338649279470129742085692846502857029472095729856928").unwrap();
    let m = UBigDec64::from_str("924874928740274085620847057805692759326592").unwrap();
    let r = n % m;
    assert_eq!(format!("{}", r), "579494661511233909925933152107839265085216");
}

#[test]
#[should_panic]
fn test_rem_by_big_zero_binary()
{
    let _n = UBigBin32::from_str("0xe7691881761813f81a7").unwrap() % UBigBin32::zero();
}

#[test]
#[should_panic]
fn test_rem_by_big_zero_decimal()
{
    let _n = UBigDec64::from_str("39103919881210219921").unwrap() % UBigDec64::zero();
}

