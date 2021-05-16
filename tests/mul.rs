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

use babs::{UBigBin8, UBigDec8, UBigBin32, UBigDec32};
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

#[test]
fn test_mul_assign_big_binary()
{
    let mut n0 = UBigBin8::zero();
    let n1 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0x0");

    let mut n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::zero();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0x0");

    let mut n0 = UBigBin8::from_str("0xfedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0x121fa000a3723a58c00503ab15959929cefea12cd7a44a41");

    let mut n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xfedcba0987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0x121fa000a3723a58c00503ab15959929cefea12cd7a44a41");

    let mut n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xfedcba0987654321ffffffffffffffff").unwrap();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0x121fa000a3723a58d2395a23a6416719bba704bdce5dbf72012345f6789abcdf");

    let mut n0 = UBigBin8::from_str("0xffffffffffffffff55555555555555551234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xffffffffffffffff0123456789abcdeffedcba0987654321ffffffffffffffff3333333333333333").unwrap();
    n0 *= n1;
    assert_eq!(format!("{:#x}", n0), "0xfffffffffffffffe56789abcdf012345baf98ce7bc493272427386d5dc70a52112574b059c3de1497cf8bbd52d200871ae3a04f80d6f0ac4307826ad10596de8cd070dfe181ef293");
}

#[test]
fn test_mul_assign_big_decimal()
{
    let mut n0 = UBigDec8::zero();
    let n1 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "0");

    let mut n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::zero();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "0");

    let mut n0 = UBigDec8::from_str("9595959595950987654321").unwrap();
    let n1 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "1184686360037595433101200204970154951434993533413697789971041");

    let mut n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::from_str("9595959595950987654321").unwrap();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "1184686360037595433101200204970154951434993533413697789971041");

    let mut n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::from_str("982997489281903873893021388939802022890").unwrap();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "121357713718891939860849282139725158093481964939210303155948856078891849407690");

    let mut n0 = UBigDec8::from_str("121357713718891939860849282139725158093481964939210303155948856078891849407690").unwrap();
    let n1 = UBigDec8::from_str("93029402983198372396198718927039019381098178973717903190830971309179801978").unwrap();
    n0 *= n1;
    assert_eq!(format!("{}", n0), "11289835654674419874013163552036167512633752634305413123327030511599249897482191495952901109662410448300334897691877327195498875692661112537790790410820");
}

#[test]
fn test_mul_big_binary()
{
    let n0 = UBigBin8::zero();
    let n1 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::zero();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n0 = UBigBin8::from_str("0xfedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0x121fa000a3723a58c00503ab15959929cefea12cd7a44a41");

    let n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xfedcba0987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0x121fa000a3723a58c00503ab15959929cefea12cd7a44a41");

    let n0 = UBigBin8::from_str("0x1234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xfedcba0987654321ffffffffffffffff").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0x121fa000a3723a58d2395a23a6416719bba704bdce5dbf72012345f6789abcdf");

    let n0 = UBigBin8::from_str("0xffffffffffffffff55555555555555551234567890abcdeffedcba0987654321").unwrap();
    let n1 = UBigBin8::from_str("0xffffffffffffffff0123456789abcdeffedcba0987654321ffffffffffffffff3333333333333333").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{:#x}", n), "0xfffffffffffffffe56789abcdf012345baf98ce7bc493272427386d5dc70a52112574b059c3de1497cf8bbd52d200871ae3a04f80d6f0ac4307826ad10596de8cd070dfe181ef293");
}

#[test]
fn test_mul_big_decimal()
{
    let n0 = UBigDec8::zero();
    let n1 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "0");

    let n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::zero();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "0");

    let n0 = UBigDec8::from_str("9595959595950987654321").unwrap();
    let n1 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "1184686360037595433101200204970154951434993533413697789971041");

    let n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::from_str("9595959595950987654321").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "1184686360037595433101200204970154951434993533413697789971041");

    let n0 = UBigDec8::from_str("123456789098765432101234567890987654321").unwrap();
    let n1 = UBigDec8::from_str("982997489281903873893021388939802022890").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "121357713718891939860849282139725158093481964939210303155948856078891849407690");

    let n0 = UBigDec8::from_str("121357713718891939860849282139725158093481964939210303155948856078891849407690").unwrap();
    let n1 = UBigDec8::from_str("93029402983198372396198718927039019381098178973717903190830971309179801978").unwrap();
    let n = n0 * n1;
    assert_eq!(format!("{}", n), "11289835654674419874013163552036167512633752634305413123327030511599249897482191495952901109662410448300334897691877327195498875692661112537790790410820");
}
