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

use babs::{UBigBin8, UBigBin32, UBigDec8, UBigDec32};
use std::str::FromStr;

#[test]
fn test_eq()
{
    assert!(UBigBin8::from_str("0x0").unwrap() == UBigBin8::from_str("0x00").unwrap());
    assert!(UBigBin8::from_str("0x1").unwrap() == UBigBin8::from_str("0x01").unwrap());
    assert!(UBigBin8::from_str("0x0").unwrap() != UBigBin8::from_str("0x01").unwrap());
    assert!(UBigBin8::from_str("0x123456789abcdef").unwrap() == UBigBin8::from_str("0x00000123456789abcdef").unwrap());
    assert!(UBigBin8::from_str("0x123456789abcdef").unwrap() != UBigBin8::from_str("0x123456789abcdef0").unwrap());

    assert!(UBigBin32::from_str("0x0").unwrap() == UBigBin32::from_str("0x00").unwrap());
    assert!(UBigBin32::from_str("0x1").unwrap() == UBigBin32::from_str("0x01").unwrap());
    assert!(UBigBin32::from_str("0x0").unwrap() != UBigBin32::from_str("0x01").unwrap());
    assert!(UBigBin32::from_str("0x123456789abcdef").unwrap() == UBigBin32::from_str("0x00000123456789abcdef").unwrap());
    assert!(UBigBin32::from_str("0x123456789abcdef").unwrap() != UBigBin32::from_str("0x123456789abcdef0").unwrap());

    assert!(UBigDec8::from_str("0").unwrap() == UBigDec8::from_str("00").unwrap());
    assert!(UBigDec8::from_str("1").unwrap() == UBigDec8::from_str("01").unwrap());
    assert!(UBigDec8::from_str("0").unwrap() != UBigDec8::from_str("01").unwrap());
    assert!(UBigDec8::from_str("1234567890987654321").unwrap() == UBigDec8::from_str("000001234567890987654321").unwrap());
    assert!(UBigDec8::from_str("1234567890987654321").unwrap() != UBigDec8::from_str("12345678909876543210").unwrap());

    assert!(UBigDec32::from_str("0").unwrap() == UBigDec32::from_str("00").unwrap());
    assert!(UBigDec32::from_str("1").unwrap() == UBigDec32::from_str("01").unwrap());
    assert!(UBigDec32::from_str("0").unwrap() != UBigDec32::from_str("01").unwrap());
    assert!(UBigDec32::from_str("1234567890987654321").unwrap() == UBigDec32::from_str("000001234567890987654321").unwrap());
    assert!(UBigDec32::from_str("1234567890987654321").unwrap() != UBigDec32::from_str("12345678909876543210").unwrap());
}

#[test]
fn test_cmp()
{
    assert!(UBigBin8::from_str("0x0").unwrap() < UBigBin8::from_str("0x1").unwrap());
    assert!(UBigBin8::from_str("0x0").unwrap() <= UBigBin8::from_str("0x1").unwrap());
    assert!(UBigBin8::from_str("0x1").unwrap() > UBigBin8::from_str("0x0").unwrap());
    assert!(UBigBin8::from_str("0x1").unwrap() < UBigBin8::from_str("0x2").unwrap());
    assert!(UBigBin8::from_str("0x1").unwrap() <= UBigBin8::from_str("0x2").unwrap());
    assert!(UBigBin8::from_str("0x2").unwrap() > UBigBin8::from_str("0x1").unwrap());
    assert!(UBigBin8::from_str("0x00ff").unwrap() < UBigBin8::from_str("0x0100").unwrap());
    assert!(UBigBin8::from_str("0x1001").unwrap() > UBigBin8::from_str("0x0100").unwrap());

    assert!(UBigBin32::from_str("0x0").unwrap() < UBigBin32::from_str("0x1").unwrap());
    assert!(UBigBin32::from_str("0x0").unwrap() <= UBigBin32::from_str("0x1").unwrap());
    assert!(UBigBin32::from_str("0x1").unwrap() > UBigBin32::from_str("0x0").unwrap());
    assert!(UBigBin32::from_str("0x1").unwrap() < UBigBin32::from_str("0x2").unwrap());
    assert!(UBigBin32::from_str("0x1").unwrap() <= UBigBin32::from_str("0x2").unwrap());
    assert!(UBigBin32::from_str("0x2").unwrap() > UBigBin32::from_str("0x1").unwrap());
    assert!(UBigBin32::from_str("0x00000000ffffffff").unwrap() < UBigBin32::from_str("0x0000000100000000").unwrap());
    assert!(UBigBin32::from_str("0x0000000100000001").unwrap() > UBigBin32::from_str("0x0000000100000000").unwrap());

    assert!(UBigDec8::from_str("0").unwrap() < UBigDec8::from_str("1").unwrap());
    assert!(UBigDec8::from_str("0").unwrap() <= UBigDec8::from_str("1").unwrap());
    assert!(UBigDec8::from_str("1").unwrap() > UBigDec8::from_str("0").unwrap());
    assert!(UBigDec8::from_str("1").unwrap() < UBigDec8::from_str("2").unwrap());
    assert!(UBigDec8::from_str("1").unwrap() <= UBigDec8::from_str("2").unwrap());
    assert!(UBigDec8::from_str("2").unwrap() > UBigDec8::from_str("1").unwrap());
    assert!(UBigDec8::from_str("0099").unwrap() < UBigDec8::from_str("0100").unwrap());
    assert!(UBigDec8::from_str("1001").unwrap() > UBigDec8::from_str("0100").unwrap());

    assert!(UBigDec32::from_str("0").unwrap() < UBigDec32::from_str("0x1").unwrap());
    assert!(UBigDec32::from_str("0").unwrap() <= UBigDec32::from_str("0x1").unwrap());
    assert!(UBigDec32::from_str("1").unwrap() > UBigDec32::from_str("0x0").unwrap());
    assert!(UBigDec32::from_str("1").unwrap() < UBigDec32::from_str("0x2").unwrap());
    assert!(UBigDec32::from_str("1").unwrap() <= UBigDec32::from_str("0x2").unwrap());
    assert!(UBigDec32::from_str("2").unwrap() > UBigDec32::from_str("0x1").unwrap());
    assert!(UBigDec32::from_str("000000000999999999").unwrap() < UBigDec32::from_str("000000001000000000").unwrap());
    assert!(UBigDec32::from_str("000000001000000001").unwrap() > UBigDec32::from_str("000000001000000000").unwrap());
}
