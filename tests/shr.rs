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

use babs::{UBigBin32, UBigBin64, UBigDec32, UBigDec64};
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

    let mut n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap();
    n >>= 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let mut n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
    n >>= 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffff");

    let mut n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap();
    n >>= 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let mut n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap();
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

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() >> 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let n = UBigBin32::from_str("0x71919fc729e01f34d132").unwrap() >> 82;
    assert_eq!(format!("{:#x}", n), "0x0");

    let n = UBigBin32::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap() >> 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffff");

    let n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap() >> 73;
    assert_eq!(format!("{:#x}", n), "0x38");

    let n = UBigBin64::from_str("0x71919fc729e01f34d132").unwrap() >> 0;
    assert_eq!(format!("{:#x}", n), "0x71919fc729e01f34d132");

    let n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffff").unwrap() >> 128;
    assert_eq!(format!("{:#x}", n), "0xfffffffffff");
}
