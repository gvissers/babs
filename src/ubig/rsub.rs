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

use crate::digit::Digit;
use crate::result::{Error, Result};
use crate::ubig::support::drop_leading_zeros;

/// Subtract the big number represented by te digits in `n0` from the number or number part represented
/// by `n1`, and store the result back in `nr0`. Returns the number of digits in the result. If
/// `nr0` is less than `nr1`, an `Underflow` error is returned. The length of `nr0` must be equal to
//// that of `nr1`.
pub fn rsub_assign_big<T>(nr0: &mut [T], nr1: &[T]) -> Result<usize>
where T: Digit
{
    let n0 = nr0.len();
    assert!(nr1.len() == n0);

    let mut carry = false;
    for (d0, mut d1) in nr0.iter_mut().zip(nr1.iter().copied())
    {
        carry = d1.sub_carry_assign(*d0, carry);
        *d0 = d1;
    }

    if carry
    {
        Err(Error::Underflow)
    }
    else
    {
        Ok(drop_leading_zeros(nr0, n0))
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_rsub_assign_big_binary()
    {
        let mut nr0: [BinaryDigit<u8>; 0] = [];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, []);
        assert_eq!(res, Ok(0));

        let mut nr0 = [BinaryDigit(0x34u8), BinaryDigit(0x12)];
        let nr1 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x02), BinaryDigit(0x04)]);
        assert_eq!(res, Ok(2));

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x12)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0xfb)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x17)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x16)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [BinaryDigit(0x81fe61acu32), BinaryDigit(0xf352e1a3), BinaryDigit(0x729100ac)];
        let nr1 = [BinaryDigit(0x6ffe6215u32), BinaryDigit(0xa625f3dc), BinaryDigit(0xd612f42f)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xee000069), BinaryDigit(0xb2d31238), BinaryDigit(0x6381f382)]);
        assert_eq!(res, Ok(3));
    }

    #[test]
    fn test_rsub_assign_big_decimal()
    {
        let mut nr0: [DecimalDigit<u8>; 0] = [];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, []);
        assert_eq!(res, Ok(0));

        let mut nr0 = [DecimalDigit(34u8), DecimalDigit(12)];
        let nr1 = [DecimalDigit(36u8), DecimalDigit(16)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(2), DecimalDigit(4)]);
        assert_eq!(res, Ok(2));

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(12)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(95)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(17)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(16)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(99)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [DecimalDigit(287_091_918u32), DecimalDigit(827_909_001), DecimalDigit(275_599_012)];
        let nr1 = [DecimalDigit(874_762_199u32), DecimalDigit(564_887_009), DecimalDigit(387_764_666)];
        let res = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(587_670_281), DecimalDigit(736_978_008), DecimalDigit(112_165_653)]);
        assert_eq!(res, Ok(3));
    }
}
