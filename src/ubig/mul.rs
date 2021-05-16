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

mod karatsuba;
mod long;
mod toom3;

use crate::digit::Digit;

/// The minimum size of a number (in digits) for Karatsuba multiplication. Should be at least 4.
const KARATSUBA_CUTOFF: usize = 20;
/// The minimum size of a number (in digits) for Toom-Cook multiplication.
const TOOM3_CUTOFF: usize = 128;

/// Double the number or number part in `nr`, and add carry to the result. Returns `true` if the
/// result overflows, `flase` otherwise.
pub fn double_carry_assign<T>(nr: &mut [T], carry: bool) -> bool
where T: Digit
{
    nr.iter_mut().fold(carry, |carry, d| d.double_carry_assign(carry))
}

/// Multiply the number or number part represented by the digits in `nr` by the single digit `fac`,
/// and add the single digit `off` to the result. Return the carry on overflow, or `None` if the
/// number does not overflow.
pub fn mul_add_assign_digit<T>(nr: &mut [T], fac: T, off: T) -> T
where T: Digit
{
    nr.iter_mut().fold(off, |carry, d| d.mul_carry_assign(fac, carry))
}

/// Multiply the number or number part represented by the digits in `nr` by the single digit `fac`,
/// and store the result in `product`. The length of `product` must be at least one more then that
/// of `nr`.
pub fn mul_digit_into<T>(nr: &[T], fac: T, product: &mut [T])
where T: Digit
{
    let nd = nr.len();
    debug_assert!(product.len() >= nd+1);
    product[nd] = nr.iter()
        .zip(product.iter_mut())
        .fold(T::zero(), |carry, (&d, pd)| {*pd = d; pd.mul_carry_assign(fac, carry) });
}

/// Multiply the number or number part represented by the digits in `nr` by the two-digit number
/// `fac_low + b*fac_high`, where `b` is the base of the number, and add `offset` to it. Return
/// the carry digits.
pub fn mul_pair_add_assign_digit<T>(nr: &mut [T], fac_low: T, fac_high: T, offset: T) -> (T, T)
where T: Digit
{
    if !nr.is_empty()
    {
        let mut prev = nr[0];
        let mut carry0 = nr[0].mul_carry_assign(fac_low, offset);
        let mut add_one = false;
        for d in nr[1..].iter_mut()
        {
            let new_prev = *d;

            carry0 = prev.mul_carry_assign(fac_high, carry0);
            if add_one
            {
                add_one = carry0.inc();
            }
            let carry1 = d.mul_carry_assign(fac_low, prev);
            add_one |= carry0.add_carry_assign(carry1, false);

            prev = new_prev;
        }
        carry0 = prev.mul_carry_assign(fac_high, carry0);
        if add_one
        {
            carry0.inc();
        }

        (prev, carry0)
    }
    else
    {
        (offset, T::zero())
    }
}

/// Calculate the maximum size of the scratch array necessary to perform multiplication
/// on two `n`-digit numbers.
pub fn calc_mul_work_size(n: usize) -> usize
{
    if n >= TOOM3_CUTOFF
    {
        toom3::calc_toom3_work_size(n)
    }
    else if n >= KARATSUBA_CUTOFF
    {
        karatsuba::calc_karatsuba_work_size(n)
    }
    else
    {
        0
    }
}

/// Multiply the number represented by `nr0` by `nr1`, and store the  result in `product`. The
/// result array must have space for at least `n0+n1` digits,  where `n0` denotes the number of
/// digits in `nr0`, and `n1` the number of digits in `nr1`. Returns the number of digits in the
/// product.
pub fn mul_big_into<T>(nr0: &[T], nr1: &[T], product: &mut [T]) -> usize
where T: Digit
{
    if nr0.is_empty() || nr1.is_empty()
    {
        0
    }
    else
    {
        let n0 = nr0.len();
        let n1 = nr1.len();
        assert!(product.len() >= n0 + n1, "Not enough space to store the result");

        if n0 >= TOOM3_CUTOFF && n1 >= TOOM3_CUTOFF
        {
            let work_size = toom3::calc_toom3_work_size(n0.max(n1));
            let mut work = vec![T::zero(); work_size];
            toom3::mul_big_toom3_into(nr0, nr1, product, &mut work)
        }
        else if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
        {
            let work_size = karatsuba::calc_karatsuba_work_size(n0.max(n1));
            let mut work = vec![T::zero(); work_size];
            karatsuba::mul_big_karatsuba_into(nr0, nr1, product, &mut work)
        }
        else
        {
            long::mul_big_long_into(nr0, nr1, product)
        }
    }
}

/// Multiply the number represented by `nr0` by `nr1`, possibly uing scratch array `work` in the
/// process, and store the result in `product`. The result array must have space for at least
/// `n0+n1` digits,  where `n0` denotes the number of digits in `nr0`, and `n1` the number of digits
/// in `nr1`. Returns the number of digits in the product.
pub(super) fn mul_big_into_with_work<T>(nr0: &[T], nr1: &[T], product: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    if nr0.is_empty() || nr1.is_empty()
    {
        0
    }
    else
    {
        let n0 = nr0.len();
        let n1 = nr1.len();
        assert!(product.len() >= n0 + n1, "Not enough space to store the result");

        if n0 >= TOOM3_CUTOFF && n1 >= TOOM3_CUTOFF
        {
            toom3::mul_big_toom3_into(nr0, nr1, product, work)
        }
        else if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
        {
            karatsuba::mul_big_karatsuba_into(nr0, nr1, product, work)
        }
        else
        {
            long::mul_big_long_into(nr0, nr1, product)
        }
    }
}

/// Calculate the square of the number represented by `nr0`, and store the result in `square`. The
/// result array must have space for at least `2*n0` digits,  where `n0` denotes the number of
/// digits in `nr0`. Returns the number of digits in the square.
pub fn square_into<T>(nr0: &[T], square: &mut [T]) -> usize
where T: Digit
{
    if nr0.is_empty()
    {
        0
    }
    else
    {
        let n0 = nr0.len();
        assert!(square.len() >= 2*n0, "Not enough space to store the result");

        if n0 >= TOOM3_CUTOFF
        {
            let work_size = toom3::calc_toom3_work_size(n0);
            let mut work = vec![T::zero(); work_size];
            toom3::square_toom3_into(nr0, square, &mut work)
        }
        else if n0 >= KARATSUBA_CUTOFF
        {
            let work_size = karatsuba::calc_karatsuba_work_size(n0);
            let mut work = vec![T::zero(); work_size];
            karatsuba::square_karatsuba_into(nr0, square, &mut work)
        }
        else
        {
            long::square_long_into(nr0, square)
        }
    }
}

/// Square the number represented by `nr0`, possibly uing scratch array `work` in the
/// process, and store the result in `square`. The result array must have space for at least
/// `2*n0` digits,  where `n0` denotes the number of digits in `nr0`. Returns the number of
/// digits in the square.
fn square_into_with_work<T>(nr0: &[T], square: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    if nr0.is_empty()
    {
        0
    }
    else
    {
        let n0 = nr0.len();
        assert!(square.len() >= 2*n0, "Not enough space to store the result");

        if n0 >= TOOM3_CUTOFF
        {
            toom3::square_toom3_into(nr0, square, work)
        }
        else if n0 >= KARATSUBA_CUTOFF
        {
            karatsuba::square_karatsuba_into(nr0, square, work)
        }
        else
        {
            long::square_long_into(nr0, square)
        }
    }
}

#[cfg(test)]
mod tests
{
    use crate::digit::{BinaryDigit, DecimalDigit};
    use super::*;

    #[test]
    fn test_double_carry_assign_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, []);
        assert!(carry);

        let mut nr = [BinaryDigit(0x78_u8), BinaryDigit(0xf2), BinaryDigit(0x76)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [BinaryDigit(0xf1), BinaryDigit(0xe4), BinaryDigit(0xed)]);
        assert!(!carry);

        let mut nr = [BinaryDigit(0x78_u8), BinaryDigit(0xf2), BinaryDigit(0x86)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [BinaryDigit(0xf1), BinaryDigit(0xe4), BinaryDigit(0x0d)]);
        assert!(carry);

        let mut nr = [BinaryDigit(0x78_u16), BinaryDigit(0xf2), BinaryDigit(0x86)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [BinaryDigit(0xf1), BinaryDigit(0x01e4), BinaryDigit(0x010c)]);
        assert!(!carry);

        let mut nr = [BinaryDigit(0x1278_u16), BinaryDigit(0x80f2), BinaryDigit(0xc386)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [BinaryDigit(0x24f0), BinaryDigit(0x01e4), BinaryDigit(0x870d)]);
        assert!(carry);

        let mut nr = [BinaryDigit(0x1278_u32), BinaryDigit(0x80f2), BinaryDigit(0xc386)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [BinaryDigit(0x24f0), BinaryDigit(0x0101e4), BinaryDigit(0x01870c)]);
        assert!(!carry);

        let mut nr = [BinaryDigit(0xffff1278_u32), BinaryDigit(0xc38580f2), BinaryDigit(0x764dc386)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [BinaryDigit(0xfffe24f1), BinaryDigit(0x870b01e5), BinaryDigit(0xec9b870d)]);
        assert!(!carry);

        let mut nr = [BinaryDigit(0xffff1278_u64), BinaryDigit(0xc38580f2), BinaryDigit(0x764dc386)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [BinaryDigit(0x01fffe24f1), BinaryDigit(0x01870b01e4), BinaryDigit(0xec9b870c)]);
        assert!(!carry);

        let mut nr = [BinaryDigit(0x73f5d78affff1278_u64), BinaryDigit(0x809267f4c38580f2), BinaryDigit(0x818df45d764dc386)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [BinaryDigit(0xe7ebaf15fffe24f0), BinaryDigit(0x0124cfe9870b01e4), BinaryDigit(0x031be8baec9b870d)]);
        assert!(carry);
    }

    #[test]
    fn test_double_carry_assign_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, []);
        assert!(carry);

        let mut nr = [DecimalDigit(78_u8), DecimalDigit(92), DecimalDigit(36)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [DecimalDigit(57), DecimalDigit(85), DecimalDigit(73)]);
        assert!(!carry);

        let mut nr = [DecimalDigit(78_u8), DecimalDigit(92), DecimalDigit(76)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [DecimalDigit(57), DecimalDigit(85), DecimalDigit(53)]);
        assert!(carry);

        let mut nr = [DecimalDigit(78_u16), DecimalDigit(92), DecimalDigit(76)];
        let carry = double_carry_assign(&mut nr, true);
        assert_eq!(nr, [DecimalDigit(157), DecimalDigit(184), DecimalDigit(152)]);
        assert!(!carry);

        let mut nr = [DecimalDigit(8_765_u16), DecimalDigit(4_321), DecimalDigit(5_000)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(7_530), DecimalDigit(8_643), DecimalDigit(0)]);
        assert!(carry);

        let mut nr = [DecimalDigit(8_765_u32), DecimalDigit(4_321), DecimalDigit(5_000)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(17_530), DecimalDigit(8_642), DecimalDigit(10_000)]);
        assert!(!carry);

        let mut nr = [DecimalDigit(999_999_999_u32), DecimalDigit(999_999_999), DecimalDigit(999_999_999)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(999_999_998), DecimalDigit(999_999_999), DecimalDigit(999_999_999)]);
        assert!(carry);

        let mut nr = [DecimalDigit(999_999_999_u64), DecimalDigit(999_999_999), DecimalDigit(999_999_999)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(1_999_999_998), DecimalDigit(1_999_999_998), DecimalDigit(1_999_999_998)]);
        assert!(!carry);

        let mut nr = [DecimalDigit(5_789_987_625_187_287_987_u64), DecimalDigit(3_981_928_988_564_766_999)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(1_579_975_250_374_575_974), DecimalDigit(7_963_857_977_129_533_999)]);
        assert!(!carry);

        let mut nr = [DecimalDigit(3_981_928_988_564_766_999_u64), DecimalDigit(5_789_987_625_187_287_987)];
        let carry = double_carry_assign(&mut nr, false);
        assert_eq!(nr, [DecimalDigit(7_963_857_977_129_533_998), DecimalDigit(1_579_975_250_374_575_974)]);
        assert!(carry);
    }

    #[test]
    fn test_mul_add_assign_digit_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x57), BinaryDigit(0x32));
        assert_eq!(nr, []);
        assert_eq!(carry, BinaryDigit(0x32));

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(0x61), BinaryDigit(0xa7)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x57), BinaryDigit(0x32));
        assert_eq!(nr, [BinaryDigit(0xdb), BinaryDigit(0x4d), BinaryDigit(0xe2)]);
        assert_eq!(carry, BinaryDigit(0x38));

        let mut nr = [BinaryDigit(0xf3u8), BinaryDigit(0xa7), BinaryDigit(0x50)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x03), BinaryDigit(0x32));
        assert_eq!(nr, [BinaryDigit(0x0b), BinaryDigit(0xf8), BinaryDigit(0xf1)]);
        assert_eq!(carry, BinaryDigit(0));

        let mut nr: [BinaryDigit<u16>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f), BinaryDigit(0x3298));
        assert_eq!(nr, []);
        assert_eq!(carry, BinaryDigit(0x3298));

        let mut nr = [BinaryDigit(0xffe3u16), BinaryDigit(0x619a), BinaryDigit(0xa7ff)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f), BinaryDigit(0x3298));
        assert_eq!(nr, [BinaryDigit(0x7335), BinaryDigit(0x52d2), BinaryDigit(0xf19a)]);
        assert_eq!(carry, BinaryDigit(0x6c9a));

        let mut nr = [BinaryDigit(0xffe3u16), BinaryDigit(0x619a), BinaryDigit(0x50)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x00ff), BinaryDigit(0x3298));
        assert_eq!(nr, [BinaryDigit(0x15b5), BinaryDigit(0x3965), BinaryDigit(0x5011)]);
        assert_eq!(carry, BinaryDigit(0));

        let mut nr: [BinaryDigit<u32>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f7fb1), BinaryDigit(0x32988fa3));
        assert_eq!(nr, []);
        assert_eq!(carry, BinaryDigit(0x32988fa3));

        let mut nr = [BinaryDigit(0xffe316fau32), BinaryDigit(0x619a99ff), BinaryDigit(0xa7ff321c)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f9af2), BinaryDigit(0x32988fa3));
        assert_eq!(nr, [BinaryDigit(0x3b1cabf7), BinaryDigit(0xaab6e366), BinaryDigit(0x7a5f827f)]);
        assert_eq!(carry, BinaryDigit(0x6c9b3894));

        let mut nr = [BinaryDigit(0xffe316fau32), BinaryDigit(0x619a99ff), BinaryDigit(0x77ff321c)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(2), BinaryDigit(0x32988fa3));
        assert_eq!(nr, [BinaryDigit(0x325ebd97), BinaryDigit(0xc3353400), BinaryDigit(0xeffe6438)]);
        assert_eq!(carry, BinaryDigit(0));
    }

    #[test]
    fn test_mul_add_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(57), DecimalDigit(32));
        assert_eq!(nr, []);
        assert_eq!(carry, DecimalDigit(32));

        let mut nr = [DecimalDigit(99u8), DecimalDigit(61), DecimalDigit(97)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(57), DecimalDigit(32));
        assert_eq!(nr, [DecimalDigit(75), DecimalDigit(33), DecimalDigit(64)]);
        assert_eq!(carry, DecimalDigit(55));

        let mut nr = [DecimalDigit(93u8), DecimalDigit(87), DecimalDigit(21)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(3), DecimalDigit(32));
        assert_eq!(nr, [DecimalDigit(11), DecimalDigit(64), DecimalDigit(65)]);
        assert_eq!(carry, DecimalDigit(0));

        let mut nr: [DecimalDigit<u16>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(8_739), DecimalDigit(3_298));
        assert_eq!(nr, []);
        assert_eq!(carry, DecimalDigit(3_298));

        let mut nr = [DecimalDigit(9_935u16), DecimalDigit(6_193), DecimalDigit(4_324)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(8_739), DecimalDigit(3_298));
        assert_eq!(nr, [DecimalDigit(5_263), DecimalDigit(9_309), DecimalDigit(2_848)]);
        assert_eq!(carry, DecimalDigit(3_779));

        let mut nr = [DecimalDigit(9_935u16), DecimalDigit(6_193), DecimalDigit(45)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(175), DecimalDigit(3_298));
        assert_eq!(nr, [DecimalDigit(1_923), DecimalDigit(3_949), DecimalDigit(7_983)]);
        assert_eq!(carry, DecimalDigit(0));

        let mut nr: [DecimalDigit<u32>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(123_761_987), DecimalDigit(321_563_982));
        assert_eq!(nr, []);
        assert_eq!(carry, DecimalDigit(321_563_982));

        let mut nr = [DecimalDigit(873_817_123u32), DecimalDigit(999_987_999), DecimalDigit(281_784_299)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(123_761_987), DecimalDigit(321_563_982));
        assert_eq!(nr, [DecimalDigit(738_667_383), DecimalDigit(840_539_356), DecimalDigit(873_402_614)]);
        assert_eq!(carry, DecimalDigit(34_874_184));

        let mut nr = [DecimalDigit(873_817_123u32), DecimalDigit(999_987_999), DecimalDigit(4_299)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(2_987), DecimalDigit(321_563_982));
        assert_eq!(nr, [DecimalDigit(413_310_383), DecimalDigit(964_155_623), DecimalDigit(12_844_099)]);
        assert_eq!(carry, DecimalDigit(0));
    }

    #[test]
    fn test_mul_digit_into_binary()
    {
        let nr: [BinaryDigit<u8>; 0] = [];
        let mut product = [BinaryDigit(0u8); 1];
        mul_digit_into(&nr, BinaryDigit(0x57), &mut product);
        assert_eq!(product, [BinaryDigit(0)]);

        let nr = [BinaryDigit(0xff_u8), BinaryDigit(0x61), BinaryDigit(0xa7)];
        let mut product = [BinaryDigit(0u8); 4];
        mul_digit_into(&nr, BinaryDigit(0x57), &mut product);
        assert_eq!(product, [BinaryDigit(0xa9), BinaryDigit(0x4d), BinaryDigit(0xe2), BinaryDigit(0x38)]);

        let nr = [BinaryDigit(0xf3_u8), BinaryDigit(0xa7), BinaryDigit(0x50)];
        let mut product = [BinaryDigit(0u8); 4];
        mul_digit_into(&nr, BinaryDigit(0x03), &mut product);
        assert_eq!(product, [BinaryDigit(0xd9), BinaryDigit(0xf7), BinaryDigit(0xf1), BinaryDigit(0)]);

        let nr: [BinaryDigit<u16>; 0] = [];
        let mut product = [BinaryDigit(0u16); 1];
        mul_digit_into(&nr, BinaryDigit(0xa57f), &mut product);
        assert_eq!(product, [BinaryDigit(0)]);

        let nr = [BinaryDigit(0xffe3_u16), BinaryDigit(0x619a), BinaryDigit(0xa7ff)];
        let mut product = [BinaryDigit(0u16); 4];
        mul_digit_into(&nr, BinaryDigit(0xa57f), &mut product);
        assert_eq!(product, [BinaryDigit(0x409d), BinaryDigit(0x52d2), BinaryDigit(0xf19a), BinaryDigit(0x6c9a)]);

        let nr = [BinaryDigit(0xffe3_u16), BinaryDigit(0x619a), BinaryDigit(0x50)];
        let mut product = [BinaryDigit(0u16); 4];
        mul_digit_into(&nr, BinaryDigit(0x00ff), &mut product);
        assert_eq!(product, [BinaryDigit(0xe31d), BinaryDigit(0x3964), BinaryDigit(0x5011), BinaryDigit(0)]);

        let nr: [BinaryDigit<u32>; 0] = [];
        let mut product = [BinaryDigit(0u32); 1];
        mul_digit_into(&nr, BinaryDigit(0xa57f7fb1), &mut product);
        assert_eq!(product, [BinaryDigit(0)]);

        let nr = [BinaryDigit(0xffe316fa_u32), BinaryDigit(0x619a99ff), BinaryDigit(0xa7ff321c)];
        let mut product = [BinaryDigit(0u32); 4];
        mul_digit_into(&nr, BinaryDigit(0xa57f9af2), &mut product);
        assert_eq!(product, [
            BinaryDigit(0x08841c54),
            BinaryDigit(0xaab6e366),
            BinaryDigit(0x7a5f827f),
            BinaryDigit(0x6c9b3894)
        ]);

        let nr = [BinaryDigit(0xffe316fa_u32), BinaryDigit(0x619a99ff), BinaryDigit(0x77ff321c)];
        let mut product = [BinaryDigit(0u32); 4];
        mul_digit_into(&nr, BinaryDigit(2), &mut product);
        assert_eq!(product, [
            BinaryDigit(0xffc62df4),
            BinaryDigit(0xc33533ff),
            BinaryDigit(0xeffe6438),
            BinaryDigit(0)
        ]);

        let nr = [BinaryDigit(0xffe316fa98326729_u64), BinaryDigit(0x619a99fff34ddad3)];
        let mut product = [BinaryDigit(0u64); 3];
        mul_digit_into(&nr, BinaryDigit(0x3d453d24a57f9af2), &mut product);
        assert_eq!(product, [
            BinaryDigit(0x67a0bcb4cc0b2ec2),
            BinaryDigit(0xe5c8cc73088dad7a),
            BinaryDigit(0x175c3cad4e7f121f)
        ]);
    }

    #[test]
    fn test_mul_digit_into_decimal()
    {
        let nr: [DecimalDigit<u8>; 0] = [];
        let mut product = [DecimalDigit(0u8); 1];
        mul_digit_into(&nr, DecimalDigit(57), &mut product);
        assert_eq!(product, [DecimalDigit(0)]);

        let nr = [DecimalDigit(99_u8), DecimalDigit(61), DecimalDigit(97)];
        let mut product = [DecimalDigit(0u8); 4];
        mul_digit_into(&nr, DecimalDigit(57), &mut product);
        assert_eq!(product, [DecimalDigit(43), DecimalDigit(33), DecimalDigit(64), DecimalDigit(55)]);

        let nr = [DecimalDigit(93_u8), DecimalDigit(87), DecimalDigit(21)];
        let mut product = [DecimalDigit(0u8); 4];
        mul_digit_into(&nr, DecimalDigit(3), &mut product);
        assert_eq!(product, [DecimalDigit(79), DecimalDigit(63), DecimalDigit(65), DecimalDigit(0)]);

        let nr: [DecimalDigit<u16>; 0] = [];
        let mut product = [DecimalDigit(0u16); 1];
        mul_digit_into(&nr, DecimalDigit(8_739), &mut product);
        assert_eq!(product, [DecimalDigit(0)]);

        let nr = [DecimalDigit(9_935_u16), DecimalDigit(6_193), DecimalDigit(4_324)];
        let mut product = [DecimalDigit(0u16); 4];
        mul_digit_into(&nr, DecimalDigit(8_739), &mut product);
        assert_eq!(product, [DecimalDigit(1_965), DecimalDigit(9_309), DecimalDigit(2_848), DecimalDigit(3_779)]);

        let nr = [DecimalDigit(9_935u16), DecimalDigit(6_193), DecimalDigit(45)];
        let mut product = [DecimalDigit(0u16); 4];
        mul_digit_into(&nr, DecimalDigit(175), &mut product);
        assert_eq!(product, [DecimalDigit(8_625), DecimalDigit(3_948), DecimalDigit(7_983), DecimalDigit(0)]);

        let nr: [DecimalDigit<u32>; 0] = [];
        let mut product = [DecimalDigit(0u32); 1];
        mul_digit_into(&nr, DecimalDigit(123_761_987), &mut product);
        assert_eq!(product, [DecimalDigit(0)]);

        let nr = [DecimalDigit(873_817_123_u32), DecimalDigit(999_987_999), DecimalDigit(281_784_299)];
        let mut product = [DecimalDigit(0u32); 4];
        mul_digit_into(&nr, DecimalDigit(123_761_987), &mut product);
        assert_eq!(product, [
            DecimalDigit(417_103_401),
            DecimalDigit(840_539_356),
            DecimalDigit(873_402_614),
            DecimalDigit(34_874_184)
        ]);

        let nr = [DecimalDigit(873_817_123_u32), DecimalDigit(999_987_999), DecimalDigit(4_299)];
        let mut product = [DecimalDigit(0u32); 4];
        mul_digit_into(&nr, DecimalDigit(2_987), &mut product);
        assert_eq!(product, [
            DecimalDigit( 91_746_401),
            DecimalDigit(964_155_623),
            DecimalDigit(12_844_099),
            DecimalDigit(0)
        ]);

        let nr = [DecimalDigit(5_873_817_123_123_777_879_u64), DecimalDigit(7_999_987_999_345_142_555)];
        let mut product = [DecimalDigit(0u64); 3];
        mul_digit_into(&nr, DecimalDigit(6_123_761_987_748_339_967), &mut product);
        assert_eq!(product, [
            DecimalDigit(3_334_168_447_886_189_993),
            DecimalDigit(  432_382_588_376_065_863),
            DecimalDigit(4_899_002_241_283_267_563)
        ]);
    }

    #[test]
    fn test_mul_pair_add_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(33), DecimalDigit(27), DecimalDigit(93));
        assert_eq!(nr, []);
        assert_eq!(carry, (DecimalDigit(93), DecimalDigit(0)));

        let mut nr = [DecimalDigit(67u8)];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(33), DecimalDigit(27), DecimalDigit(93));
        assert_eq!(nr, [DecimalDigit(4)]);
        assert_eq!(carry, (DecimalDigit(32), DecimalDigit(18)));

        let mut nr = [DecimalDigit(99u8)];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(99), DecimalDigit(99), DecimalDigit(99));
        assert_eq!(nr, [DecimalDigit(0)]);
        assert_eq!(carry, (DecimalDigit(0), DecimalDigit(99)));

        let mut nr = [DecimalDigit(99u8), DecimalDigit(99)];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(99), DecimalDigit(99), DecimalDigit(99));
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(1)]);
        assert_eq!(carry, (DecimalDigit(98), DecimalDigit(99)));

        let mut nr = [
            DecimalDigit(18u8),
            DecimalDigit(0),
            DecimalDigit(90),
            DecimalDigit(71),
            DecimalDigit(12),
            DecimalDigit(28),
            DecimalDigit(27),
            DecimalDigit(7)
        ];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(23), DecimalDigit(67), DecimalDigit(92));
        assert_eq!(nr, [
            DecimalDigit(06),
            DecimalDigit(11),
            DecimalDigit(82),
            DecimalDigit(83),
            DecimalDigit(09),
            DecimalDigit(99),
            DecimalDigit(11),
            DecimalDigit(95),
        ]);
        assert_eq!(carry, (DecimalDigit(88), DecimalDigit(4)));

        let mut nr = [DecimalDigit(99u8); 8];
        let carry = mul_pair_add_assign_digit(&mut nr, DecimalDigit(99), DecimalDigit(99), DecimalDigit(99));
        assert_eq!(nr, [
            DecimalDigit(0),
            DecimalDigit(1),
            DecimalDigit(99),
            DecimalDigit(99),
            DecimalDigit(99),
            DecimalDigit(99),
            DecimalDigit(99),
            DecimalDigit(99)
        ]);
        assert_eq!(carry, (DecimalDigit(98), DecimalDigit(99)));
    }
}
