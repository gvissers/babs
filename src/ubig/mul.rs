mod karatsuba;
mod long;
mod toom3;

use crate::digit::Digit;

/// The minimum size of a number (in digits) for Karatsuba multiplication. Should be at least 4.
const KARATSUBA_CUTOFF: usize = 20;
/// The minimum size of a number (in digits) for Toom-Cook multiplication.
const TOOM3_CUTOFF: usize = 128;


/// Multiply the number or number part represented by the digits in `nr` by the single digit `fac`,
/// and add the single digit `off` to the result. Return the carry on overflow, or `None` if the
/// number does not overflow.
pub fn mul_add_assign_digit<T>(nr: &mut [T], fac: T, off: T) -> Option<T>
where T: Digit
{
    let mut carry = off;
    for d in nr.iter_mut()
    {
        carry = d.mul_carry_assign(fac, carry);
    }

    (!carry.is_zero()).then(|| carry)
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
fn mul_big_into_with_work<T>(nr0: &[T], nr1: &[T], product: &mut [T], work: &mut [T]) -> usize
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

#[cfg(test)]
mod tests
{
    use crate::digit::{BinaryDigit, DecimalDigit};
    use super::*;

    #[test]
    fn test_mul_add_assign_digit_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x57), BinaryDigit(0x32));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(BinaryDigit(0x32)));

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(0x61), BinaryDigit(0xa7)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x57), BinaryDigit(0x32));
        assert_eq!(nr, [BinaryDigit(0xdb), BinaryDigit(0x4d), BinaryDigit(0xe2)]);
        assert_eq!(carry, Some(BinaryDigit(0x38)));

        let mut nr = [BinaryDigit(0xf3u8), BinaryDigit(0xa7), BinaryDigit(0x50)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x03), BinaryDigit(0x32));
        assert_eq!(nr, [BinaryDigit(0x0b), BinaryDigit(0xf8), BinaryDigit(0xf1)]);
        assert_eq!(carry, None);

        let mut nr: [BinaryDigit<u16>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f), BinaryDigit(0x3298));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(BinaryDigit(0x3298)));

        let mut nr = [BinaryDigit(0xffe3u16), BinaryDigit(0x619a), BinaryDigit(0xa7ff)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f), BinaryDigit(0x3298));
        assert_eq!(nr, [BinaryDigit(0x7335), BinaryDigit(0x52d2), BinaryDigit(0xf19a)]);
        assert_eq!(carry, Some(BinaryDigit(0x6c9a)));

        let mut nr = [BinaryDigit(0xffe3u16), BinaryDigit(0x619a), BinaryDigit(0x50)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0x00ff), BinaryDigit(0x3298));
        assert_eq!(nr, [BinaryDigit(0x15b5), BinaryDigit(0x3965), BinaryDigit(0x5011)]);
        assert_eq!(carry, None);

        let mut nr: [BinaryDigit<u32>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f7fb1), BinaryDigit(0x32988fa3));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(BinaryDigit(0x32988fa3)));

        let mut nr = [BinaryDigit(0xffe316fau32), BinaryDigit(0x619a99ff), BinaryDigit(0xa7ff321c)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(0xa57f9af2), BinaryDigit(0x32988fa3));
        assert_eq!(nr, [BinaryDigit(0x3b1cabf7), BinaryDigit(0xaab6e366), BinaryDigit(0x7a5f827f)]);
        assert_eq!(carry, Some(BinaryDigit(0x6c9b3894)));

        let mut nr = [BinaryDigit(0xffe316fau32), BinaryDigit(0x619a99ff), BinaryDigit(0x77ff321c)];
        let carry = mul_add_assign_digit(&mut nr, BinaryDigit(2), BinaryDigit(0x32988fa3));
        assert_eq!(nr, [BinaryDigit(0x325ebd97), BinaryDigit(0xc3353400), BinaryDigit(0xeffe6438)]);
        assert_eq!(carry, None);
    }

    #[test]
    fn test_mul_add_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(57), DecimalDigit(32));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(DecimalDigit(32)));

        let mut nr = [DecimalDigit(99u8), DecimalDigit(61), DecimalDigit(97)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(57), DecimalDigit(32));
        assert_eq!(nr, [DecimalDigit(75), DecimalDigit(33), DecimalDigit(64)]);
        assert_eq!(carry, Some(DecimalDigit(55)));

        let mut nr = [DecimalDigit(93u8), DecimalDigit(87), DecimalDigit(21)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(3), DecimalDigit(32));
        assert_eq!(nr, [DecimalDigit(11), DecimalDigit(64), DecimalDigit(65)]);
        assert_eq!(carry, None);

        let mut nr: [DecimalDigit<u16>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(8_739), DecimalDigit(3_298));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(DecimalDigit(3_298)));

        let mut nr = [DecimalDigit(9_935u16), DecimalDigit(6_193), DecimalDigit(4_324)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(8_739), DecimalDigit(3_298));
        assert_eq!(nr, [DecimalDigit(5_263), DecimalDigit(9_309), DecimalDigit(2_848)]);
        assert_eq!(carry, Some(DecimalDigit(3_779)));

        let mut nr = [DecimalDigit(9_935u16), DecimalDigit(6_193), DecimalDigit(45)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(175), DecimalDigit(3_298));
        assert_eq!(nr, [DecimalDigit(1_923), DecimalDigit(3_949), DecimalDigit(7_983)]);
        assert_eq!(carry, None);

        let mut nr: [DecimalDigit<u32>; 0] = [];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(123_761_987), DecimalDigit(321_563_982));
        assert_eq!(nr, []);
        assert_eq!(carry, Some(DecimalDigit(321_563_982)));

        let mut nr = [DecimalDigit(873_817_123u32), DecimalDigit(999_987_999), DecimalDigit(281_784_299)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(123_761_987), DecimalDigit(321_563_982));
        assert_eq!(nr, [DecimalDigit(738_667_383), DecimalDigit(840_539_356), DecimalDigit(873_402_614)]);
        assert_eq!(carry, Some(DecimalDigit(34_874_184)));

        let mut nr = [DecimalDigit(873_817_123u32), DecimalDigit(999_987_999), DecimalDigit(4_299)];
        let carry = mul_add_assign_digit(&mut nr, DecimalDigit(2_987), DecimalDigit(321_563_982));
        assert_eq!(nr, [DecimalDigit(413_310_383), DecimalDigit(964_155_623), DecimalDigit(12_844_099)]);
        assert_eq!(carry, None);
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
