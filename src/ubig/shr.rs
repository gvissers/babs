use crate::digit::Digit;
use crate::ubig::support::drop_leading_zeros;

/// Shift the number represented by the digits in `nr` right by `shift` bits, and whift in `carry`
/// as the most significant bits. The carry `carry` must fit in `shift` bits, which in turn must be
/// smaller than the bit width of the digit, i.e. `carry` < 2<sup>`shift`</sup> < `b`.  Returns the
/// number of digits of the shifted result, and the new carry after the right shift.
pub fn shr_carry_assign_within_digit<T>(nr: &mut [T], shift: usize, carry: T) -> (usize, T)
where T: Digit
{
    if shift == 0
    {
        (nr.len(), T::zero())
    }
    else
    {
        let carry = nr.iter_mut().rev().fold(carry, |carry, d| d.shr_carry_assign(shift, carry));
        let nd = drop_leading_zeros(nr, nr.len());
        (nd, carry)
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_shr_carry_assign_within_digit_binary()
    {
        let mut n: [BinaryDigit<u32>; 0] = [];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x7fff));
        assert_eq!(nd, 0);
        assert_eq!(carry, BinaryDigit(0x7fff));
        assert_eq!(n, []);

        let mut n = [BinaryDigit(0x06725412u32), BinaryDigit(0x16fadefe), BinaryDigit(0x61c14ad4)];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x7fff));
        assert_eq!(nd, 3);
        assert_eq!(carry, BinaryDigit(0x5412));
        assert_eq!(n, [BinaryDigit(0xbdfc0ce4), BinaryDigit(0x95a82df5), BinaryDigit(0xfffec382)]);

        let mut n = [
            BinaryDigit(0x5412u16),
            BinaryDigit(0x0672),
            BinaryDigit(0xdefe),
            BinaryDigit(0x16fa),
            BinaryDigit(0x4ad4),
            BinaryDigit(0x61c1)
        ];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x02e5));
        assert_eq!(nd, 6);
        assert_eq!(carry, BinaryDigit(0x5412));
        assert_eq!(n, [
            BinaryDigit(0x0ce4),
            BinaryDigit(0xbdfc),
            BinaryDigit(0x2df5),
            BinaryDigit(0x95a8),
            BinaryDigit(0xc382),
            BinaryDigit(0x05ca)
        ]);

        let mut n = [BinaryDigit(0x82729180f6deeef5_u64), BinaryDigit(0x00ffffffffffffff)];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 56, BinaryDigit(0));
        assert_eq!(nd, 1);
        assert_eq!(carry, BinaryDigit(0x00729180f6deeef5));
        assert_eq!(n, [BinaryDigit(0xffffffffffffff82), BinaryDigit(0)]);
    }

    #[test]
    fn test_shl_carry_assign_within_digit_decimal()
    {
        let mut n: [DecimalDigit<u32>; 0] = [];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, DecimalDigit(9_999));
        assert_eq!(n, []);
        assert_eq!(nd, 0);
        assert_eq!(carry, DecimalDigit(9_999));

        let mut n = [DecimalDigit(826_211_332u32), DecimalDigit(187_721_198), DecimalDigit(987_365_181)];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, DecimalDigit(9_999));
        assert_eq!(n, [DecimalDigit(61_975_897), DecimalDigit(665_929_801), DecimalDigit(305_175_395)]);
        assert_eq!(nd, 3);
        assert_eq!(carry, DecimalDigit(18_436));

        let mut n = [DecimalDigit(826_211_332u32), DecimalDigit(187_721_198), DecimalDigit(5_181)];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 15, DecimalDigit(0));
        assert_eq!(nd, 2);
        assert_eq!(carry, DecimalDigit(18_436));
        assert_eq!(n, [DecimalDigit(61_975_897), DecimalDigit(158_117_301), DecimalDigit(0)]);

        let mut n = [
            DecimalDigit(1_332u16),
            DecimalDigit(2_621),
            DecimalDigit(1_988),
            DecimalDigit(7_721),
            DecimalDigit(8_118),
            DecimalDigit(3_651),
            DecimalDigit(987)
        ];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 11, DecimalDigit(2_000));
        assert_eq!(n, [
            DecimalDigit(4_361),
            DecimalDigit(9_161),
            DecimalDigit(8_169),
            DecimalDigit(4_876),
            DecimalDigit(1_190),
            DecimalDigit(1_071),
            DecimalDigit(9_766)
        ]);
        assert_eq!(nd, 7);
        assert_eq!(carry, DecimalDigit(4));

        let mut n = [DecimalDigit(7_826_211_332_987_999_393u64), DecimalDigit(1_187_721_198_756_888_897)];
        let (nd, carry) = shr_carry_assign_within_digit(&mut n, 42, DecimalDigit(4_398_046_511_103));
        assert_eq!(nd, 2);
        assert_eq!(carry, DecimalDigit(4_015_589_610_657));
        assert_eq!(n, [DecimalDigit(7_799_308_747_784_795_334), DecimalDigit(9_999_999_999_997_996_319)]);
    }
}
