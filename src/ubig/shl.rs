use crate::digit::Digit;

/// Shift the number represented by the digits in `nr` left by `shift` bits, and add `carry` to the
/// result. The carry `carry` must fit in  `shift` bits, which in turn must be smaller than the bit
/// width of the digit, i.e. `off` < 2<sup>`n`</sup> < `b`, where `b` is the base of the number.
/// Returns the carry after the left shift.
pub fn shl_carry_assign_within_digit<T>(nr: &mut [T], shift: usize, carry: T) -> T
where T: Digit
{
    let mut carry = carry;
    for d in nr.iter_mut()
    {
        carry = d.shl_carry_assign(shift, carry);
    }
    carry
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_shl_carry_assign_within_digit_binary()
    {
        let mut n: [BinaryDigit<u32>; 0] = [];
        let carry = shl_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x7fff));
        assert_eq!(n, []);
        assert_eq!(carry, BinaryDigit(0x7fff));

        let mut n = [BinaryDigit(0x06725412u32), BinaryDigit(0x16fadefe), BinaryDigit(0x61c14ad4)];
        let carry = shl_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x7fff));
        assert_eq!(n, [BinaryDigit(0x2a097fff), BinaryDigit(0x6f7f0339), BinaryDigit(0xa56a0b7d)]);
        assert_eq!(carry, BinaryDigit(0x30e0));

        let mut n = [
            BinaryDigit(0x5412u16),
            BinaryDigit(0x0672),
            BinaryDigit(0xdefe),
            BinaryDigit(0x16fa),
            BinaryDigit(0x4ad4),
            BinaryDigit(0x61c1)
        ];
        let carry = shl_carry_assign_within_digit(&mut n, 15, BinaryDigit(0x7fff));
        assert_eq!(n, [
            BinaryDigit(0x7fff),
            BinaryDigit(0x2a09),
            BinaryDigit(0x0339),
            BinaryDigit(0x6f7f),
            BinaryDigit(0x0b7d),
            BinaryDigit(0xa56a)
        ]);
        assert_eq!(carry, BinaryDigit(0x30e0));
    }

    #[test]
    fn test_shl_carry_assign_within_digit_decimal()
    {
        let mut n: [DecimalDigit<u32>; 0] = [];
        let carry = shl_carry_assign_within_digit(&mut n, 15, DecimalDigit(9_999));
        assert_eq!(n, []);
        assert_eq!(carry, DecimalDigit(9_999));

        let mut n = [DecimalDigit(826_211_332u32), DecimalDigit(187_721_198), DecimalDigit(987_365_181)];
        let carry = shl_carry_assign_within_digit(&mut n, 15, DecimalDigit(9_999));
        assert_eq!(n, [DecimalDigit(292_936_975), DecimalDigit(248_243_137), DecimalDigit(982_257_159)]);
        assert_eq!(carry, DecimalDigit(32_353));

        let mut n = [
            DecimalDigit(1_332u16),
            DecimalDigit(2_621),
            DecimalDigit(1_988),
            DecimalDigit(7_721),
            DecimalDigit(8_118),
            DecimalDigit(3_651),
            DecimalDigit(987)
        ];
        let carry = shl_carry_assign_within_digit(&mut n, 11, DecimalDigit(2_000));
        assert_eq!(n, [
            DecimalDigit(9_936),
            DecimalDigit(8_080),
            DecimalDigit(1_960),
            DecimalDigit(3_015),
            DecimalDigit(7_245),
            DecimalDigit(8_910),
            DecimalDigit(2_123)
        ]);
        assert_eq!(carry, DecimalDigit(202));
    }
}
