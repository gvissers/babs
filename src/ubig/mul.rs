use crate::digit::Digit;
use num_traits::Zero;

/// Multiply the number or number part represented by the digits in `nr` by the single digit `fac`,
/// and add the single digit `off` to the result. Return the carry on overflow, or `None` if the
/// number does not overflow.
pub fn mul_add_assign_digit<T>(nr: &mut [T], fac: T, off: T) -> Option<T>
where T: Copy + Digit + Zero
{
    let mut carry = off;
    for d in nr.iter_mut()
    {
        carry = d.mul_add_assign(fac, carry);
    }

    (!carry.is_zero()).then(|| carry)
}

#[cfg(test)]
mod tests
{
    use crate::digit::{BinaryDigit, DecimalDigit};
    use super::mul_add_assign_digit;

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
}
