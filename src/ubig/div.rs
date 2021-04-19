use crate::digit::Digit;

/// Divide the number or number part represented by the digits in `nr` by 3. The carry should
/// be less than 3.
#[inline]
pub fn div3_carry_assign<T>(nr: &mut [T], carry: T)
where T: Digit
{
    nr.iter_mut().rev().fold(carry, |carry, d| d.div3_carry_assign(carry));
}

/// Divide the number or number part represented by the digits in `nr` by the single digit `fac`,
// and return the remainder.
pub fn div_assign_digit<T>(nr: &mut [T], fac: T) -> T
where T: Digit
{
    assert!(!fac.is_zero());
    let mut carry = T::zero();
    for d in nr.iter_mut().rev()
    {
        carry = d.div_carry_assign(fac, carry);
    }

    carry
}

/// Divide the number or number part represented by the digits in `nr` by the two-digit number
/// `fac_low + b*fac_high`, where `b` is the base of the number. Return the carry digits.
pub fn div_pair_assign_digit<T>(nr: &mut [T], fac_low: T, fac_high: T) -> (T, T)
where T: Digit
{
    assert!(!fac_high.is_zero());

    match nr.len()
    {
        0 => (T::zero(), T::zero()),
        1 => { let rem_low = nr[0]; nr[0] = T::zero(); (rem_low, T::zero()) },
        n => {
            let shift = fac_high.max_shift() as usize;
            let (mut den_low, mut den_high) = (fac_low, fac_high);
            let mut rem_high = T::zero();
            if shift > 0
            {
                let carry = den_low.shl_carry_assign(shift, T::zero());
                den_high.shl_carry_assign(shift, carry);
                rem_high = crate::ubig::shl::shl_carry_assign_within_digit(nr, shift, T::zero());
            }
            let mut rem_low = std::mem::replace(&mut nr[n-1], T::zero());

            for digit in nr[..n-1].iter_mut().rev()
            {
                let mut quot = rem_low;
                quot.div_carry_assign(den_high, rem_high);

                let mut d1 = den_low;
                let c1 = d1.mul_carry_assign(quot, T::zero());
                let mut d2 = den_high;
                let mut d3 = d2.mul_carry_assign(quot, c1);
                if [d3, d2, d1] > [rem_high, rem_low, *digit]
                {
                    quot.dec();
                    let carry = d1.sub_carry_assign(den_low, false);
                    if d2.sub_carry_assign(den_high, carry)
                    {
                        d3.dec();
                    }
                    if [d3, d2, d1] > [rem_high, rem_low, *digit]
                    {
                        quot.dec();
                        let carry = d1.sub_carry_assign(den_low, false);
                        d2.sub_carry_assign(den_high, carry);
                    }
                }

                let carry = digit.sub_carry_assign(d1, false);
                rem_low.sub_carry_assign(d2, carry);

                rem_high = rem_low;
                rem_low = *digit;
                *digit = quot;
            }

            let carry = rem_high.shr_carry_assign(shift, T::zero());
            rem_low.shr_carry_assign(shift, carry);
            (rem_low, rem_high)
        }
    }
}


#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_div3_carry_assign_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        div3_carry_assign(&mut n, BinaryDigit(0));
        assert_eq!(n, []);

        let mut n = [BinaryDigit(0u8), BinaryDigit(0xfa), BinaryDigit(0x13), BinaryDigit(0xf2)];
        div3_carry_assign(&mut n, BinaryDigit(2));
        assert_eq!(n, [BinaryDigit(0), BinaryDigit(0xfe), BinaryDigit(0x5b), BinaryDigit(0xfb)]);

        let mut n = [BinaryDigit(0x761fu16), BinaryDigit(0xfa3d), BinaryDigit(0x1c3a)];
        div3_carry_assign(&mut n, BinaryDigit(0));
        assert_eq!(n, [BinaryDigit(0x7cb5), BinaryDigit(0xfe14), BinaryDigit(0x0968)]);

        let mut n = [BinaryDigit(0x1761f876u32), BinaryDigit(0xfa3dffe3), BinaryDigit(0x1c3ab218)];
        div3_carry_assign(&mut n, BinaryDigit(1));
        assert_eq!(n, [BinaryDigit(0xb275fd7c), BinaryDigit(0xa8bf554b), BinaryDigit(0x5ebe3b5d)]);
    }

    #[test]
    fn test_div3_carry_assign_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        div3_carry_assign(&mut n, DecimalDigit(2));
        assert_eq!(n, []);

        let mut n = [DecimalDigit(0u8), DecimalDigit(35), DecimalDigit(98), DecimalDigit(22)];
        div3_carry_assign(&mut n, DecimalDigit(2));
        assert_eq!(n, [DecimalDigit(33), DecimalDigit(78), DecimalDigit(32), DecimalDigit(74)]);

        let mut n = [DecimalDigit(0u16), DecimalDigit(0), DecimalDigit(1)];
        div3_carry_assign(&mut n, DecimalDigit(1));
        assert_eq!(n, [DecimalDigit(6_666), DecimalDigit(6_666), DecimalDigit(3_333)]);

        let mut n = [DecimalDigit(891_563_891u32), DecimalDigit(821_976_524), DecimalDigit(321_098_000)];
        div3_carry_assign(&mut n, DecimalDigit(0));
        assert_eq!(n, [DecimalDigit(630_521_297), DecimalDigit(940_658_841), DecimalDigit(107_032_666)]);
    }

    #[test]
    fn test_div_assign_digit_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        let carry = div_assign_digit(&mut n, BinaryDigit(0x53));
        assert_eq!(n, []);
        assert_eq!(carry, BinaryDigit(0));

        let mut n = [BinaryDigit(0u8), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let carry = div_assign_digit(&mut n, BinaryDigit(0x53));
        assert_eq!(n, [BinaryDigit(0x5c), BinaryDigit(0x82), BinaryDigit(0x13), BinaryDigit(0x02)]);
        assert_eq!(carry, BinaryDigit(0x2c));

        let mut n = [BinaryDigit(0u8), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let carry = div_assign_digit(&mut n, BinaryDigit(0xe6));
        assert_eq!(n, [BinaryDigit(0x35), BinaryDigit(0xce), BinaryDigit(0xbf), BinaryDigit(0x00)]);
        assert_eq!(carry, BinaryDigit(0x62));

        let mut n = [BinaryDigit(0u16), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let carry = div_assign_digit(&mut n, BinaryDigit(0xe6));
        assert_eq!(n, [BinaryDigit(0xd140), BinaryDigit(0xe42c), BinaryDigit(0xbf71), BinaryDigit(0x00)]);
        assert_eq!(carry, BinaryDigit(0x80));

        let mut n = [BinaryDigit(0x08762628u32), BinaryDigit(0x6afefe44), BinaryDigit(0x3981a76d), BinaryDigit(0xac)];
        let carry = div_assign_digit(&mut n, BinaryDigit(0xe6876a43));
        assert_eq!(n, [BinaryDigit(0xe779e424), BinaryDigit(0x40ef54e5), BinaryDigit(0xbf), BinaryDigit(0x00)]);
        assert_eq!(carry, BinaryDigit(0x541c88bc));
    }

    #[test]
    fn test_div_assign_digit_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        let carry = div_assign_digit(&mut n, DecimalDigit(53));
        assert_eq!(n, []);
        assert_eq!(carry, DecimalDigit(0));

        let mut n = [DecimalDigit(0u8), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let carry = div_assign_digit(&mut n, DecimalDigit(53));
        assert_eq!(n, [DecimalDigit(92), DecimalDigit(15), DecimalDigit(65), DecimalDigit(1)]);
        assert_eq!(carry, DecimalDigit(24));

        let mut n = [DecimalDigit(0u8), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let carry = div_assign_digit(&mut n, DecimalDigit(99));
        assert_eq!(n, [DecimalDigit(85), DecimalDigit(41), DecimalDigit(88), DecimalDigit(0)]);
        assert_eq!(carry, DecimalDigit(85));

        let mut n = [DecimalDigit(0u16), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let carry = div_assign_digit(&mut n, DecimalDigit(99));
        assert_eq!(n, [DecimalDigit(8_585), DecimalDigit(4_141), DecimalDigit(8_788), DecimalDigit(0)]);
        assert_eq!(carry, DecimalDigit(85));

        let mut n = [DecimalDigit(987_654_321u32), DecimalDigit(123_456_789), DecimalDigit(999_888_777), DecimalDigit(444_555_666)];
        let carry = div_assign_digit(&mut n, DecimalDigit(918_273_645));
        assert_eq!(n, [DecimalDigit(669_748_356), DecimalDigit(650_930_945), DecimalDigit(484_121__121), DecimalDigit(0)]);
        assert_eq!(carry, DecimalDigit(890_776_701));
    }

    #[test]
    fn test_div_pair_assign_digit_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x04), BinaryDigit(0x05));
        assert_eq!(n, []);
        assert_eq!(rem_low, BinaryDigit(0));
        assert_eq!(rem_high, BinaryDigit(0));

        let mut n = [BinaryDigit(0x88u8)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x04), BinaryDigit(0x05));
        assert_eq!(n, [BinaryDigit(0)]);
        assert_eq!(rem_low, BinaryDigit(0x88));
        assert_eq!(rem_high, BinaryDigit(0));

        let mut n = [BinaryDigit(0x88u8), BinaryDigit(0x04)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x04), BinaryDigit(0x05));
        assert_eq!(n, [BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(rem_low, BinaryDigit(0x88));
        assert_eq!(rem_high, BinaryDigit(0x04));

        let mut n = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x04), BinaryDigit(0x05));
        assert_eq!(n, [BinaryDigit(0x99), BinaryDigit(0x00), BinaryDigit(0x00)]);
        assert_eq!(rem_low, BinaryDigit(0x9d));
        assert_eq!(rem_high, BinaryDigit(0x02));

        let mut n = [BinaryDigit(0x5148u16), BinaryDigit(0x01a5), BinaryDigit(0xfd12), BinaryDigit(0x81a6), BinaryDigit(0x1983), BinaryDigit(0xfffa), BinaryDigit(0x8a51), BinaryDigit(0x7f91)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x8761), BinaryDigit(0x10ad));
        assert_eq!(n, [BinaryDigit(0xdc46), BinaryDigit(0xf00c), BinaryDigit(0xb68b), BinaryDigit(0xcd0c), BinaryDigit(0x8c94), BinaryDigit(0xa623), BinaryDigit(0x7), BinaryDigit(0)]);
        assert_eq!(rem_low, BinaryDigit(0xf0c2));
        assert_eq!(rem_high, BinaryDigit(0x094e));

        let mut n = [BinaryDigit(0x01a55148u32), BinaryDigit(0x81a6fd12), BinaryDigit(0xfffa1983), BinaryDigit(0x7f918a51)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, BinaryDigit(0x876110ad), BinaryDigit(0x05));
        assert_eq!(n, [BinaryDigit(0xb8e3b9c7), BinaryDigit(0x3d3d2c16), BinaryDigit(0x1712c723), BinaryDigit(0)]);
        assert_eq!(rem_low, BinaryDigit(0x7ebd55cd));
        assert_eq!(rem_high, BinaryDigit(0x4));
    }

    #[test]
    fn test_div_pair_assign_digit_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(4), DecimalDigit(5));
        assert_eq!(n, []);
        assert_eq!(rem_low, DecimalDigit(0));
        assert_eq!(rem_high, DecimalDigit(0));

        let mut n = [DecimalDigit(88u8)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(4), DecimalDigit(5));
        assert_eq!(n, [DecimalDigit(0)]);
        assert_eq!(rem_low, DecimalDigit(88));
        assert_eq!(rem_high, DecimalDigit(0));

        let mut n = [DecimalDigit(88u8), DecimalDigit(4)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(4), DecimalDigit(5));
        assert_eq!(n, [DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(rem_low, DecimalDigit(88));
        assert_eq!(rem_high, DecimalDigit(4));

        let mut n = [DecimalDigit(1u8), DecimalDigit(2), DecimalDigit(3)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(4), DecimalDigit(5));
        assert_eq!(n, [DecimalDigit(59), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(rem_low, DecimalDigit(65));
        assert_eq!(rem_high, DecimalDigit(4));

        let mut n = [DecimalDigit(8_291u16), DecimalDigit(9_818), DecimalDigit(1_782), DecimalDigit(8_181), DecimalDigit(79), DecimalDigit(3_181), DecimalDigit(9_716), DecimalDigit(2_191)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(4_534), DecimalDigit(1_982));
        assert_eq!(n, [DecimalDigit(7_899), DecimalDigit(6_751), DecimalDigit(5_211), DecimalDigit(3_817), DecimalDigit(8_633), DecimalDigit(1_056), DecimalDigit(1), DecimalDigit(0)]);
        assert_eq!(rem_low, DecimalDigit(4_225));
        assert_eq!(rem_high, DecimalDigit(1_385));

        let mut n = [DecimalDigit(738_181_009u32), DecimalDigit(198_118_981), DecimalDigit(345_123_731), DecimalDigit(673_291_756)];
        let (rem_low, rem_high) = div_pair_assign_digit(&mut n, DecimalDigit(21), DecimalDigit(287_278_981));
        assert_eq!(n, [DecimalDigit(102_985_940), DecimalDigit(343_686_106), DecimalDigit(2), DecimalDigit(0)]);
        assert_eq!(rem_low, DecimalDigit(575_476_269));
        assert_eq!(rem_high, DecimalDigit(80_183_613));
    }
}
