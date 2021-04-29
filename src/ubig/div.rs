use crate::digit::Digit;
use crate::result::{Error, Result};
use crate::ubig::support::drop_leading_zeros;

/// Calculate the remainder after dividing the number or number part represented by the digits in
/// `nr` by the single digit `fac`. If `fac` is zero, a `DivisionByZero` error is returned.
pub fn rem_digit<T>(nr: &[T], fac: T) -> Result<T>
where T: Digit
{
    if fac.is_zero()
    {
        Err(Error::DivisionByZero)
    }
    else
    {
        let rem = nr.iter().rev().fold(T::zero(), |carry, d| d.rem_carry(fac, carry));
        Ok(rem)
    }
}

/// Divide the number or number part represented by the digits in `nr` by 3. The carry should
/// be less than 3. Returns the number of digits in the quotient, and the remainder after the
/// division.
#[inline]
pub fn div3_carry_assign<T>(nr: &mut [T], carry: u8) -> (usize, u8)
where T: Digit
{
    let rem = nr.iter_mut().rev().fold(carry, |carry, d| d.div3_carry_assign(carry));
    let nd = drop_leading_zeros(nr, nr.len());
    (nd, rem)
}

/// Divide the number or number part represented by the digits in `nr` by the single digit `fac`.
/// Returns the nuber of digits in the quotient, and the remainder. If `fac` is zero, a
/// `DivisionByZero` error is returned.
pub fn div_assign_digit<T>(nr: &mut [T], fac: T) -> Result<(usize, T)>
where T: Digit
{
    if fac.is_zero()
    {
        Err(Error::DivisionByZero)
    }
    else
    {
        let rem = nr.iter_mut().rev().fold(T::zero(), |carry, d| d.div_carry_assign(fac, carry));
        let nquot = drop_leading_zeros(nr, nr.len());
        Ok((nquot, rem))
    }
}

/// Divide the number or number part represented by the digits in `nr` by the two-digit number
/// `fac_low + b*fac_high`, where `b` is the base of the number. Returns the numberof digits in
/// the quotient, and the digits of the remainder.
pub fn div_assign_digit_pair<T>(nr: &mut [T], fac_low: T, fac_high: T) -> Result<(usize, T, T)>
where T: Digit
{
    if fac_high.is_zero()
    {
        let (nquot, rem) = div_assign_digit(nr, fac_low)?;
        Ok((nquot, rem, T::zero()))
    }
    else
    {
        match nr.len()
        {
            0 => Ok((0, T::zero(), T::zero())),
            1 => { let rem_low = nr[0]; nr[0] = T::zero(); Ok((0, rem_low, T::zero())) },
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
                let nquot = drop_leading_zeros(nr, n);

                Ok((nquot, rem_low, rem_high))
            }
        }
    }
}

/// Divide the number or number part `num` by `den`, and store the quotient in `quot`, keeping
/// the remainder in `num`. If `den` is zero, a `DivisionByZero` error is returned. If `quot`
/// is not large enough to hold the quotient, a `NoSpace` error is returned. On success, returns
/// the number of digits in the quotient and the remainder, respectively.
pub fn div_big<T>(num: &mut [T], den: &[T], quot: &mut[T]) -> Result<(usize, usize)>
where T: Digit
{
    div_big_long(num, den, quot)
}

/// Divide the number or number part `num` by `den` using "schoolbook" long division, and store
/// the quotient in `quot`, keeping the remainder in `num`. If `den` is zero, a `DivisionByZero`
/// error is returned. If `quot` is not large enough to hold the quotient, a `NoSpace` error is
/// returned. On success, returns the number of digits in the quotient and the remainder,
/// respectively.
fn div_big_long<T>(num: &mut [T], den: &[T], quot: &mut[T]) -> Result<(usize, usize)>
where T: Digit
{
    let nnum = num.len();
    let nden = den.len();

    if den.is_empty()
    {
        Err(Error::DivisionByZero)
    }
    else if crate::ubig::cmp::lt(num, den)
    {
        Ok((0, num.len()))
    }
    else if quot.len() < nnum - nden + 1
    {
        Err(Error::NoSpace)
    }
    else if nden == 1
    {
        let (nquot, rem) = div_assign_digit(num, den[0])?;
        quot[..nquot].copy_from_slice(&num[..nquot]);
        if rem.is_zero()
        {
            Ok((nquot, 0))
        }
        else
        {
            num[0] = rem;
            Ok((nquot, 1))
        }
    }
    else if nden == 2
    {
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(num, den[0], den[1])?;
        quot[..nquot].copy_from_slice(&num[..nquot]);
        if rem_high.is_zero()
        {
            if rem_low.is_zero()
            {
                Ok((nquot, 0))
            }
            else
            {
                num[0] = rem_low;
                Ok((nquot, 1))
            }
        }
        else
        {
            num[0] = rem_low;
            num[1] = rem_high;
            Ok((nquot, 2))
        }
    }
    else
    {
        let shift = den[nden-1].max_shift() as usize;
        let mut scaled_den = den.to_vec();
        crate::ubig::shl::shl_carry_assign_within_digit(&mut scaled_den, shift, T::zero());
        let msd = scaled_den[nden-1];
        let mut carry = crate::ubig::shl::shl_carry_assign_within_digit(num, shift, T::zero());
        let mut qden = vec![T::zero(); nden+1];

        for iq in (0..nnum-nden+1).rev()
        {
            let mut q = num[iq+nden-1];
            q.div_carry_assign(msd, carry);
            if !q.is_zero()
            {
                qden[..nden].copy_from_slice(&scaled_den);
                qden[nden] = crate::ubig::mul::mul_add_assign_digit(&mut qden[..nden], q, T::zero());
                if qden[nden] > carry
                    || (qden[nden] == carry && crate::ubig::cmp::lt(&num[iq..iq+nden], &qden[..nden]))
                {
                    q.dec();
                    crate::ubig::sub::sub_assign_big(&mut qden, &scaled_den);
                    if qden[nden] > carry
                        || (qden[nden] == carry && crate::ubig::cmp::lt(&num[iq..iq+nden], &qden[..nden]))
                    {
                        q.dec();
                        crate::ubig::sub::sub_assign_big(&mut qden, &scaled_den);
                    }
                }

                crate::ubig::sub::sub_assign_big(&mut num[iq..iq+nden], &qden[..nden]);
            }

            quot[iq] = q;
            carry = num[iq+nden-1];
        }

        let nquot = drop_leading_zeros(quot, nnum-nden+1);
        let (nrem, _) = crate::ubig::shr::shr_carry_assign_within_digit(&mut num[..nden], shift, T::zero());

        Ok((nquot, nrem))
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::Zero;

    #[test]
    fn test_rem_digit_binary()
    {
        let n: [BinaryDigit<u8>; 0] = [];
        let rem = rem_digit(&n, BinaryDigit(0x23)).unwrap();
        assert_eq!(rem, BinaryDigit(0));

        let n = [BinaryDigit(0x34_u8), BinaryDigit(0x23), BinaryDigit(0xac), BinaryDigit(0x6f)];
        let rem = rem_digit(&n, BinaryDigit(0x23)).unwrap();
        assert_eq!(rem, BinaryDigit(0x0a));

        let n = [BinaryDigit(0x34_u16), BinaryDigit(0x23), BinaryDigit(0xac), BinaryDigit(0x6f)];
        let rem = rem_digit(&n, BinaryDigit(0x23)).unwrap();
        assert_eq!(rem, BinaryDigit(0x19));

        let n = [BinaryDigit(0x34726fd5_u32), BinaryDigit(0x23467fff), BinaryDigit(0x45fffd54)];
        let rem = rem_digit(&n, BinaryDigit(0xa53f542d)).unwrap();
        assert_eq!(rem, BinaryDigit(0x17330f46));

        let n = [
            BinaryDigit(0xa34726fd5f656622_u64),
            BinaryDigit(0x1234567823467fff),
            BinaryDigit(0x45fffd54d6f24acc),
            BinaryDigit(0x45fffd54d6f24acc)
        ];
        let rem = rem_digit(&n, BinaryDigit(0xa53f542d45cdfe23)).unwrap();
        assert_eq!(rem, BinaryDigit(0x53b0ca121b88387a));
    }

    #[test]
    fn test_rem_digit_decimal()
    {
        let n: [DecimalDigit<u8>; 0] = [];
        let rem = rem_digit(&n, DecimalDigit(23)).unwrap();
        assert_eq!(rem, DecimalDigit(0));

        let n = [DecimalDigit(34_u8), DecimalDigit(23), DecimalDigit(87), DecimalDigit(94)];
        let rem = rem_digit(&n, DecimalDigit(23)).unwrap();
        assert_eq!(rem, DecimalDigit(2));

        let n = [DecimalDigit(34_u16), DecimalDigit(23), DecimalDigit(87), DecimalDigit(94)];
        let rem = rem_digit(&n, DecimalDigit(23)).unwrap();
        assert_eq!(rem, DecimalDigit(4));

        let n = [DecimalDigit(786_333_654_u32), DecimalDigit(877_956_000), DecimalDigit(999)];
        let rem = rem_digit(&n, DecimalDigit(746_338_876)).unwrap();
        assert_eq!(rem, DecimalDigit(589_833_110));

        let n = [
            DecimalDigit(4_887_845_550_996_777_877_u64),
            DecimalDigit(3_569_987_999_789_676_455),
            DecimalDigit(6_767_888_677_923_221_344),
            DecimalDigit(2_898_999_342_484_877_009)
        ];
        let rem = rem_digit(&n, DecimalDigit(3_575_466_978_777_965_622)).unwrap();
        assert_eq!(rem, DecimalDigit(3_225_957_266_729_764_797));
    }

    #[test]
    fn test_div3_carry_assign_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        let (nd, rem) = div3_carry_assign(&mut n, 0);
        assert_eq!(nd, 0);
        assert_eq!(rem, 0);
        assert_eq!(n, []);

        let mut n = [BinaryDigit(0u8), BinaryDigit(0xfa), BinaryDigit(0x13), BinaryDigit(0xf2)];
        let (nd, rem) = div3_carry_assign(&mut n, 2);
        assert_eq!(nd, 4);
        assert_eq!(rem, 0);
        assert_eq!(n, [BinaryDigit(0), BinaryDigit(0xfe), BinaryDigit(0x5b), BinaryDigit(0xfb)]);

        let mut n = [BinaryDigit(0x761fu16), BinaryDigit(0xfa3d), BinaryDigit(0x1c3a)];
        let (nd, rem) = div3_carry_assign(&mut n, 0);
        assert_eq!(nd, 3);
        assert_eq!(rem, 0);
        assert_eq!(n, [BinaryDigit(0x7cb5), BinaryDigit(0xfe14), BinaryDigit(0x0968)]);

        let mut n = [BinaryDigit(0x1761f876u32), BinaryDigit(0xfa3dffe3), BinaryDigit(0x1c3ab218)];
        let (nd, rem) = div3_carry_assign(&mut n, 1);
        assert_eq!(nd, 3);
        assert_eq!(rem, 2);
        assert_eq!(n, [BinaryDigit(0xb275fd7c), BinaryDigit(0xa8bf554b), BinaryDigit(0x5ebe3b5d)]);

        let mut n = [BinaryDigit(0x1761f87678276ff5u64), BinaryDigit(0x8726f3f4fa3dffe3), BinaryDigit(0x1)];
        let (nd, rem) = div3_carry_assign(&mut n, 0);
        assert_eq!(nd, 2);
        assert_eq!(rem, 1);
        assert_eq!(n, [BinaryDigit(0xb275fd7cd2b7cffc), BinaryDigit(0x82625151a8bf554b), BinaryDigit(0)]);
    }

    #[test]
    fn test_div3_carry_assign_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        let (nd, rem) = div3_carry_assign(&mut n, 2);
        assert_eq!(nd, 0);
        assert_eq!(rem, 2);
        assert_eq!(n, []);

        let mut n = [DecimalDigit(0u8), DecimalDigit(35), DecimalDigit(98), DecimalDigit(22)];
        let (nd, rem) = div3_carry_assign(&mut n, 2);
        assert_eq!(nd, 4);
        assert_eq!(rem, 1);
        assert_eq!(n, [DecimalDigit(33), DecimalDigit(78), DecimalDigit(32), DecimalDigit(74)]);

        let mut n = [DecimalDigit(0u16), DecimalDigit(0), DecimalDigit(1)];
        let (nd, rem) = div3_carry_assign(&mut n, 1);
        assert_eq!(nd, 3);
        assert_eq!(rem, 2);
        assert_eq!(n, [DecimalDigit(6_666), DecimalDigit(6_666), DecimalDigit(3_333)]);

        let mut n = [DecimalDigit(0u16), DecimalDigit(0), DecimalDigit(1)];
        let (nd, rem) = div3_carry_assign(&mut n, 0);
        assert_eq!(nd, 2);
        assert_eq!(rem, 1);
        assert_eq!(n, [DecimalDigit(3_333), DecimalDigit(3_333), DecimalDigit(0)]);

        let mut n = [DecimalDigit(891_563_891u32), DecimalDigit(821_976_524), DecimalDigit(321_098_000)];
        let (nd, rem) = div3_carry_assign(&mut n, 0);
        assert_eq!(nd, 3);
        assert_eq!(rem, 0);
        assert_eq!(n, [DecimalDigit(630_521_297), DecimalDigit(940_658_841), DecimalDigit(107_032_666)]);

        let mut n = [DecimalDigit(5_891_563_891_999_567_342u64), DecimalDigit(1_821_976_524_213_465_888)];
        let (nd, rem) = div3_carry_assign(&mut n, 1);
        assert_eq!(nd, 2);
        assert_eq!(rem, 2);
        assert_eq!(n, [DecimalDigit(5_297_187_963_999_855_780), DecimalDigit(3_940_658_841_404_488_629)]);
    }

    #[test]
    fn test_div_assign_digit_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        let (nquot, rem) = div_assign_digit(&mut n, BinaryDigit(0x53)).unwrap();
        assert_eq!(n, []);
        assert_eq!(nquot, 0);
        assert_eq!(rem, BinaryDigit(0));

        let mut n = [BinaryDigit(0u8), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let (nquot, rem) = div_assign_digit(&mut n, BinaryDigit(0x53)).unwrap();
        assert_eq!(n, [BinaryDigit(0x5c), BinaryDigit(0x82), BinaryDigit(0x13), BinaryDigit(0x02)]);
        assert_eq!(nquot, 4);
        assert_eq!(rem, BinaryDigit(0x2c));

        let mut n = [BinaryDigit(0u8), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let (nquot, rem) = div_assign_digit(&mut n, BinaryDigit(0xe6)).unwrap();
        assert_eq!(n, [BinaryDigit(0x35), BinaryDigit(0xce), BinaryDigit(0xbf), BinaryDigit(0x00)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, BinaryDigit(0x62));

        let mut n = [BinaryDigit(0u16), BinaryDigit(0x44), BinaryDigit(0x53), BinaryDigit(0xac)];
        let (nquot, rem) = div_assign_digit(&mut n, BinaryDigit(0xe6)).unwrap();
        assert_eq!(n, [BinaryDigit(0xd140), BinaryDigit(0xe42c), BinaryDigit(0xbf71), BinaryDigit(0x00)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, BinaryDigit(0x80));

        let mut n = [BinaryDigit(0x08762628u32), BinaryDigit(0x6afefe44), BinaryDigit(0x3981a76d), BinaryDigit(0xac)];
        let (nquot, rem) = div_assign_digit(&mut n, BinaryDigit(0xe6876a43)).unwrap();
        assert_eq!(n, [BinaryDigit(0xe779e424), BinaryDigit(0x40ef54e5), BinaryDigit(0xbf), BinaryDigit(0x00)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, BinaryDigit(0x541c88bc));
    }

    #[test]
    fn test_div_assign_digit_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        let (nquot, rem) = div_assign_digit(&mut n, DecimalDigit(53)).unwrap();
        assert_eq!(n, []);
        assert_eq!(nquot, 0);
        assert_eq!(rem, DecimalDigit(0));

        let mut n = [DecimalDigit(0u8), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let (nquot, rem) = div_assign_digit(&mut n, DecimalDigit(53)).unwrap();
        assert_eq!(n, [DecimalDigit(92), DecimalDigit(15), DecimalDigit(65), DecimalDigit(1)]);
        assert_eq!(nquot, 4);
        assert_eq!(rem, DecimalDigit(24));

        let mut n = [DecimalDigit(0u8), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let (nquot, rem) = div_assign_digit(&mut n, DecimalDigit(99)).unwrap();
        assert_eq!(n, [DecimalDigit(85), DecimalDigit(41), DecimalDigit(88), DecimalDigit(0)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, DecimalDigit(85));

        let mut n = [DecimalDigit(0u16), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let (nquot, rem) = div_assign_digit(&mut n, DecimalDigit(99)).unwrap();
        assert_eq!(n, [DecimalDigit(8_585), DecimalDigit(4_141), DecimalDigit(8_788), DecimalDigit(0)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, DecimalDigit(85));

        let mut n = [DecimalDigit(987_654_321u32), DecimalDigit(123_456_789), DecimalDigit(999_888_777), DecimalDigit(444_555_666)];
        let (nquot, rem) = div_assign_digit(&mut n, DecimalDigit(918_273_645)).unwrap();
        assert_eq!(n, [DecimalDigit(669_748_356), DecimalDigit(650_930_945), DecimalDigit(484_121__121), DecimalDigit(0)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem, DecimalDigit(890_776_701));
    }

    #[test]
    fn test_div_assign_digit_zero()
    {
        let mut n = [BinaryDigit(0xdfff827208762628u64), BinaryDigit(0x736fe25f6afefe44), BinaryDigit(0x3981a76d), BinaryDigit(0xac)];
        let res = div_assign_digit(&mut n, BinaryDigit(0));
        assert_eq!(res, Err(Error::DivisionByZero));

        let mut n = [DecimalDigit(0u8), DecimalDigit(44), DecimalDigit(53), DecimalDigit(87)];
        let res = div_assign_digit(&mut n, DecimalDigit(0));
        assert_eq!(res, Err(Error::DivisionByZero));
    }

    #[test]
    fn test_div_assign_digit_pair_binary()
    {
        let mut n: [BinaryDigit<u8>; 0] = [];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x04), BinaryDigit(0x05)).unwrap();
        assert_eq!(n, []);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, BinaryDigit(0));
        assert_eq!(rem_high, BinaryDigit(0));

        let mut n = [BinaryDigit(0x88u8)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x04), BinaryDigit(0x05)).unwrap();
        assert_eq!(n, [BinaryDigit(0)]);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, BinaryDigit(0x88));
        assert_eq!(rem_high, BinaryDigit(0));

        let mut n = [BinaryDigit(0x88u8), BinaryDigit(0x04)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x04), BinaryDigit(0x05)).unwrap();
        assert_eq!(n, [BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, BinaryDigit(0x88));
        assert_eq!(rem_high, BinaryDigit(0x04));

        let mut n = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x04), BinaryDigit(0x05)).unwrap();
        assert_eq!(n, [BinaryDigit(0x99), BinaryDigit(0x00), BinaryDigit(0x00)]);
        assert_eq!(nquot, 1);
        assert_eq!(rem_low, BinaryDigit(0x9d));
        assert_eq!(rem_high, BinaryDigit(0x02));

        let mut n = [BinaryDigit(0x5148u16), BinaryDigit(0x01a5), BinaryDigit(0xfd12), BinaryDigit(0x81a6), BinaryDigit(0x1983), BinaryDigit(0xfffa), BinaryDigit(0x8a51), BinaryDigit(0x7f91)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x8761), BinaryDigit(0x10ad)).unwrap();
        assert_eq!(n, [BinaryDigit(0xdc46), BinaryDigit(0xf00c), BinaryDigit(0xb68b), BinaryDigit(0xcd0c), BinaryDigit(0x8c94), BinaryDigit(0xa623), BinaryDigit(0x7), BinaryDigit(0)]);
        assert_eq!(nquot, 7);
        assert_eq!(rem_low, BinaryDigit(0xf0c2));
        assert_eq!(rem_high, BinaryDigit(0x094e));

        let mut n = [BinaryDigit(0x01a55148u32), BinaryDigit(0x81a6fd12), BinaryDigit(0xfffa1983), BinaryDigit(0x7f918a51)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, BinaryDigit(0x876110ad), BinaryDigit(0x05)).unwrap();
        assert_eq!(n, [BinaryDigit(0xb8e3b9c7), BinaryDigit(0x3d3d2c16), BinaryDigit(0x1712c723), BinaryDigit(0)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem_low, BinaryDigit(0x7ebd55cd));
        assert_eq!(rem_high, BinaryDigit(0x4));
    }

    #[test]
    fn test_div_assign_digit_pair_decimal()
    {
        let mut n: [DecimalDigit<u8>; 0] = [];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(4), DecimalDigit(5)).unwrap();
        assert_eq!(n, []);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, DecimalDigit(0));
        assert_eq!(rem_high, DecimalDigit(0));

        let mut n = [DecimalDigit(88u8)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(4), DecimalDigit(5)).unwrap();
        assert_eq!(n, [DecimalDigit(0)]);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, DecimalDigit(88));
        assert_eq!(rem_high, DecimalDigit(0));

        let mut n = [DecimalDigit(88u8), DecimalDigit(4)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(4), DecimalDigit(5)).unwrap();
        assert_eq!(n, [DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(nquot, 0);
        assert_eq!(rem_low, DecimalDigit(88));
        assert_eq!(rem_high, DecimalDigit(4));

        let mut n = [DecimalDigit(1u8), DecimalDigit(2), DecimalDigit(3)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(4), DecimalDigit(5)).unwrap();
        assert_eq!(n, [DecimalDigit(59), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(nquot, 1);
        assert_eq!(rem_low, DecimalDigit(65));
        assert_eq!(rem_high, DecimalDigit(4));

        let mut n = [DecimalDigit(8_291u16), DecimalDigit(9_818), DecimalDigit(1_782), DecimalDigit(8_181), DecimalDigit(79), DecimalDigit(3_181), DecimalDigit(9_716), DecimalDigit(2_191)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(4_534), DecimalDigit(1_982)).unwrap();
        assert_eq!(n, [DecimalDigit(7_899), DecimalDigit(6_751), DecimalDigit(5_211), DecimalDigit(3_817), DecimalDigit(8_633), DecimalDigit(1_056), DecimalDigit(1), DecimalDigit(0)]);
        assert_eq!(nquot, 7);
        assert_eq!(rem_low, DecimalDigit(4_225));
        assert_eq!(rem_high, DecimalDigit(1_385));

        let mut n = [DecimalDigit(738_181_009u32), DecimalDigit(198_118_981), DecimalDigit(345_123_731), DecimalDigit(673_291_756)];
        let (nquot, rem_low, rem_high) = div_assign_digit_pair(&mut n, DecimalDigit(21), DecimalDigit(287_278_981)).unwrap();
        assert_eq!(n, [DecimalDigit(102_985_940), DecimalDigit(343_686_106), DecimalDigit(2), DecimalDigit(0)]);
        assert_eq!(nquot, 3);
        assert_eq!(rem_low, DecimalDigit(575_476_269));
        assert_eq!(rem_high, DecimalDigit(80_183_613));
    }

    #[test]
    fn test_div_assign_digit_pair_zero()
    {
        let mut n = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03)];
        let res = div_assign_digit_pair(&mut n, BinaryDigit(0), BinaryDigit(0));
        assert_eq!(res, Err(Error::DivisionByZero));

        let mut n = [DecimalDigit(8_291u16), DecimalDigit(9_818), DecimalDigit(1_782), DecimalDigit(8_181), DecimalDigit(79), DecimalDigit(3_181), DecimalDigit(9_716), DecimalDigit(2_191)];
        let res = div_assign_digit_pair(&mut n, DecimalDigit(0), DecimalDigit(0));
        assert_eq!(res, Err(Error::DivisionByZero));
    }

    #[test]
    fn test_div_big_long_binary()
    {
        let mut num: [BinaryDigit<u8>; 0] = [];
        let den = [BinaryDigit(0x53), BinaryDigit(0x12), BinaryDigit(0x91)];
        let mut quot = [BinaryDigit::zero(); 0];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 0);
        assert_eq!(nrem, 0);
        assert_eq!(quot, []);
        assert_eq!(num, []);

        let mut num = [
            BinaryDigit(0x43u8),
            BinaryDigit(0x98),
            BinaryDigit(0x12),
            BinaryDigit(0xfe),
            BinaryDigit(0xf2),
            BinaryDigit(0x43)
        ];
        let den = [BinaryDigit(0x53u8), BinaryDigit(0x12), BinaryDigit(0x91)];
        let mut quot = [BinaryDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [BinaryDigit(0x01), BinaryDigit(0xe8), BinaryDigit(0x77), BinaryDigit(0)]);
        assert_eq!(num[..nrem], [BinaryDigit(0xf0), BinaryDigit(0x4d), BinaryDigit(0x51)]);

        let mut num = [
            BinaryDigit(0x6734_u16),
            BinaryDigit(0x6712),
            BinaryDigit(0x29fd),
            BinaryDigit(0xff33),
            BinaryDigit(0x657c)
        ];
        let den = [BinaryDigit(0x7df3), BinaryDigit(0x0123)];
        let mut quot = [BinaryDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 4);
        assert_eq!(nrem, 2);
        assert_eq!(quot, [BinaryDigit(0x204d), BinaryDigit(0xb324), BinaryDigit(0x218e), BinaryDigit(0x59)]);
        assert_eq!(num[..nrem], [BinaryDigit(0x251d), BinaryDigit(0x7b)]);

        let mut num = [
            BinaryDigit(0x67347fff_u32),
            BinaryDigit(0x67120009),
            BinaryDigit(0x29fd47fd),
            BinaryDigit(0xff33ff33),
            BinaryDigit(0x657cc982)
        ];
        let den = [BinaryDigit(0x79ff5df3), BinaryDigit(0x12345678), BinaryDigit(0x63726fff)];
        let mut quot = [BinaryDigit::zero(); 3];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [BinaryDigit(0xc86d03d2), BinaryDigit(0x0540a699), BinaryDigit(0x01)]);
        assert_eq!(num[..nrem], [BinaryDigit(0x7d2895a9), BinaryDigit(0x2e397c6b), BinaryDigit(0x05201ff6)]);

        let mut num = [
            BinaryDigit(0x67347fff71ff453d_u64),
            BinaryDigit(0x671200092314d4ff),
        ];
        let den = [BinaryDigit(0xf5df399f64736df5), BinaryDigit(0x1234567879f73882), BinaryDigit(0x63726fff)];
        let mut quot = [BinaryDigit::zero(); 3];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 0);
        assert_eq!(nrem, 2);
        assert_eq!(quot, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(num[..nrem], [BinaryDigit(0x67347fff71ff453d), BinaryDigit(0x671200092314d4ff)]);

        let mut num = [
            BinaryDigit(0x67347fff71ff453d_u64),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff),
            BinaryDigit(0x671200092314d4ff)
        ];
        let den = [BinaryDigit(0xf5df399f64736df5), BinaryDigit(0x1234567879f73882), BinaryDigit(0x63726fff)];
        let mut quot = [BinaryDigit::zero(); 8];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 8);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [
            BinaryDigit(0x27f8b7e7788703ea),
            BinaryDigit(0x3b5e4d976379c4f3),
            BinaryDigit(0x1717b5f7323cc94d),
            BinaryDigit(0x5de408c5942c0da8),
            BinaryDigit(0x04f1f91c8cb7ccb0),
            BinaryDigit(0x864896085c32ab49),
            BinaryDigit(0xc4941a9bd6f3e486),
            BinaryDigit(0x010953c3a3)
        ]);
        assert_eq!(num[..nrem], [
            BinaryDigit(0xf13e86a371ffe44b),
            BinaryDigit(0x9f6724dd963e8fea),
            BinaryDigit(0x5fb91280)
        ]);
    }

    #[test]
    fn test_div_big_long_decimal()
    {
        let mut num: [DecimalDigit<u8>; 0] = [];
        let den = [DecimalDigit(53), DecimalDigit(12), DecimalDigit(91)];
        let mut quot = [DecimalDigit::zero(); 0];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 0);
        assert_eq!(nrem, 0);
        assert_eq!(quot, []);
        assert_eq!(num, []);

        let mut num = [
            DecimalDigit(43u8),
            DecimalDigit(98),
            DecimalDigit(12),
            DecimalDigit(98),
            DecimalDigit(92),
            DecimalDigit(43)
        ];
        let den = [DecimalDigit(53u8), DecimalDigit(12), DecimalDigit(91)];
        let mut quot = [DecimalDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [DecimalDigit(81), DecimalDigit(20), DecimalDigit(48), DecimalDigit(0)]);
        assert_eq!(num[..nrem], [DecimalDigit(50), DecimalDigit(23), DecimalDigit(37)]);

        let mut num = [
            DecimalDigit(4_453_u16),
            DecimalDigit(3_885),
            DecimalDigit(3_324),
            DecimalDigit(8_998),
            DecimalDigit(6_754)
        ];
        let den = [DecimalDigit(3_756), DecimalDigit(123)];
        let mut quot = [DecimalDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 4);
        assert_eq!(nrem, 2);
        assert_eq!(quot, [DecimalDigit(6_267), DecimalDigit(9_489), DecimalDigit(7_506), DecimalDigit(54)]);
        assert_eq!(num[..nrem], [DecimalDigit(5_601), DecimalDigit(6)]);

        let mut num = [
            DecimalDigit(736_877_958_u32),
            DecimalDigit(473_222_398),
            DecimalDigit(123_987_987),
            DecimalDigit(857_833_398),
            DecimalDigit(12_345)
        ];
        let den = [DecimalDigit(847_928_000), DecimalDigit(340_987_987), DecimalDigit(345_756_986)];
        let mut quot = [DecimalDigit::zero(); 3];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 2);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [DecimalDigit(748_731_383), DecimalDigit(35_706), DecimalDigit(0)]);
        assert_eq!(num[..nrem], [DecimalDigit(612_453_958), DecimalDigit(628_288_073), DecimalDigit(241_893_843)]);

        let mut num = [
            DecimalDigit(2_827_928_982_748_837_756_u64),
            DecimalDigit(9_987_857_888_374_321_333),
        ];
        let den = [
            DecimalDigit(3_464_444_454_444_454_777),
            DecimalDigit(9_399_999_474_765_588_888),
            DecimalDigit(867_984_998_999_572_288)
        ];
        let mut quot = [DecimalDigit::zero(); 3];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 0);
        assert_eq!(nrem, 2);
        assert_eq!(quot, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(num[..nrem], [DecimalDigit(2_827_928_982_748_837_756), DecimalDigit(9_987_857_888_374_321_333)]);

        let mut num = [
            DecimalDigit(2_827_928_982_748_837_756_u64),
            DecimalDigit(9_987_857_888_374_321_333),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
            DecimalDigit(9_567_099_055_999_999_999),
        ];
        let den = [
            DecimalDigit(3_464_444_454_444_454_777),
            DecimalDigit(9_399_999_474_765_588_888),
            DecimalDigit(867_984_998_999_572_288)
        ];
        let mut quot = [DecimalDigit::zero(); 11];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot).unwrap();
        assert_eq!(nquot, 11);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [
            DecimalDigit(2_739_132_595_692_916_609),
            DecimalDigit(  186_009_061_497_178_731),
            DecimalDigit(3_515_246_891_635_834_223),
            DecimalDigit(1_016_137_553_008_377_404),
            DecimalDigit(9_633_276_126_066_576_086),
            DecimalDigit(4_265_899_626_824_713_455),
            DecimalDigit(2_736_435_672_850_267_122),
            DecimalDigit(3_717_274_131_184_765_525),
            DecimalDigit(6_660_916_798_959_678_502),
            DecimalDigit(  221_940_091_440_616_178),
            DecimalDigit(                       11)
        ]);
        assert_eq!(num[..nrem], [
            DecimalDigit(2_701_266_084_816_146_563),
            DecimalDigit(3_684_527_600_083_895_574),
            DecimalDigit(347_460_090_911_990_341)
        ]);
    }

    #[test]
    fn test_div_big_long_zero()
    {
        let mut num = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03)];
        let den: [BinaryDigit<u8>; 0] = [];
        let mut quot = [BinaryDigit(0); 4];
        let res = div_big_long(&mut num, &den, &mut quot);
        assert_eq!(res, Err(Error::DivisionByZero));

        let mut num = [DecimalDigit(1u64), DecimalDigit(2), DecimalDigit(3)];
        let den: [DecimalDigit<u64>; 0] = [];
        let mut quot = [DecimalDigit(0); 4];
        let res = div_big_long(&mut num, &den, &mut quot);
        assert_eq!(res, Err(Error::DivisionByZero));
    }

    #[test]
    fn test_div_big_no_space()
    {
        let mut num = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03), BinaryDigit(0x04), BinaryDigit(0x05)];
        let den = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03)];
        let mut quot = [BinaryDigit(0); 2];
        let res = div_big_long(&mut num, &den, &mut quot);
        assert_eq!(res, Err(Error::NoSpace));

        let mut num = [DecimalDigit(1u64), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4), DecimalDigit(5)];
        let den = [DecimalDigit(1u64), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)];
        let mut quot = [DecimalDigit(0); 1];
        let res = div_big_long(&mut num, &den, &mut quot);
        assert_eq!(res, Err(Error::NoSpace));
    }
}
