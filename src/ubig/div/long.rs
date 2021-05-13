use crate::digit::Digit;
use crate::ubig::support::drop_leading_zeros;

/// Calculate the minimum size of the scratch array needed for long division with a denominator
/// of `nden` digits.
pub fn calc_div_long_work_size(nden: usize) -> usize
{
    nden + 1
}

/// Divide the number or number part `num` by `den` using "schoolbook" long division, and store
/// the quotient in `quot`, keeping the remainder in `num`. The number of digits `nden` in `den`
/// should at least be three, `num` should not be less than `den`, and `quot` should be able to hold
/// at least `nnum - nden + 1` digits, where `nnum` is the number of digits in `num`.
/// Returns the number of digits in the quotient and the remainder, respectively.
pub fn div_big_long<T>(num: &mut [T], den: &[T], quot: &mut[T], work: &mut [T]) -> (usize, usize)
where T: Digit
{
    let nnum = num.len();
    let nden = den.len();

    debug_assert!(nden > 2);
    debug_assert!(nnum >= nden);
    debug_assert!(quot.len() >= nnum - nden + 1
        || (quot.len() >= nnum - nden && crate::ubig::cmp::lt(&num[nnum-nden..], den)));
    debug_assert!(work.len() >= calc_div_long_work_size(nden));

    let shift = den[nden-1].max_shift() as usize;
    if shift == 0
    {
        div_big_long_scaled(num, T::zero(), den, quot, work)
    }
    else
    {
        // Shift numerator and denominator such that the most significant digit of the denominator
        // is at least half the radix of this number. This way, estimates for the quotient digits
        // in div_big_long_scaled() are at most 2 too high.
        let mut scaled_den = den.to_vec();
        crate::ubig::shl::shl_carry_assign_within_digit(&mut scaled_den, shift, T::zero());
        let num_msd = crate::ubig::shl::shl_carry_assign_within_digit(num, shift, T::zero());
        let qden = &mut work[..nden+1];
        let (nquot, nrem) = div_big_long_scaled(num, num_msd, &mut scaled_den, quot, qden);
        let (nrem, _) = crate::ubig::shr::shr_carry_assign_within_digit(&mut num[..nrem], shift, T::zero());
        (nquot, nrem)
    }
}

fn div_big_long_scaled<T>(num: &mut [T], num_msd: T, den: &[T], quot: &mut[T], work: &mut [T])
    -> (usize, usize)
where T: Digit
{
    let nnum = num.len();
    let nden = den.len();

    let msd = den[nden-1];
    debug_assert!(msd.max_shift() == 0);
    let qden = &mut work[..nden+1];

    // Handle first digit separately, since if it's zero, we need one less digit in `quot` and
    // don't store it. This is mostly useful for the BZ division.
    let mut carry = num_msd;
    let mut nquot = nnum - nden + 1;
    let mut q = num[nnum-1];
    q.div_carry_assign(msd, carry);
    if q.is_zero()
    {
        nquot -= 1;
    }
    else
    {
        qden[..nden].copy_from_slice(&den);
        qden[nden] = crate::ubig::mul::mul_add_assign_digit(&mut qden[..nden], q, T::zero());
        if qden[nden] > carry
            || (qden[nden] == carry && crate::ubig::cmp::lt(&num[nnum-nden..], &qden[..nden]))
        {
            q.dec();
            let _ = crate::ubig::sub::sub_assign_big(qden, &den);
            if qden[nden] > carry
                || (qden[nden] == carry && crate::ubig::cmp::lt(&num[nnum-nden..], &qden[..nden]))
            {
                q.dec();
                let _ = crate::ubig::sub::sub_assign_big(qden, &den);
            }
        }

        let _ = crate::ubig::sub::sub_assign_big(&mut num[nnum-nden..], &qden[..nden]);
        quot[nquot-1] = q;
    }

    // Now handle the other digits
    carry = num[nnum-1];
    for iq in (0..nnum-nden).rev()
    {
        q = num[iq+nden-1];
        q.div_carry_assign(msd, carry);
        if !q.is_zero()
        {
            qden[..nden].copy_from_slice(&den);
            qden[nden] = crate::ubig::mul::mul_add_assign_digit(&mut qden[..nden], q, T::zero());
            if qden[nden] > carry
                || (qden[nden] == carry && crate::ubig::cmp::lt(&num[iq..iq+nden], &qden[..nden]))
            {
                q.dec();
                let _ = crate::ubig::sub::sub_assign_big(qden, &den);
                if qden[nden] > carry
                    || (qden[nden] == carry && crate::ubig::cmp::lt(&num[iq..iq+nden], &qden[..nden]))
                {
                    q.dec();
                    let _ = crate::ubig::sub::sub_assign_big(qden, &den);
                }
            }

            let _ = crate::ubig::sub::sub_assign_big(&mut num[iq..iq+nden+1], qden);
        }

        quot[iq] = q;
        carry = num[iq+nden-1];
    }

    nquot = drop_leading_zeros(quot, nquot);
    let nrem = drop_leading_zeros(num, nden);

    (nquot, nrem)
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::Zero;

    #[test]
    fn test_div_big_long_binary()
    {
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
        let mut work = [BinaryDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [BinaryDigit(0x01), BinaryDigit(0xe8), BinaryDigit(0x77), BinaryDigit(0)]);
        assert_eq!(num[..nrem], [BinaryDigit(0xf0), BinaryDigit(0x4d), BinaryDigit(0x51)]);

        let mut num = [
            BinaryDigit(0x67347fff_u32),
            BinaryDigit(0x67120009),
            BinaryDigit(0x29fd47fd),
            BinaryDigit(0xff33ff33),
            BinaryDigit(0x657cc982)
        ];
        let den = [BinaryDigit(0x79ff5df3), BinaryDigit(0x12345678), BinaryDigit(0x63726fff)];
        let mut quot = [BinaryDigit::zero(); 3];
        let mut work = [BinaryDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [BinaryDigit(0xc86d03d2), BinaryDigit(0x0540a699), BinaryDigit(0x01)]);
        assert_eq!(num[..nrem], [BinaryDigit(0x7d2895a9), BinaryDigit(0x2e397c6b), BinaryDigit(0x05201ff6)]);

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
        let mut work = [BinaryDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
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
        let mut work = [DecimalDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [DecimalDigit(81), DecimalDigit(20), DecimalDigit(48), DecimalDigit(0)]);
        assert_eq!(num[..nrem], [DecimalDigit(50), DecimalDigit(23), DecimalDigit(37)]);

        let mut num = [
            DecimalDigit(736_877_958_u32),
            DecimalDigit(473_222_398),
            DecimalDigit(123_987_987),
            DecimalDigit(857_833_398),
            DecimalDigit(12_345)
        ];
        let den = [DecimalDigit(847_928_000), DecimalDigit(340_987_987), DecimalDigit(345_756_986)];
        let mut quot = [DecimalDigit::zero(); 3];
        let mut work = [DecimalDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 2);
        assert_eq!(nrem, 3);
        assert_eq!(quot, [DecimalDigit(748_731_383), DecimalDigit(35_706), DecimalDigit(0)]);
        assert_eq!(num[..nrem], [DecimalDigit(612_453_958), DecimalDigit(628_288_073), DecimalDigit(241_893_843)]);

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
        let mut work = [DecimalDigit::zero(); 4];
        let (nquot, nrem) = div_big_long(&mut num, &den, &mut quot, &mut work);
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
}
