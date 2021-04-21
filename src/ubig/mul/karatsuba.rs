use crate::digit::Digit;
use crate::ubig::support::drop_leading_zeros;

/// Calculate the maximum size of the scratch array necessary to perform Karatsuba multiplication
/// on two `n`-digit numbers.
pub const fn calc_karatsuba_work_size(n: usize) -> usize
{
    let mut work_size = 0;
    let mut nn = n;
    while nn >= super::KARATSUBA_CUTOFF
    {
        let split = (nn + 1) / 2;
        work_size += 2 * split;
        nn = split;
    }
    work_size
}

/// Multiply the number represented by `nr0` by `nr1` using Karatsuba multiplication, and store
/// the result in `result`. The scratch array `work` should be of appropriate size
/// (see [calc_karatsuba_work_size()](calc_karatsuba_work_size)). The result array must
/// have space for at least `n0+n1` digits, where `n0` denotes the number of digits in ths
/// borrow, and `n1` the number of digits in `other`. Returns the number of digits in the product.
pub fn mul_big_karatsuba_into<T>(nr0: &[T], nr1: &[T], result: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    let nmax = n0.max(n1);
    assert!(n0 >= 2 && n1 >= 2, "Number of digits should be at least 2 for Karatsuba multiplication");
    assert!(work.len() >= calc_karatsuba_work_size(nmax), "Insufficient work space");

    let split = (nmax + 1) / 2;

    let (low0, high0) = nr0.split_at(split.min(n0));
    let nlow0 = drop_leading_zeros(low0, low0.len());
    let (low1, high1) = nr1.split_at(split.min(n1));
    let nlow1 = drop_leading_zeros(low1, low1.len());

    let (diff0, diff1) = result.split_at_mut(split);
    let (sign0, ndiff0) = crate::ubig::sub::sub_big_into_abs_sign(&low0[..nlow0], &high0, diff0); // low0 - high0
    let (sign1, ndiff1) = crate::ubig::sub::sub_big_into_abs_sign(&low1[..nlow1], &high1, diff1); // low1 - high1

    let (z1, new_work) = work.split_at_mut(2*split);
    z1.fill(T::zero());
    // |(low0-high0)*(low1-high1)|
    let mut nz1 = super::mul_big_into_with_work(&diff0[..ndiff0], &diff1[..ndiff1], z1, new_work);
    result[..n0+n1].fill(T::zero());
    let (z0, z2) = result.split_at_mut(2*split);
    let nz0 = super::mul_big_into_with_work(&low0[..nlow0], &low1[..nlow1], z0, new_work); // low0*low1
    let nz2 = super::mul_big_into_with_work(&high0, &high1, z2, new_work);                 // high0*high1

    // Now calculate z1 = low0*high1 + high0*low1
    if sign0 ^ sign1
    {
        nz1 = nz1.max(nz0).max(nz2);
        let carry0 = crate::ubig::add::add_assign_big(&mut z1[..nz1], &z0[..nz0]);
        let carry2 = crate::ubig::add::add_assign_big(&mut z1[..nz1], &z2[..nz2]);
        if carry0
        {
            crate::ubig::add::inc_assign(&mut result[split+nz1..]);
        }
        if carry2
        {
            crate::ubig::add::inc_assign(&mut result[split+nz1..]);
        }
    }
    else if crate::ubig::cmp::lt(&z1[..nz1], &z0[..nz0])
    {
        crate::ubig::rsub::rsub_assign_big(&mut z1[..nz0], &z0[..nz0]);
        nz1 = drop_leading_zeros(z1, nz0).max(nz2);
        if crate::ubig::add::add_assign_big(&mut z1[..nz1], &z2[..nz2])
        {
            crate::ubig::add::inc_assign(&mut result[split+nz1..]);
        }
    }
    else
    {
        crate::ubig::sub::sub_assign_big(z1, &z0[..nz0]);
        nz1 = drop_leading_zeros(z1, nz1);
        debug_assert!(!crate::ubig::cmp::lt(&z2[..nz2], &z1[..nz1]), "z1 < 0");
        crate::ubig::rsub::rsub_assign_big(&mut z1[..nz2], &z2[..nz2]);
        nz1 = drop_leading_zeros(z1, nz2);
    }

    let carry = crate::ubig::add::add_assign_big(&mut result[split..], &z1[..nz1]);
    assert!(!carry);

    drop_leading_zeros(result, n0+n1)
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::Zero;

    #[test]
    fn test_mul_big_into_karatsuba_binary()
    {
        let nr0 = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)];
        let nr1 = [BinaryDigit(1u8), BinaryDigit(2), BinaryDigit(3), BinaryDigit(4)];
        let mut result = [BinaryDigit::zero(); 8];
        let mut work = [BinaryDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 0);
        assert_eq!(result, [BinaryDigit(0); 8]);

        let nr0 = [BinaryDigit(0x08u8), BinaryDigit(0x09), BinaryDigit(0x10), BinaryDigit(0x11)];
        let nr1 = [BinaryDigit(0x01u8), BinaryDigit(0x02), BinaryDigit(0x03), BinaryDigit(0x04)];
        let mut result = [BinaryDigit::zero(); 8];
        let mut work = [BinaryDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 7);
        assert_eq!(result, [
            BinaryDigit(0x08),
            BinaryDigit(0x19),
            BinaryDigit(0x3a),
            BinaryDigit(0x6c),
            BinaryDigit(0x76),
            BinaryDigit(0x73),
            BinaryDigit(0x44),
            BinaryDigit(0)
        ]);

        let nr0 = [BinaryDigit(0x08u8), BinaryDigit(0x09), BinaryDigit(0x10), BinaryDigit(0x11), BinaryDigit(0xf8), BinaryDigit(0x82)];
        let nr1 = [BinaryDigit(0xf8u8), BinaryDigit(0x82), BinaryDigit(0x33), BinaryDigit(0xf4)];
        let mut result = [BinaryDigit::zero(); 10];
        let mut work = [BinaryDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 10);
        assert_eq!(result, [
            BinaryDigit(0xc0),
            BinaryDigit(0xcf),
            BinaryDigit(0xb6),
            BinaryDigit(0x18),
            BinaryDigit(0xc8),
            BinaryDigit(0x87),
            BinaryDigit(0xaf),
            BinaryDigit(0xca),
            BinaryDigit(0xee),
            BinaryDigit(0x7c)
        ]);

        let nr0 = [BinaryDigit(0xf8u8), BinaryDigit(0x82), BinaryDigit(0x33), BinaryDigit(0xf4)];
        let nr1 = [BinaryDigit(0x08u8), BinaryDigit(0x09), BinaryDigit(0x10), BinaryDigit(0x11), BinaryDigit(0xf8), BinaryDigit(0x82)];
        let mut result = [BinaryDigit::zero(); 10];
        let mut work = [BinaryDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 10);
        assert_eq!(result, [
            BinaryDigit(0xc0),
            BinaryDigit(0xcf),
            BinaryDigit(0xb6),
            BinaryDigit(0x18),
            BinaryDigit(0xc8),
            BinaryDigit(0x87),
            BinaryDigit(0xaf),
            BinaryDigit(0xca),
            BinaryDigit(0xee),
            BinaryDigit(0x7c)
        ]);

        let nr0 = [BinaryDigit(0x08u64), BinaryDigit(0x09), BinaryDigit(0x10), BinaryDigit(0x11), BinaryDigit(0xf8), BinaryDigit(0x82)];
        let nr1 = [BinaryDigit(0xf8u64), BinaryDigit(0x82), BinaryDigit(0x33), BinaryDigit(0xf4)];
        let mut result = [BinaryDigit::zero(); 10];
        let mut work = [BinaryDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 9);
        assert_eq!(result, [
            BinaryDigit(0x7c0),
            BinaryDigit(0xcc8),
            BinaryDigit(0x15aa),
            BinaryDigit(0x2203),
            BinaryDigit(0x104a6),
            BinaryDigit(0x10e83),
            BinaryDigit(0x83a0),
            BinaryDigit(0x10646),
            BinaryDigit(0x7be8),
            BinaryDigit(0)
        ]);
    }

    #[test]
    fn test_mul_big_into_karatsuba_decimal()
    {
        let nr0 = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)];
        let nr1 = [DecimalDigit(1u8), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)];
        let mut result = [DecimalDigit::zero(); 8];
        let mut work = [DecimalDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 0);
        assert_eq!(result, [DecimalDigit(0); 8]);

        let nr0 = [DecimalDigit(8u8), DecimalDigit(9), DecimalDigit(10), DecimalDigit(11)];
        let nr1 = [DecimalDigit(1u8), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)];
        let mut result = [DecimalDigit::zero(); 8];
        let mut work = [DecimalDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 7);
        assert_eq!(result, [
            DecimalDigit(8),
            DecimalDigit(25),
            DecimalDigit(52),
            DecimalDigit(90),
            DecimalDigit(88),
            DecimalDigit(73),
            DecimalDigit(44),
            DecimalDigit(0)
        ]);

        let nr0 = [DecimalDigit(8u8), DecimalDigit(9), DecimalDigit(10), DecimalDigit(11), DecimalDigit(98), DecimalDigit(52)];
        let nr1 = [DecimalDigit(98u8), DecimalDigit(52), DecimalDigit(33), DecimalDigit(94)];
        let mut result = [DecimalDigit::zero(); 10];
        let mut work = [DecimalDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 10);
        assert_eq!(result, [
            DecimalDigit(84),
            DecimalDigit(5),
            DecimalDigit(25),
            DecimalDigit(64),
            DecimalDigit(78),
            DecimalDigit(08),
            DecimalDigit(88),
            DecimalDigit(98),
            DecimalDigit(97),
            DecimalDigit(49)
        ]);

        let nr0 = [DecimalDigit(98u8), DecimalDigit(52), DecimalDigit(33), DecimalDigit(94)];
        let nr1 = [DecimalDigit(8u8), DecimalDigit(9), DecimalDigit(10), DecimalDigit(11), DecimalDigit(98), DecimalDigit(52)];
        let mut result = [DecimalDigit::zero(); 10];
        let mut work = [DecimalDigit::zero(); 16];
        let n = mul_big_karatsuba_into(&nr0, &nr1, &mut result, &mut work);
        assert_eq!(n, 10);
        assert_eq!(result, [
            DecimalDigit(84),
            DecimalDigit(5),
            DecimalDigit(25),
            DecimalDigit(64),
            DecimalDigit(78),
            DecimalDigit(08),
            DecimalDigit(88),
            DecimalDigit(98),
            DecimalDigit(97),
            DecimalDigit(49)
        ]);
    }
}
