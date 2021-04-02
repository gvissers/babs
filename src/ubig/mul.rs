use crate::digit::Digit;

/// The minimum size of a number (in digits) for Karatsuba multiplication. Should be at leats 4.
const KARATSUBA_CUTOFF: usize = 16;

/// Multiply the number or number part represented by the digits in `nr` by the single digit `fac`,
/// and add the single digit `off` to the result. Return the carry on overflow, or `None` if the
/// number does not overflow.
pub fn mul_add_assign_digit<T>(nr: &mut [T], fac: T, off: T) -> Option<T>
where T: Digit
{
    let mut carry = off;
    for d in nr.iter_mut()
    {
        carry = d.mul_add_assign(fac, carry);
    }

    (!carry.is_zero()).then(|| carry)
}

/// Multiply the number or number part represented by the digits in `nr` by the two-digit number
/// `fac_low+ b*fac_high`, where `b` is the base of the number, and add `offset` to it. Return
/// the carry digits.
pub fn mul_pair_add_assign_digit<T>(nr: &mut [T], fac_low: T, fac_high: T, offset: T) -> (T, T)
where T: Digit
{
    if !nr.is_empty()
    {
        let mut prev = nr[0];
        let mut carry0 = nr[0].mul_add_assign(fac_low, offset);
        let mut add_one = false;
        for d in nr[1..].iter_mut()
        {
            let new_prev = *d;

            carry0 = prev.mul_add_assign(fac_high, carry0);
            if add_one
            {
                add_one = carry0.inc();
            }
            let carry1 = d.mul_add_assign(fac_low, prev);
            add_one |= carry0.add_assign(carry1);

            prev = new_prev;
        }
        carry0 = prev.mul_add_assign(fac_high, carry0);
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

        if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
        {
            let work_size = calc_karatsuba_work_size(n0.max(n1));
            let mut work = vec![T::zero(); work_size];
            mul_big_karatsuba_into(nr0, nr1, product, &mut work)
        }
        else
        {
            mul_big_long_into(nr0, nr1, product)
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

        if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
        {
            mul_big_karatsuba_into(nr0, nr1, product, work)
        }
        else
        {
            mul_big_long_into(nr0, nr1, product)
        }
    }
}

/// Multiply the number represented by `nr0` by `nr1` using long multiplication, and store the
/// result in `result`. The result array must have space for at least `n0+n1` digits,  where `n0`
/// denotes the number of digits in `nr0`, and `n1` the number of digits in `nr1`. Returns the
/// number of digits in the product.
fn mul_big_long_into<T>(nr0: &[T], nr1: &[T], result: &mut [T]) -> usize
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    let mut n = n0 + n1;

    result[..n].fill(T::zero());
    for (offset, &d1) in nr1.iter().enumerate()
    {
        let mut carry = T::zero();
        for (&d0, rd) in nr0.iter().zip(&mut result[offset..])
        {
            carry = rd.add_prod_carry_assign(d0, d1, carry);
        }
        result[offset+n0] = carry;
    }

    while n > 0  && result[n-1].is_zero()
    {
        n -= 1;
    }
    n
}

/// Calculate the maximum size of the scratch array necessary to perform Karatsuba multiplication
/// on two `n`-digit numbers.
const fn calc_karatsuba_work_size(n: usize) -> usize
{
    let mut work_size = 0;
    let mut nn = n;
    while nn >= KARATSUBA_CUTOFF
    {
        let split1 = (nn + 1) / 2 + 1;
        work_size += 2 * split1;
        nn = split1;
    }
    work_size
}

/// Multiply the number represented by `nr0` by `nr1` using Karatsuba multiplication, and store
/// the result in `result`. The scratch array `work` should be of appropriate size
/// (see [calc_karatsuba_work_size()](Self::calc_karatsuba_work_size)). The result array must
/// have space for at least `n0+n1` digits, where `n0` denotes the number of digits in ths
/// borrow, and `n1` the number of digits in `other`. Returns the number of digits in the product.
fn mul_big_karatsuba_into<T>(nr0: &[T], nr1: &[T], result: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    let nmax = n0.max(n1);
    assert!(n0 >= 4 && n1 >= 4, "Number of digits should be at least 4 for Karatsuba multiplication");
    assert!(work.len() >= calc_karatsuba_work_size(nmax), "Insufficient work space");

    let split = (nmax + 1) / 2;

    let (low0, high0) = nr0.split_at(split.min(n0));
    let (low1, high1) = nr1.split_at(split.min(n1));

    let (sum0, sum1) = result.split_at_mut(split+1);
    let nsum0 = crate::ubig::add::add_big_into(&low0, &high0, sum0);                    // low0 + high0
    let nsum1 = crate::ubig::add::add_big_into(&low1, &high1, sum1);                    // low1 + high1

    let (z1, new_work) = work.split_at_mut(2*split+2);
    let mut nz1 = mul_big_into_with_work(&sum0[..nsum0], &sum1[..nsum1], z1, new_work); // (low0+high0)*(low1+high1)
    result[..n0+n1].fill(T::zero());
    let (z0, z2) = result.split_at_mut(2*split);
    let nz0 = mul_big_into_with_work(&low0, &low1, z0, new_work);                       // low0*low1
    let nz2 = mul_big_into_with_work(&high0, &high1, z2, new_work);                     // high0*high1

    crate::ubig::sub::sub_assign_big(&mut z1[..nz1], &z2[..nz2]);
    crate::ubig::sub::sub_assign_big(&mut z1[..nz1], &z0[..nz0]);                       // low0*high1 + high0*low1
    while nz1 > 0 && z1[nz1-1].is_zero()
    {
        nz1 -= 1;
    }

    let carry = crate::ubig::add::add_assign_big(&mut result[split..], &z1[..nz1]);
    assert!(carry.is_none());
    let mut n = n0 + n1;
    while n > 0 && result[n-1].is_zero()
    {
        n -= 1;
    }
    n
}


#[cfg(test)]
mod tests
{
    use crate::digit::{BinaryDigit, DecimalDigit};
    use super::*;
    use num_traits::Zero;

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

    #[test]
    fn test_mul_big_long_into_binary()
    {
        let nr0: [BinaryDigit<u8>; 0] = [];
        let nr1 = [BinaryDigit(0x7f), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 3];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 0);
        assert_eq!(result, [BinaryDigit(0); 3]);

        let nr0 = [BinaryDigit(0x80u8)];
        let nr1 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 4];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 4);
        assert_eq!(result, [BinaryDigit(0x80), BinaryDigit(0x3f), BinaryDigit(0x9b), BinaryDigit(0x11)]);

        let nr0 = [BinaryDigit(0x80u8), BinaryDigit(0x65), BinaryDigit(0x21), BinaryDigit(0xfe), BinaryDigit(0x9c)];
        let nr1 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            BinaryDigit(0x80),
            BinaryDigit(0x5a),
            BinaryDigit(0x7a),
            BinaryDigit(0xfe),
            BinaryDigit(0x0d),
            BinaryDigit(0x2a),
            BinaryDigit(0x98),
            BinaryDigit(0x15)
        ]);

        let nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let nr1 = [BinaryDigit(0x80u8), BinaryDigit(0x65), BinaryDigit(0x21), BinaryDigit(0xfe), BinaryDigit(0x9c)];
        let mut result = [BinaryDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            BinaryDigit(0x80),
            BinaryDigit(0x5a),
            BinaryDigit(0x7a),
            BinaryDigit(0xfe),
            BinaryDigit(0x0d),
            BinaryDigit(0x2a),
            BinaryDigit(0x98),
            BinaryDigit(0x15)
        ]);

        let nr0 = [BinaryDigit(0x7f32u16), BinaryDigit(0x367d), BinaryDigit(0x23a0)];
        let nr1 = [BinaryDigit(0x8008u16), BinaryDigit(0x6543), BinaryDigit(0x21ff), BinaryDigit(0xfe)];
        let mut result = [BinaryDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 7);
        assert_eq!(result, [
            BinaryDigit(0xf990),
            BinaryDigit(0x779a),
            BinaryDigit(0x2315),
            BinaryDigit(0x4242),
            BinaryDigit(0x4238),
            BinaryDigit(0x5db1),
            BinaryDigit(0x23),
        ]);

        let nr0 = [BinaryDigit(0x7f32u32), BinaryDigit(0x367d), BinaryDigit(0x23a0)];
        let nr1 = [BinaryDigit(0x8008u32), BinaryDigit(0x6543), BinaryDigit(0x21ff), BinaryDigit(0xfe)];
        let mut result = [BinaryDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 6);
        assert_eq!(result, [
            BinaryDigit(0x3f9cf990),
            BinaryDigit(0x4d9037fe),
            BinaryDigit(0x3842d585),
            BinaryDigit(0x15d209ff),
            BinaryDigit(0x04f12c66),
            BinaryDigit(0x2358c0),
            BinaryDigit(0)
        ]);
    }

    #[test]
    fn test_mul_big_long_into_decimal()
    {
        let nr0: [DecimalDigit<u8>; 0] = [];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 3];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 0);
        assert_eq!(result, [DecimalDigit(0); 3]);

        let nr0 = [DecimalDigit(50u8)];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 4];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 4);
        assert_eq!(result, [DecimalDigit(50), DecimalDigit(24), DecimalDigit(68), DecimalDigit(11)]);

        let nr0 = [DecimalDigit(50u8), DecimalDigit(65), DecimalDigit(21), DecimalDigit(98), DecimalDigit(95)];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            DecimalDigit(50),
            DecimalDigit(9),
            DecimalDigit(69),
            DecimalDigit(98),
            DecimalDigit(36),
            DecimalDigit(61),
            DecimalDigit(42),
            DecimalDigit(22)
        ]);

        let nr0 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let nr1 = [DecimalDigit(50u8), DecimalDigit(65), DecimalDigit(21), DecimalDigit(98), DecimalDigit(95)];
        let mut result = [DecimalDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            DecimalDigit(50),
            DecimalDigit(9),
            DecimalDigit(69),
            DecimalDigit(98),
            DecimalDigit(36),
            DecimalDigit(61),
            DecimalDigit(42),
            DecimalDigit(22)
        ]);

        let nr0 = [DecimalDigit(7_932u16), DecimalDigit(3_677), DecimalDigit(2_380)];
        let nr1 = [DecimalDigit(8_008u16), DecimalDigit(6_543), DecimalDigit(2_155), DecimalDigit(98)];
        let mut result = [DecimalDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 7);
        assert_eq!(result, [
            DecimalDigit(9456),
            DecimalDigit(843),
            DecimalDigit(9246),
            DecimalDigit(9632),
            DecimalDigit(1673),
            DecimalDigit(3789),
            DecimalDigit(23),
        ]);

        let nr0 = [DecimalDigit(7_932u32), DecimalDigit(3_677), DecimalDigit(2_380)];
        let nr1 = [DecimalDigit(8_008u32), DecimalDigit(6_543), DecimalDigit(2_155), DecimalDigit(98)];
        let mut result = [DecimalDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 6);
        assert_eq!(result, [
            DecimalDigit(63_519_456),
            DecimalDigit(81_344_492),
            DecimalDigit(60_211_111),
            DecimalDigit(24_273_611),
            DecimalDigit(5_489_246),
            DecimalDigit(233_240),
            DecimalDigit(0)
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
