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
            let work_size = calc_toom3_work_size(n0.max(n1));
            let mut work = vec![T::zero(); work_size];
            mul_big_toom3_into(nr0, nr1, product, &mut work)
        }
        else if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
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

        if n0 >= TOOM3_CUTOFF && n1 >= TOOM3_CUTOFF
        {
            mul_big_toom3_into(nr0, nr1, product, work)
        }
        else if n0 >= KARATSUBA_CUTOFF && n1 >= KARATSUBA_CUTOFF
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
    let nd0 = nr0.len();
    let nd1 = nr1.len();
    let nd = nd0 + nd1;

    result[..nd].fill(T::zero());
    for (offset, &d1) in nr1.iter().enumerate()
    {
        let carry = nr0.iter()
            .zip(&mut result[offset..offset+nd0])
            .fold(T::zero(), |carry, (&d0, rd)| rd.add_prod_carry_assign(d0, d1, carry));
        result[offset+nd0] = carry;
    }

    drop_leading_zeros(result, nd)
}

/// Calculate the maximum size of the scratch array necessary to perform Karatsuba multiplication
/// on two `n`-digit numbers.
const fn calc_karatsuba_work_size(n: usize) -> usize
{
    let mut work_size = 0;
    let mut nn = n;
    while nn >= KARATSUBA_CUTOFF
    {
        let split = (nn + 1) / 2;
        work_size += 2 * split;
        nn = split;
    }
    work_size
}

fn sub_big_into_abs_sign<T>(nr0: &[T], nr1: &[T], abs_diff: &mut[T]) -> (bool, usize)
where T: Digit
{
    debug_assert!(abs_diff.len() >= nr0.len().max(nr1.len()));
    if less(nr0, nr1)
    {
        (true, crate::ubig::sub::sub_big_into(nr1, nr0, abs_diff).unwrap())
    }
    else
    {
        (false, crate::ubig::sub::sub_big_into(nr0, nr1, abs_diff).unwrap())
    }
}

fn sub_assign_big_abs_sign<T>(nr0: &mut [T], len0: usize, nr1: &[T]) -> (bool, usize)
where T: Digit
{
    if less(&nr0[..len0], nr1)
    {
        crate::ubig::rsub::rsub_assign_big(&mut nr0[..nr1.len()], nr1);
        (true, drop_leading_zeros(nr0, nr1.len()))
    }
    else
    {
        crate::ubig::sub::sub_assign_big(&mut nr0[..len0], nr1);
        (false, drop_leading_zeros(nr0, len0))
    }
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
    assert!(n0 >= 2 && n1 >= 2, "Number of digits should be at least 2 for Karatsuba multiplication");
    assert!(work.len() >= calc_karatsuba_work_size(nmax), "Insufficient work space");

    let split = (nmax + 1) / 2;

    let (low0, high0) = nr0.split_at(split.min(n0));
    let nlow0 = drop_leading_zeros(low0, low0.len());
    let (low1, high1) = nr1.split_at(split.min(n1));
    let nlow1 = drop_leading_zeros(low1, low1.len());

    let (diff0, diff1) = result.split_at_mut(split);
    let (sign0, ndiff0) = sub_big_into_abs_sign(&low0[..nlow0], &high0, diff0);     // low0 - high0
    let (sign1, ndiff1) = sub_big_into_abs_sign(&low1[..nlow1], &high1, diff1);     // low1 - high1

    let (z1, new_work) = work.split_at_mut(2*split);
    z1.fill(T::zero());
    let mut nz1 = mul_big_into_with_work(&diff0[..ndiff0], &diff1[..ndiff1], z1, new_work); // |(low0-high0)*(low1-high1)|
    result[..n0+n1].fill(T::zero());
    let (z0, z2) = result.split_at_mut(2*split);
    let nz0 = mul_big_into_with_work(&low0[..nlow0], &low1[..nlow1], z0, new_work); // low0*low1
    let nz2 = mul_big_into_with_work(&high0, &high1, z2, new_work);                 // high0*high1

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
    else if less(&z1[..nz1], &z0[..nz0])
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
        debug_assert!(!less(&z2[..nz2], &z1[..nz1]), "z1 < 0");
        crate::ubig::rsub::rsub_assign_big(&mut z1[..nz2], &z2[..nz2]);
        nz1 = drop_leading_zeros(z1, nz2);
    }

    let carry = crate::ubig::add::add_assign_big(&mut result[split..], &z1[..nz1]);
    assert!(!carry);

    drop_leading_zeros(result, n0+n1)
}

#[inline]
fn less<T>(nr0: &[T], nr1: &[T]) -> bool
where T: Digit
{
    nr0.len() < nr1.len() || (nr0.len() == nr1.len() && nr0.iter().rev().lt(nr1.iter().rev()))
}

#[inline]
fn drop_leading_zeros<T>(nr: &[T], len: usize) -> usize
where T: Digit
{
    let mut n = len;
    while n > 0 && nr[n-1].is_zero()
    {
        n -= 1
    }
    n
}

/// Calculate the maximum size of the scratch array necessary to perform Toom-Cook multiplication
/// on two `n`-digit numbers.
const fn calc_toom3_work_size(n: usize) -> usize
{
    let mut work_size = 0;
    let mut nn = n;
    while nn >= TOOM3_CUTOFF
    {
        let b = (nn + 2) / 3;
        work_size += 6*b + 10;
        nn = b + 2;
    }
    work_size += calc_karatsuba_work_size(nn);
    work_size
}

fn mul_big_toom3_into<T>(nr0: &[T], nr1: &[T], result: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    // r = base^b, worst case base = 2
    //       0 ≤  p(0),  q(0) ≤ r-1                        → b digits
    //       1 ≤  p(1),  q(1) ≤ 3*(r-1) = (2+1)*(r-1)      → b+1 digits
    //  -(r-2) ≤ p(-1), q(-1) ≤ 2*(r-1)                    → b+1 digits
    // -2(r-3) ≤ p(-2), q(-2) ≤ 5*(r-1) = (4+1)*(r-1)      → b+2 digits
    //       1 ≤  p(∞),  q(∞) ≤ r-1                        → b digits
    //
    //                0 ≤  r(0) ≤ (r-1)^2 < r^2            → 2b digits
    //                1 ≤  r(1) ≤ 9*(r-1)^2 < (8+1)r^2     → 2b+3 digits
    //   -2*(r-2)*(r-1) ≤ r(-1) ≤ 4*(r-1)^2 < 4r^2         → 2b+2 digits
    //  -10*(r-3)*(r-1) ≤ r(-2) ≤ 25*(r-1)^2 < (16+8+1)r^2 → 2b+4 digits
    //                1 ≤  r(∞) ≤ (r-1)^2 < r^2            → 2b digits
    //
    // r_0 ← r(0): 0 ≤ r_0 ≤ (r-1)^2 < r^2                 → 2b digits
    // r_4 ← r(∞): 1 ≤ r_4 ≤ (r-1)^2 < r^2                 → 2b digits
    // r_3 ← (r(−2) − r(1))/3:                             → 2b+2 digits, +2 before /3 → 2b+4
    //   -4(r-1)^2 ≤ r_3 ≤ 7(r-1)^2 < (4+2+1)r^2
    // r_1 ← (r(1) - r(-1))/2:                             → 2b+2 digits, +1 before /2 → 2b+3
    //    0 ≤ r_1 ≤ 4(r-1)^2
    // r_2 ← r(-1) - r(0):                                 → 2b+1 digits
    //    -2(r-1)^2 ≤ r_2 ≤ 3(r-1)^2 < (2+1)r^2
    // r_3 ← (r_2 − r_3)/2 + 2r(∞)                         → 2b+1 digits, +1 before /2 → 2b+2
    //    0 ≤ r_3 ≤ 2(r-1)^2
    // r_2 ← r_2 + r_1 − r_4                               → 2b+1 digits, +1 before -r4 → 2b+2
    //    0 ≤ r_2 ≤ 3(r-1)^2 < (2+1)r^2
    // r_1 ← r_1 - r_3                                     → 2b digits
    //    0 ≤ r_1 ≤ 2(r-1)^2

    let nd0 = nr0.len();
    let nd1 = nr1.len();
    let nmax = nd0.max(nd1);
    assert!(nd0 >= 5 && nd1 >= 5, "Number of digits should be at least 5 for Toom-Cook multiplication");
    assert!(work.len() >= calc_toom3_work_size(nmax), "Insufficient work space");
    let b = (nmax + 2) / 3;

    let n = nd0 + nd1;

    let (pm2, qm2) = result.split_at_mut(b+2);
    let (work, new_work) = work.split_at_mut(6*b+10);
    let (r1, work) = work.split_at_mut(2*b+3);
    let (rm1, rm2) = work.split_at_mut(2*b+3);
    let (p1, q1) = rm1.split_at_mut(b+1);
    let (pm1, qm1) = rm2.split_at_mut(b+1);

    let min_b_nd0 = b.min(nd0);
    let len_p0 = drop_leading_zeros(nr0, min_b_nd0);
    // 0 ≤ p0 ≤ r-1
    let p0 = &nr0[..len_p0];
    let len_m1 = drop_leading_zeros(&nr0[min_b_nd0..], b.min(nd0 - min_b_nd0));
    // 0 ≤ n1 ≤ r-1
    let m1 = &nr0[min_b_nd0..min_b_nd0+len_m1];
    // 0 ≤ pinf ≤ r-1
    let pinf = &nr0[(2*b).min(nd0)..];
    // 0 ≤ pm1 ≤ 2(r-1)
    let len_pm1 = crate::ubig::add::add_big_into(p0, &pinf, pm1).unwrap();
    // 0 ≤ p1 ≤ 3(r-1)
    let len_p1 = crate::ubig::add::add_big_into(&pm1[..len_pm1], m1, p1).unwrap();
    let (sign_pm1, len_pm1) = sub_assign_big_abs_sign(pm1, len_pm1, m1);
    let (mut sign_pm2, mut len_pm2) = if sign_pm1
        {
            // -(r-1) ≤ pm2 < 0     if sign_pm2
            //      0 ≤ pm2 ≤ (r-1) if !sign_pm2
            sub_big_into_abs_sign(pinf, &pm1[..len_pm1], pm2)
        }
        else
        {
            // 0 ≤ pm2 ≤ 3(r-1)
            (false, crate::ubig::add::add_big_into(&pm1[..len_pm1], pinf, pm2).unwrap())
        };
    if !crate::ubig::shl::shl_carry_assign_within_digit(&mut pm2[..len_pm2], 1, T::zero()).is_zero()
    {
        // -2(r-1) ≤ pm2 < 0      if sign_pm2
        //       0 ≤ pm2 ≤ 6(r-1) if !sign_pm2
        pm2[len_pm2] = T::one();
        len_pm2 += 1;
    }
    if sign_pm2
    {
        len_pm2 = len_pm2.max(len_p0);
        if crate::ubig::add::add_assign_big(&mut pm2[..len_pm2], p0)
        {
            pm2[len_pm2] = T::one();
            len_pm2 += 1;
        }
    }
    else
    {
        let (sign, len) = sub_assign_big_abs_sign(pm2, len_pm2, p0);
        sign_pm2 = sign;
        len_pm2 = len;
    }

    let min_b_nd1 = b.min(nd1);
    let len_q0 = drop_leading_zeros(nr1, min_b_nd1);
    let q0 = &nr1[..len_q0];
    let len_n1 = drop_leading_zeros(&nr1[min_b_nd1..], b.min(nd1 - min_b_nd1));
    let n1 = &nr1[min_b_nd1..min_b_nd1+len_n1];
    let qinf = &nr1[(2*b).min(nd1)..];
    let len_qm1 = crate::ubig::add::add_big_into(q0, qinf, qm1).unwrap();
    let len_q1 = crate::ubig::add::add_big_into(&qm1[..len_qm1], n1, q1).unwrap();
    let (sign_qm1, len_qm1) = sub_assign_big_abs_sign(qm1, len_qm1, n1);
    let (mut sign_qm2, mut len_qm2) = if sign_qm1
        {
            sub_big_into_abs_sign(qinf, &qm1[..len_qm1], qm2)
        }
        else
        {
            (false, crate::ubig::add::add_big_into(&qm1[..len_qm1], qinf, qm2).unwrap())
        };
    if !crate::ubig::shl::shl_carry_assign_within_digit(&mut qm2[..len_qm2], 1, T::zero()).is_zero()
    {
        qm2[len_qm2] = T::one();
        len_qm2 += 1;
    }
    if sign_qm2
    {
        len_qm2 = len_qm2.max(len_q0);
        if crate::ubig::add::add_assign_big(&mut qm2[..len_qm2], q0)
        {
            qm2[len_qm2] = T::one();
            len_qm2 += 1;
        }
    }
    else
    {
        let (sign, len) = sub_assign_big_abs_sign(qm2, len_qm2, q0);
        sign_qm2 = sign;
        len_qm2 = len;
    }

    let mut len_r1 = mul_big_into_with_work(&p1[..len_p1], &q1[..len_q1], r1, new_work);
    let len_rm1 = mul_big_into_with_work(&pm1[..len_pm1], &qm1[..len_qm1], rm1, new_work);
rm1[len_rm1..].fill(T::zero());
    let sign_rm1 = sign_pm1 ^ sign_qm1;
    let len_rm2 = mul_big_into_with_work(&pm2[..len_pm2], &qm2[..len_qm2], rm2, new_work);
rm2[len_rm2..].fill(T::zero());
    let sign_rm2 = sign_pm2 ^ sign_qm2;
    result[..n].fill(T::zero());
    let (r0, r4) = result.split_at_mut((4*b).min(result.len()));
    let len_r0 = mul_big_into_with_work(p0, q0, r0, new_work);
    let len_r4 = mul_big_into_with_work(&pinf, &qinf, r4, new_work);
    let r4 = &r4[..len_r4];

    let r3 = rm2;
    let mut len_r3 = len_rm2;
    let mut sign_r3;
    let mut carry;
    if sign_rm2
    {
        len_r3 = len_r3.max(len_r1);
        carry = crate::ubig::add::add_assign_big(&mut r3[..len_r3], &r1[..len_r1]);
        sign_r3 = true;
    }
    else
    {
        let (sign, len) = sub_assign_big_abs_sign(r3, len_r3, &r1[..len_r1]);
        len_r3 = len;
        sign_r3 = sign;
        carry = false;
    }
    crate::ubig::div::div3_carry_assign(&mut r3[..len_r3], T::from_bit(carry));
    len_r3 = drop_leading_zeros(r3, len_r3);
    if sign_rm1
    {
        len_r1 = len_r1.max(len_rm1);
        carry = crate::ubig::add::add_assign_big(&mut r1[..len_r1], &rm1[..len_rm1]);
    }
    else
    {
        crate::ubig::sub::sub_assign_big(&mut r1[..len_r1], &rm1[..len_rm1]);
        len_r1 = drop_leading_zeros(r1, len_r1);
        carry = false;
    };
    crate::ubig::shr::shr_carry_assign_within_digit(&mut r1[..len_r1], 1, T::from_bit(carry));
    len_r1 = drop_leading_zeros(r1, len_r1);
    let r2 = rm1;
    let mut len_r2 = len_rm1;
    let sign_r2;
    if sign_rm1
    {
        len_r2 = len_r2.max(len_r0);
        if crate::ubig::add::add_assign_big(&mut r2[..len_r2], &r0[..len_r0])
        {
            r2[len_r2] = T::one();
            len_r2 += 1;
        }
        sign_r2 = true;
    }
    else
    {
        let (sign, len) = sub_assign_big_abs_sign(r2, len_r2, &r0[..len_r0]);
        sign_r2 = sign;
        len_r2 = len;
    }
    if sign_r2 != sign_r3
    {
        len_r3 = len_r3.max(len_r2);
        carry = crate::ubig::add::add_assign_big(&mut r3[..len_r3], &r2[..len_r2]);
        sign_r3 = sign_r2;
    }
    else
    {
        let (sign, len) = sub_assign_big_abs_sign(r3, len_r3, &r2[..len_r2]);
        len_r3 = len;
        sign_r3 = !(sign_r3 ^ sign) && len != 0;
        carry = false;
    }
    crate::ubig::shr::shr_carry_assign_within_digit(&mut r3[..len_r3], 1, T::from_bit(carry));
    len_r3 = drop_leading_zeros(r3, len_r3);
    if !sign_r3
    {
        len_r3 = len_r3.max(len_r4);
        if crate::ubig::add::add_assign_big(&mut r3[..len_r3], r4)
        {
            r3[len_r3] = T::one();
            len_r3 += 1;
        }
        if crate::ubig::add::add_assign_big(&mut r3[..len_r3], r4)
        {
            r3[len_r3] = T::one();
            len_r3 += 1;
        }
    }
    else if less(&r3[..len_r3], r4)
    {
        len_r3 = len_r4;
        crate::ubig::rsub::rsub_assign_big(&mut r3[..len_r4], r4);
        if crate::ubig::add::add_assign_big(&mut r3[..len_r3], r4)
        {
            r3[len_r3] = T::one();
            len_r3 += 1;
        }
    }
    else
    {
        crate::ubig::sub::sub_assign_big(&mut r3[..len_r4], r4);
        crate::ubig::rsub::rsub_assign_big(&mut r3[..len_r4], r4);
        len_r3 = drop_leading_zeros(r3, len_r4);
    }
    // sign_r3 = false;
    if sign_r2
    {
        crate::ubig::rsub::rsub_assign_big(&mut r2[..len_r1], &r1[..len_r1]);
        len_r2 = drop_leading_zeros(r2, len_r1);
    }
    else
    {
        len_r2 = len_r2.max(len_r1);
        if crate::ubig::add::add_assign_big(&mut r2[..len_r2], &r1[..len_r1])
        {
            r2[len_r2] = T::one();
            len_r2 += 1;
        }
    }
    // sign_r2 = false;
    crate::ubig::sub::sub_assign_big(&mut r2[..len_r2], r4);
    len_r2 = drop_leading_zeros(r2, len_r2);
    crate::ubig::sub::sub_assign_big(&mut r1[..len_r1], &r3[..len_r3]);
    len_r1 = drop_leading_zeros(r1, len_r1);

    crate::ubig::add::add_assign_big(&mut result[b..], &r1[..len_r1]);
    crate::ubig::add::add_assign_big(&mut result[2*b..], &r2[..len_r2]);
    crate::ubig::add::add_assign_big(&mut result[3*b..], &r3[..len_r3]);

    drop_leading_zeros(result, n)
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

    #[test]
    fn test_big_into_toom3()
    {
        let n = [DecimalDigit(9012u16), DecimalDigit(5678), DecimalDigit(1234), DecimalDigit(7890), DecimalDigit(3456), DecimalDigit(12)];
        let m = [DecimalDigit(1098), DecimalDigit(5432), DecimalDigit(9876), DecimalDigit(4321), DecimalDigit(8765), DecimalDigit(9)];
        let mut prod = vec![DecimalDigit(0); 12];
        let mut work = vec![DecimalDigit(0); 28];
        let nr_digits = mul_big_toom3_into(&n, &m, &mut prod, &mut work);
        assert_eq!(nr_digits, 11);
        assert_eq!(&prod, &[DecimalDigit(5176), DecimalDigit(8617), DecimalDigit(5858), DecimalDigit(5208), DecimalDigit(6009), DecimalDigit(4937), DecimalDigit(1632), DecimalDigit(6761), DecimalDigit(3124), DecimalDigit(9326), DecimalDigit(121), DecimalDigit(0)]);

        let n = [BinaryDigit(0x16u8), BinaryDigit(0x63), BinaryDigit(0x1f), BinaryDigit(0xe3), BinaryDigit(0x73), BinaryDigit(0x98), BinaryDigit(0xa6), BinaryDigit(0x16), BinaryDigit(0x33), BinaryDigit(0x72), BinaryDigit(0xbb)];
        let m = [BinaryDigit(0x72), BinaryDigit(0x83), BinaryDigit(0x8f), BinaryDigit(0xf7), BinaryDigit(0x72), BinaryDigit(0xa7), BinaryDigit(0xa1), BinaryDigit(0x99), BinaryDigit(0x4a), BinaryDigit(0xcf), BinaryDigit(0x32), BinaryDigit(0x5d)];
        let mut prod = vec![BinaryDigit(0); 23];
        let mut work = vec![BinaryDigit(0); 60];
        let nr_digits = mul_big_toom3_into(&n, &m, &mut prod, &mut work);
        assert_eq!(nr_digits, 23);
        assert_eq!(&prod, &[BinaryDigit(0xcc), BinaryDigit(0x61), BinaryDigit(0xf8), BinaryDigit(0xc6), BinaryDigit(0xc2), BinaryDigit(0xd1), BinaryDigit(0x85), BinaryDigit(0x63), BinaryDigit(0x94), BinaryDigit(0xe7), BinaryDigit(0x0d), BinaryDigit(0x9c), BinaryDigit(0xf4), BinaryDigit(0xcb), BinaryDigit(0xea), BinaryDigit(0x17), BinaryDigit(0x9f), BinaryDigit(0xc1), BinaryDigit(0x2b), BinaryDigit(0xa5), BinaryDigit(0xb0), BinaryDigit(0x3d), BinaryDigit(0x44)]);

        let n = [BinaryDigit(0xffu8); 5];
        let m = [BinaryDigit(0xffu8); 5];
        let mut prod = vec![BinaryDigit(0); 10];
        let mut work = vec![BinaryDigit(0); 28];
        let nr_digits = mul_big_toom3_into(&n, &m, &mut prod, &mut work);
        assert_eq!(nr_digits, 10);
        assert_eq!(prod, [BinaryDigit(0x01), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0xfe), BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)]);

        let n = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1)];
        let m = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1)];
        let mut prod = vec![DecimalDigit(0); 14];
        let mut work = vec![DecimalDigit(0); 50];
        let nr_digits = mul_big_toom3_into(&n, &m, &mut prod, &mut work);
        assert_eq!(nr_digits, 13);
        assert_eq!(prod, [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1), DecimalDigit(0)]);
    }
}
