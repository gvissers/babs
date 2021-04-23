use crate::digit::Digit;
use crate::ubig::support::drop_leading_zeros;

/// Calculate the maximum size of the scratch array necessary to perform Toom-Cook multiplication
/// on two `n`-digit numbers.
pub const fn calc_toom3_work_size(n: usize) -> usize
{
    let mut work_size = 0;
    let mut nn = n;
    while nn >= super::TOOM3_CUTOFF
    {
        let b = (nn + 2) / 3;
        work_size += 6*b + 10;
        nn = b + 2;
    }
    work_size += super::karatsuba::calc_karatsuba_work_size(nn);
    work_size
}

pub fn mul_big_toom3_into<T>(nr0: &[T], nr1: &[T], result: &mut [T], work: &mut [T]) -> usize
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
    let (sign_pm1, len_pm1) = crate::ubig::sub::sub_assign_big_abs_sign(pm1, len_pm1, m1);
    let (mut sign_pm2, mut len_pm2) = if sign_pm1
        {
            // -(r-1) ≤ pm2 < 0     if sign_pm2
            //      0 ≤ pm2 ≤ (r-1) if !sign_pm2
            crate::ubig::sub::sub_big_into_abs_sign(pinf, &pm1[..len_pm1], pm2)
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
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(pm2, len_pm2, p0);
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
    let (sign_qm1, len_qm1) = crate::ubig::sub::sub_assign_big_abs_sign(qm1, len_qm1, n1);
    let (mut sign_qm2, mut len_qm2) = if sign_qm1
        {
            crate::ubig::sub::sub_big_into_abs_sign(qinf, &qm1[..len_qm1], qm2)
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
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(qm2, len_qm2, q0);
        sign_qm2 = sign;
        len_qm2 = len;
    }

    let mut len_r1 = super::mul_big_into_with_work(&p1[..len_p1], &q1[..len_q1], r1, new_work);
    let len_rm1 = super::mul_big_into_with_work(&pm1[..len_pm1], &qm1[..len_qm1], rm1, new_work);
rm1[len_rm1..].fill(T::zero());
    let sign_rm1 = sign_pm1 ^ sign_qm1;
    let len_rm2 = super::mul_big_into_with_work(&pm2[..len_pm2], &qm2[..len_qm2], rm2, new_work);
rm2[len_rm2..].fill(T::zero());
    let sign_rm2 = sign_pm2 ^ sign_qm2;
    result[..n].fill(T::zero());
    let (r0, r4) = result.split_at_mut((4*b).min(result.len()));
    let len_r0 = super::mul_big_into_with_work(p0, q0, r0, new_work);
    let len_r4 = super::mul_big_into_with_work(&pinf, &qinf, r4, new_work);
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
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(r3, len_r3, &r1[..len_r1]);
        len_r3 = len;
        sign_r3 = sign;
        carry = false;
    }
    crate::ubig::div::div3_carry_assign(&mut r3[..len_r3], carry as u8);
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
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(r2, len_r2, &r0[..len_r0]);
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
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(r3, len_r3, &r2[..len_r2]);
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
    else if crate::ubig::cmp::lt(&r3[..len_r3], r4)
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

pub fn square_toom3_into<T>(nr0: &[T], result: &mut [T], work: &mut [T]) -> usize
where T: Digit
{
    let nd0 = nr0.len();
    assert!(nd0 >= 5, "Number of digits should be at least 5 for Toom-Cook multiplication");
    assert!(work.len() >= calc_toom3_work_size(nd0), "Insufficient work space");
    let b = (nd0 + 2) / 3;

    let n = 2*nd0;

    let (p1, res) = result.split_at_mut(b+1);
    let (pm1, pm2) = res.split_at_mut(b+1);
    let (work, new_work) = work.split_at_mut(6*b+10);
    let (r1, work) = work.split_at_mut(2*b+3);
    let (rm1, rm2) = work.split_at_mut(2*b+3);

    let min_b_nd0 = b.min(nd0);
    let len_p0 = drop_leading_zeros(nr0, min_b_nd0);
    let p0 = &nr0[..len_p0];
    let len_m1 = drop_leading_zeros(&nr0[min_b_nd0..], b.min(nd0 - min_b_nd0));
    let m1 = &nr0[min_b_nd0..min_b_nd0+len_m1];
    let pinf = &nr0[(2*b).min(nd0)..];
    let len_pm1 = crate::ubig::add::add_big_into(p0, &pinf, pm1).unwrap();
    let len_p1 = crate::ubig::add::add_big_into(&pm1[..len_pm1], m1, p1).unwrap();
    let (sign_pm1, len_pm1) = crate::ubig::sub::sub_assign_big_abs_sign(pm1, len_pm1, m1);
    let (sign_pm2, mut len_pm2) = if sign_pm1
        {
            crate::ubig::sub::sub_big_into_abs_sign(pinf, &pm1[..len_pm1], pm2)
        }
        else
        {
            (false, crate::ubig::add::add_big_into(&pm1[..len_pm1], pinf, pm2).unwrap())
        };
    if !crate::ubig::shl::shl_carry_assign_within_digit(&mut pm2[..len_pm2], 1, T::zero()).is_zero()
    {
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
        let (_, len) = crate::ubig::sub::sub_assign_big_abs_sign(pm2, len_pm2, p0);
        len_pm2 = len;
    }

    let mut len_r1 = super::square_into_with_work(&p1[..len_p1], r1, new_work);
    let len_rm1 = super::square_into_with_work(&pm1[..len_pm1], rm1, new_work);
rm1[len_rm1..].fill(T::zero());
    let len_rm2 = super::square_into_with_work(&pm2[..len_pm2], rm2, new_work);
rm2[len_rm2..].fill(T::zero());
    result[..n].fill(T::zero());
    let (r0, r4) = result.split_at_mut((4*b).min(result.len()));
    let len_r0 = super::square_into_with_work(p0, r0, new_work);
    let len_r4 = super::square_into_with_work(&pinf, r4, new_work);
    let r4 = &r4[..len_r4];

    let r3 = rm2;
    let (mut sign_r3, mut len_r3) = crate::ubig::sub::sub_assign_big_abs_sign(r3, len_rm2, &r1[..len_r1]);
    crate::ubig::div::div3_carry_assign(&mut r3[..len_r3], 0);
    len_r3 = drop_leading_zeros(r3, len_r3);
    crate::ubig::sub::sub_assign_big(&mut r1[..len_r1], &rm1[..len_rm1]);
    len_r1 = drop_leading_zeros(r1, len_r1);
    crate::ubig::shr::shr_carry_assign_within_digit(&mut r1[..len_r1], 1, T::zero());
    len_r1 = drop_leading_zeros(r1, len_r1);
    let r2 = rm1;
    let (sign_r2, mut len_r2) = crate::ubig::sub::sub_assign_big_abs_sign(r2, len_rm1, &r0[..len_r0]);
    let carry;
    if sign_r2 != sign_r3
    {
        len_r3 = len_r3.max(len_r2);
        carry = crate::ubig::add::add_assign_big(&mut r3[..len_r3], &r2[..len_r2]);
        sign_r3 = sign_r2;
    }
    else
    {
        let (sign, len) = crate::ubig::sub::sub_assign_big_abs_sign(r3, len_r3, &r2[..len_r2]);
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
    else if crate::ubig::cmp::lt(&r3[..len_r3], r4)
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
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::Zero;

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

    #[test]
    fn test_square_toom3_into_binary()
    {
        let nr0 = [BinaryDigit(0x2f_u8), BinaryDigit(0xf4), BinaryDigit(0x89), BinaryDigit(0x12), BinaryDigit(0x03)];
        let mut square = [BinaryDigit::zero(); 10];
        let mut work = [BinaryDigit::zero(); 30];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 9);
        assert_eq!(square, [
            BinaryDigit(0xa1),
            BinaryDigit(0xa0),
            BinaryDigit(0x37),
            BinaryDigit(0xdf),
            BinaryDigit(0xc7),
            BinaryDigit(0x69),
            BinaryDigit(0x93),
            BinaryDigit(0x70),
            BinaryDigit(0x09),
            BinaryDigit(0)
        ]);

        let nr0 = [BinaryDigit(0x453a_u16), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0x56af)];
        let mut square = [BinaryDigit::zero(); 10];
        let mut work = [BinaryDigit::zero(); 30];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 10);
        assert_eq!(square, [
            BinaryDigit(0x5124),
            BinaryDigit(0x12b8),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0x9d4c),
            BinaryDigit(0x2ee1),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0x0ba1),
            BinaryDigit(0x1d5a)
        ]);

        let nr0 = [
            BinaryDigit(0x7292df34_u32),
            BinaryDigit(0x839d52fa),
            BinaryDigit(0x2673feda),
            BinaryDigit(0x72fd53ce),
            BinaryDigit(0x358812df),
            BinaryDigit(0xffffffff),
            BinaryDigit(0x262fd623),
            BinaryDigit(0x32658182),
            BinaryDigit(0xfd7732dc)
        ];
        let mut square = [BinaryDigit::zero(); 18];
        let mut work = [BinaryDigit::zero(); 58];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 18);
        assert_eq!(square, [
            BinaryDigit(0xa9eba290),
            BinaryDigit(0x0ee8649d),
            BinaryDigit(0xc11f938f),
            BinaryDigit(0xa12e2b69),
            BinaryDigit(0xadb0aeb6),
            BinaryDigit(0xdcfd5699),
            BinaryDigit(0x10156a93),
            BinaryDigit(0xf0ed4ff1),
            BinaryDigit(0xfe3509a4),
            BinaryDigit(0xb733e4f8),
            BinaryDigit(0xcfa78d74),
            BinaryDigit(0x6bda5f36),
            BinaryDigit(0x12e62515),
            BinaryDigit(0x7b926a6f),
            BinaryDigit(0xd8775bea),
            BinaryDigit(0xf5734b2e),
            BinaryDigit(0x8e6e3d6f),
            BinaryDigit(0xfaf4d207)
        ]);

        let nr0 = [BinaryDigit(0xffffffffffffffff_u64); 17];
        let mut square = [BinaryDigit::zero(); 34];
        let mut work = [BinaryDigit::zero(); 100];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 34);
        assert_eq!(square, [
            BinaryDigit(1),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0xfffffffffffffffe),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff)
        ]);
    }

    #[test]
    fn test_square_toom3_into_decimal()
    {
        let nr0 = [DecimalDigit(27_u8), DecimalDigit(86), DecimalDigit(0), DecimalDigit(93), DecimalDigit(2)];
        let mut square = [DecimalDigit::zero(); 10];
        let mut work = [DecimalDigit::zero(); 30];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 9);
        assert_eq!(square, [
            DecimalDigit(29),
            DecimalDigit(51),
            DecimalDigit(42),
            DecimalDigit(96),
            DecimalDigit(54),
            DecimalDigit(5),
            DecimalDigit(54),
            DecimalDigit(58),
            DecimalDigit(8),
            DecimalDigit(0)
        ]);

        let nr0 = [DecimalDigit(5_673_u16), DecimalDigit(9_872), DecimalDigit(1_234), DecimalDigit(9_999), DecimalDigit(123)];
        let mut square = [DecimalDigit::zero(); 10];
        let mut work = [DecimalDigit::zero(); 30];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 10);
        assert_eq!(square, [
            DecimalDigit(2_929),
            DecimalDigit(  930),
            DecimalDigit(8_549),
            DecimalDigit(3_896),
            DecimalDigit(2_352),
            DecimalDigit(6_079),
            DecimalDigit(6_277),
            DecimalDigit(9_782),
            DecimalDigit(5_375),
            DecimalDigit(    1)
        ]);

        let nr0 = [
            DecimalDigit(872_201_010_u32),
            DecimalDigit(  9_872_664),
            DecimalDigit( 23_987_345),
            DecimalDigit(234_198_372),
            DecimalDigit(929_821_119),
            DecimalDigit(909_928_872),
            DecimalDigit(373_444_756)
        ];
        let mut square = [DecimalDigit::zero(); 14];
        let mut work = [DecimalDigit::zero(); 58];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 14);
        assert_eq!(square, [
            DecimalDigit(845_020_100),
            DecimalDigit(785_115_881),
            DecimalDigit(584_115_691),
            DecimalDigit(234_326_642),
            DecimalDigit( 23_625_172),
            DecimalDigit(271_489_707),
            DecimalDigit(762_922_611),
            DecimalDigit(164_247_573),
            DecimalDigit(142_583_099),
            DecimalDigit( 29_860_931),
            DecimalDigit(783_458_785),
            DecimalDigit(685_234_659),
            DecimalDigit(463_515_868),
            DecimalDigit(139_460_986)
        ]);

        let nr0 = [DecimalDigit(9_876_543_210_123_456_789_u64); 7];
        let mut square = [DecimalDigit::zero(); 14];
        let mut work = [DecimalDigit::zero(); 100];
        let n = square_toom3_into(&nr0, &mut square, &mut work);
        assert_eq!(n, 14);
        assert_eq!(square, [
            DecimalDigit(2_267_946_958_750_190_521),
            DecimalDigit(4_290_504_495_643_956_714),
            DecimalDigit(6_313_062_032_537_722_908),
            DecimalDigit(8_335_619_569_431_489_102),
            DecimalDigit(  358_177_106_325_255_296),
            DecimalDigit(2_380_734_643_219_021_491),
            DecimalDigit(4_403_292_180_112_787_685),
            DecimalDigit(1_889_955_799_506_172_837),
            DecimalDigit(9_867_398_262_612_406_645),
            DecimalDigit(7_844_840_725_718_640_450),
            DecimalDigit(5_822_283_188_824_874_256),
            DecimalDigit(3_799_725_651_931_108_062),
            DecimalDigit(1_777_168_115_037_341_868),
            DecimalDigit(9_754_610_578_143_575_674)
        ]);
    }
}
