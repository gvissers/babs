// Copyright, 2021, Gé Vissers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::digit::Digit;
use crate::ubig::support::drop_leading_zeros;

fn block_size(nden: usize) -> usize
{
    let mshift = 8 * std::mem::size_of::<usize>() as u32 - ((nden-1) / super::BZ_CUTOFF).leading_zeros();
    let m = 1usize << mshift;
    let j = (nden + m - 1) / m;
    j * m
}

pub fn calc_div_bz_work_size(nden: usize) -> usize
{
    let n = block_size(nden);
    3 * n / 2 + 1 + crate::ubig::mul::calc_mul_work_size(n / 2)
}

pub fn div_big_bz<T>(num: &mut [T], den: &[T], quot: &mut[T], work: &mut [T]) -> (usize, usize)
where T: Digit
{
    let nnum = num.len();
    let nden = den.len();

    debug_assert!(nden > 2);
    debug_assert!(!crate::ubig::cmp::lt(num, den));
    debug_assert!(quot.len() >= nnum - nden + 1);
    debug_assert!(work.len() >= calc_div_bz_work_size(nden));

    let n = block_size(nden);

    let mut sden = vec![T::zero(); n];
    sden[n-nden..].copy_from_slice(den);
    let shift = sden[n-1].max_shift();
    crate::ubig::shl::shl_carry_assign_within_digit(&mut sden, shift as usize, T::zero());

    let t = 2 + (nnum-nden) / n;
    let mut snum = vec![T::zero(); t*n];
    snum[n-nden..n-nden+nnum].copy_from_slice(num);
    crate::ubig::shl::shl_carry_assign_within_digit(&mut snum[n-nden..n-nden+nnum+1], shift as usize, T::zero());

    let mut q = vec![T::zero(); (t-1)*n];
    for i in (0..t-1).rev()
    {
        div_big_bz_2n_n(&mut snum[i*n..(i+2)*n], &sden, &mut q[i*n..(i+1)*n], work);
    }

    let (nrem, _) = crate::ubig::shr::shr_carry_assign_within_digit(&mut snum[n-nden..n], shift as usize, T::zero());
    let nquot = drop_leading_zeros(&q, q.len());

    quot[..nquot].copy_from_slice(&q[..nquot]);
    num[..nrem].copy_from_slice(&snum[n-nden..n-nden+nrem]);

    (nquot, nrem)
}

fn div_big_bz_2n_n<T>(num: &mut [T], den: &[T], quot: &mut [T], work: &mut [T]) -> (usize, usize)
where T: Digit
{
    let n = den.len();

    debug_assert!(n < super::BZ_CUTOFF || n % 2 == 0);
    debug_assert!(num.len() == 2*n);
    debug_assert!(quot.len() == n);
    debug_assert!(den[n-1].max_shift() == 0);

    if n < super::BZ_CUTOFF
    {
        let nnum = drop_leading_zeros(num, num.len());
        super::div_big_with_work(&mut num[..nnum], den, quot, work).unwrap()
    }
    else
    {
        let hn = n/2;
        div_big_bz_3n_2n(&mut num[hn..], den, &mut quot[hn..], work);
        div_big_bz_3n_2n(&mut num[..3*hn], den, &mut quot[..hn], work);

        let nquot = drop_leading_zeros(quot, n);
        let nrem = drop_leading_zeros(num, n);
        (nquot, nrem)
    }
}

fn div_big_bz_3n_2n<T>(num: &mut [T], den: &[T], quot: &mut [T], work: &mut [T]) -> (usize, usize)
where T: Digit
{
    let n = den.len() / 2;

    debug_assert!(num.len() == 3 * n);
    debug_assert!(den.len() == 2 * n);
    debug_assert!(quot.len() == n);
    debug_assert!(den[2*n-1].max_shift() == 0);
    debug_assert!(work.len() >= 3*n + 1);

    let (b2, b1) = den.split_at(n);
    let a12 = &mut num[n..];
    let (mut nquot, _) = if crate::ubig::cmp::lt(&a12[n..], b1)
        {
            div_big_bz_2n_n(a12, b1, quot, work)
        }
        else
        {
            quot.fill(T::MAX);
            let _ = crate::ubig::sub::sub_assign_big(&mut a12[n..], b1);
            crate::ubig::add::add_assign_big(a12, b1);
            let n12 = drop_leading_zeros(a12, a12.len());
            (n, n12)
        };

    let nb2 = drop_leading_zeros(b2, b2.len());
    let (qden, mul_work) = work.split_at_mut(3*n + 1);
    let nqden = crate::ubig::mul::mul_big_into_with_work(&quot[..nquot], &b2[..nb2], qden, mul_work);
    debug_assert!(nqden <= 3*n);
    let qden = &qden[..nqden];
    let nnum = drop_leading_zeros(num, num.len());
    if crate::ubig::cmp::lt(&num[..nnum], qden)
    {
        crate::ubig::add::add_assign_big(num, den);
        nquot = crate::ubig::sub::dec_assign(&mut quot[..nquot]).unwrap();
        let nnum = drop_leading_zeros(num, num.len());
        if crate::ubig::cmp::lt(&num[..nnum], qden)
        {
            crate::ubig::add::add_assign_big(num, den);
            nquot = crate::ubig::sub::dec_assign(&mut quot[..nquot]).unwrap();
        }
    }
    let nrem = crate::ubig::sub::sub_assign_big(num, qden).unwrap();

    (nquot, nrem)
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn testbz()
    {
        let mut num = [BinaryDigit(0u8); 5];
        num[4] = BinaryDigit(0x14);
        let den = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(1)];
        let mut quot = [BinaryDigit(0u8); 3];
        let mut work = [BinaryDigit(0u8); 7];
        let (nquot, nrem) = div_big_bz(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 3);
        assert_eq!(nrem, 0);
        assert_eq!(quot[..nquot], [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0x14)]);
        assert_eq!(num[..nrem], []);

        let mut num = [DecimalDigit(0), DecimalDigit(0), DecimalDigit(90)];
        let den = [DecimalDigit(0), DecimalDigit(10), DecimalDigit(1)];
        let mut quot = [DecimalDigit(0u8); 1];
        let mut work = [DecimalDigit(0u8); 7];
        let (nquot, nrem) = div_big_bz(&mut num, &den, &mut quot, &mut work);
        assert_eq!(nquot, 1);
        assert_eq!(nrem, 2);
        assert_eq!(quot[..nquot], [DecimalDigit(81)]);
        assert_eq!(num[..nrem], [DecimalDigit(0), DecimalDigit(90)]);
    }
}
