use crate::digit::Digit;
use crate::result::{Error, Result};
use crate::ubig::support::drop_leading_zeros;

/// Decrement the numer or number part represented by the digits in `nr` by one, and returns
/// the number of digits in the result. If the original number is zero, an `Underflow` error is
/// returned.
pub fn dec_assign<T>(nr: &mut [T]) -> Result<usize>
where T: Digit
{
    if nr.is_empty()
    {
        Err(Error::Underflow)
    }
    else
    {
        let n = nr.len();
        for digit in nr[..n-1].iter_mut()
        {
            if !digit.dec()
            {
                return Ok(n);
            }
        }

        if nr[n-1].dec()
        {
            Err(Error::Underflow)
        }
        else if nr[n-1].is_zero()
        {
            Ok(n-1)
        }
        else
        {
            Ok(n)
        }
    }
}

/// Subtract the single digit `digit` from the number or number part represented by the digits in
/// `nr`, and return the number of digits in the result. If `digit` is larger than `nr`, an
/// Underflow error is returned.
pub fn sub_assign_digit<T>(nr: &mut [T], digit: T) -> Result<usize>
where T: Digit
{
    if digit.is_zero()
    {
        Ok(nr.len())
    }
    else if nr.is_empty()
    {
        Err(Error::Underflow)
    }
    else if nr[0].sub_carry_assign(digit, false)
    {
        let nd = dec_assign(&mut nr[1..])?;
        Ok(1 + nd)
    }
    else
    {
        Ok(nr.len())
    }
}

/// Subtract the big number represented by the digits in `n1` from the number or number part represented
/// by `n0`, and returns the number of digits in the result. If `nr1` is greater than `nr0`, an
/// `Underflow` error is returned.
pub fn sub_assign_big<T>(nr0: &mut [T], nr1: &[T]) -> Result<usize>
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    if n0 < n1
    {
        Err(Error::Underflow)
    }
    else
    {
        let carry = nr0.iter_mut().zip(nr1).fold(false, |carry, (d0, &d1)| d0.sub_carry_assign(d1, carry));
        if carry
        {
            let nd = dec_assign(&mut nr0[n1..])?;
            Ok(n1 + nd)
        }
        else
        {
            Ok(drop_leading_zeros(nr0, n0))
        }
    }
}

/// Subtract the big numbers represented by the digits in `nr0` and `nr1`, and store the result in
/// `diff`. Returns the number of digits in the differene, a `NoSpace` error if the difference
/// cannot be stored in `diff`, or an `Underflow` error if `nr0 < nr1`.
/// NOTE: a `NoSpace` error is also returned if any leading zeros as a result of the subtraction
/// cannot be stored. Therefore, `diff` should be able to contain at least as many digits as
/// `nr0` is long.
pub fn sub_big_into<T>(nr0: &[T], nr1: &[T], diff: &mut [T]) -> Result<usize>
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    if diff.len() < n0
    {
        Err(Error::NoSpace)
    }
    else if n0 < n1
    {
        Err(Error::Underflow)
    }
    else
    {
        let mut carry = false;
        for ((&d0, &d1), dr) in nr0.iter().zip(nr1).zip(diff.iter_mut())
        {
            *dr = d0;
            carry = dr.sub_carry_assign(d1, carry);
        }

        diff[n1..n0].copy_from_slice(&nr0[n1..]);
        if carry
        {
            let nd = dec_assign(&mut diff[n1..n0])?;
            Ok(n1 + nd)
        }
        else
        {
            let n = drop_leading_zeros(diff, n0);
            Ok(n)
        }
    }
}

/// Subtract `nr1` from `nr0`, leaving the absolute value of the difference in `nr0`. Returns the
/// sign of the difference, and the number of digits it contains. The initial length of the number
/// stored in `nr0` is `len0` digits, but the array should be large enough to compute the difference,
/// i.e. `nr0.len() ≥ max(len, nr1.len())`.
pub fn sub_assign_big_abs_sign<T>(nr0: &mut [T], len0: usize, nr1: &[T]) -> (bool, usize)
where T: Digit
{
    if crate::ubig::cmp::lt(&nr0[..len0], nr1)
    {
        let nd = crate::ubig::rsub::rsub_assign_big(&mut nr0[..nr1.len()], nr1).unwrap();
        (true, nd)
    }
    else
    {
        let nd = crate::ubig::sub::sub_assign_big(&mut nr0[..len0], nr1).unwrap();
        (false, nd)
    }
}

/// Subtract `nr1` from `nr0`, and store the absolute value of the difference in `abs_diff`.
/// Return the sign of the difference, and the number of digits it contains. `abs_diff` should
/// be able to hold at least as many digits as the longest of `nr0` and `nr1`.
pub fn sub_big_into_abs_sign<T>(nr0: &[T], nr1: &[T], abs_diff: &mut[T]) -> (bool, usize)
where T: Digit
{
    debug_assert!(abs_diff.len() >= nr0.len().max(nr1.len()));
    if crate::ubig::cmp::lt(nr0, nr1)
    {
        (true, sub_big_into(nr1, nr0, abs_diff).unwrap())
    }
    else
    {
        (false, sub_big_into(nr0, nr1, abs_diff).unwrap())
    }
}

#[cfg(test)]
mod tests
{
    use crate::digit::{DecimalDigit, BinaryDigit};
    use super::*;

    #[test]
    fn test_dec_assign_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, []);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(1u8)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0)]);
        assert_eq!(res, Ok(0));

        let mut nr = [BinaryDigit(0u8)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(0u8), BinaryDigit(1)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr = [BinaryDigit(0u8), BinaryDigit(1), BinaryDigit(3)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0), BinaryDigit(3)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(3)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(2)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(0)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xff)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert_eq!(res, Ok(2));

        let mut nr = [BinaryDigit(0u32), BinaryDigit(0xff)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xffffffff), BinaryDigit(0xfe)]);
        assert_eq!(res, Ok(2));

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xffffffff)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xfe), BinaryDigit(0xffffffff)]);
        assert_eq!(res, Ok(2));

        let mut nr = [BinaryDigit(0u32), BinaryDigit(0)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xffffffff), BinaryDigit(0xffffffff)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_dec_assign_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, []);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(1u8)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0)]);
        assert_eq!(res, Ok(0));

        let mut nr = [DecimalDigit(0u8)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(0u8), DecimalDigit(1)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr = [DecimalDigit(0u8), DecimalDigit(1), DecimalDigit(3)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(0), DecimalDigit(3)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(3)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(99), DecimalDigit(2)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(99u32), DecimalDigit(99)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(98), DecimalDigit(99)]);
        assert_eq!(res, Ok(2));

        let mut nr = [DecimalDigit(0u32), DecimalDigit(99)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(999_999_999), DecimalDigit(98)]);
        assert_eq!(res, Ok(2));

        let mut nr = [DecimalDigit(99u32), DecimalDigit(999_999_999)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(98), DecimalDigit(999_999_999)]);
        assert_eq!(res, Ok(2));

        let mut nr = [DecimalDigit(0u32), DecimalDigit(0)];
        let res = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(999_999_999), DecimalDigit(999_999_999)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_assign_digit_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, []);
        assert_eq!(res, Ok(0));

        let mut nr: [BinaryDigit<u8>; 0] = [];
        let res = sub_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, []);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(1u8)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, [BinaryDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr = [BinaryDigit(48u8)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, [BinaryDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr = [BinaryDigit(1u8)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x7c)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(1)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0), BinaryDigit(0xfe)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0xff), BinaryDigit(0xfd)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0), BinaryDigit(0)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(0x105u16), BinaryDigit(0xff), BinaryDigit(0xff)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(5u16), BinaryDigit(0), BinaryDigit(0)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xff80), BinaryDigit(0xffff), BinaryDigit(0xffff)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [BinaryDigit(0x105u32), BinaryDigit(0xff), BinaryDigit(0xff)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(5u32), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xffffff80), BinaryDigit(0xfffe), BinaryDigit(0xffff)]);
        assert_eq!(res, Ok(3));

        let mut nr = [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0)];
        let res = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xffffff80u32), BinaryDigit(0xffffffff), BinaryDigit(0xffffffff)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let res = sub_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, []);
        assert_eq!(res, Ok(0));

        let mut nr: [DecimalDigit<u8>; 0] = [];
        let res = sub_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, []);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(1u8)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, [DecimalDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr = [DecimalDigit(48u8)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, [DecimalDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr = [DecimalDigit(5u8)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(5u8), DecimalDigit(1)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(0)]);
        assert_eq!(res, Ok(1));

        let mut nr = [DecimalDigit(5u8), DecimalDigit(0), DecimalDigit(99)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(98)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(5u8), DecimalDigit(0), DecimalDigit(0)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(105u16), DecimalDigit(99), DecimalDigit(99)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(5u16), DecimalDigit(0), DecimalDigit(0)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(9_950), DecimalDigit(9_999), DecimalDigit(9_999)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr = [DecimalDigit(105u32), DecimalDigit(99), DecimalDigit(99)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(5u32), DecimalDigit(10_000), DecimalDigit(9_999)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(999_999_950), DecimalDigit(9_999), DecimalDigit(9_999)]);
        assert_eq!(res, Ok(3));

        let mut nr = [DecimalDigit(5), DecimalDigit(0), DecimalDigit(0)];
        let res = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(999_999_950u32), DecimalDigit(999_999_999), DecimalDigit(999_999_999)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_assign_big_binary()
    {
        let mut nr0 = [BinaryDigit(1u8)];
        let nr1 = [];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [BinaryDigit(0xffu8)];
        let nr1 = [BinaryDigit(0xfeu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [BinaryDigit(0u8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [BinaryDigit(0x7fu8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(2)];
        let nr1 = [BinaryDigit(0xffu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(1)]);
        assert_eq!(res, Ok(2));

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0), BinaryDigit(0xff), BinaryDigit(0xff)];
        let nr1 = [BinaryDigit(0xffu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert_eq!(res, Ok(4));

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)];
        let nr1 = [BinaryDigit(0xffu8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_assign_big_decimal()
    {
        let mut nr0 = [DecimalDigit(1u8)];
        let nr1 = [];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [DecimalDigit(99u8)];
        let nr1 = [DecimalDigit(98u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(res, Ok(1));

        let mut nr0 = [DecimalDigit(0u8)];
        let nr1 = [DecimalDigit(99u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [DecimalDigit(49u8)];
        let nr1 = [DecimalDigit(99u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50)]);
        assert_eq!(res, Err(Error::Underflow));

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(2)];
        let nr1 = [DecimalDigit(99u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(1)]);
        assert_eq!(res, Ok(2));

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(0), DecimalDigit(99), DecimalDigit(99)];
        let nr1 = [DecimalDigit(99u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(98), DecimalDigit(99)]);
        assert_eq!(res, Ok(4));

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)];
        let nr1 = [DecimalDigit(99u8)];
        let res = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(res, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_big_into_binary()
    {
        let nr0: [BinaryDigit<u8>; 0] = [];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let mut diff = [];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(0));
        assert_eq!(diff, []);

        let nr0 = [BinaryDigit(1u8), BinaryDigit(2)];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let mut diff = [BinaryDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [BinaryDigit(1), BinaryDigit(2)]);

        let nr0 = [BinaryDigit(1u8), BinaryDigit(2)];
        let nr1 = [BinaryDigit(1u8)];
        let mut diff = [BinaryDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [BinaryDigit(0), BinaryDigit(2)]);

        let nr0 = [BinaryDigit(1u8), BinaryDigit(2u8)];
        let nr1 = [BinaryDigit(2u8)];
        let mut diff = [BinaryDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [BinaryDigit(0xff), BinaryDigit(1)]);

        let nr0 = [BinaryDigit(1u8), BinaryDigit(1u8)];
        let nr1 = [BinaryDigit(2u8)];
        let mut diff = [BinaryDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(1));
        assert_eq!(diff, [BinaryDigit(0xff), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0x2518af54u32), BinaryDigit(0xf6271615), BinaryDigit(0xa5617882)];
        let nr1 = [BinaryDigit(0x38278919u32), BinaryDigit(0xffffffff), BinaryDigit(0x76552298)];
        let mut diff = [BinaryDigit(0); 3];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(3));
        assert_eq!(diff, [BinaryDigit(0xecf1263b), BinaryDigit(0xf6271615), BinaryDigit(0x2f0c55e9)]);
    }

    #[test]
    fn test_sub_big_into_decimal()
    {
        let nr0: [DecimalDigit<u8>; 0] = [];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let mut diff = [];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(0));
        assert_eq!(diff, []);

        let nr0 = [DecimalDigit(1u8), DecimalDigit(2)];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let mut diff = [DecimalDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [DecimalDigit(1), DecimalDigit(2)]);

        let nr0 = [DecimalDigit(1u8), DecimalDigit(2)];
        let nr1 = [DecimalDigit(1u8)];
        let mut diff = [DecimalDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [DecimalDigit(0), DecimalDigit(2)]);

        let nr0 = [DecimalDigit(1u8), DecimalDigit(2u8)];
        let nr1 = [DecimalDigit(2u8)];
        let mut diff = [DecimalDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(2));
        assert_eq!(diff, [DecimalDigit(99), DecimalDigit(1)]);

        let nr0 = [DecimalDigit(1u8), DecimalDigit(1u8)];
        let nr1 = [DecimalDigit(2u8)];
        let mut diff = [DecimalDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(1));
        assert_eq!(diff, [DecimalDigit(99), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(837_984_655u32), DecimalDigit(982_376_123), DecimalDigit(761_233_341)];
        let nr1 = [DecimalDigit(899_987_987u32), DecimalDigit(213_872_166), DecimalDigit(688_231_987)];
        let mut diff = [DecimalDigit(0); 3];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Ok(3));
        assert_eq!(diff, [DecimalDigit(937_996_668), DecimalDigit(768_503_956), DecimalDigit(73_001_354)]);
    }

    #[test]
    fn test_sub_big_into_nospace()
    {
        let nr0 = [DecimalDigit(837_984_655u32), DecimalDigit(982_376_123), DecimalDigit(761_233_341)];
        let nr1 = [DecimalDigit(899_987_987u32), DecimalDigit(213_872_166), DecimalDigit(688_231_987)];
        let mut diff = [DecimalDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Err(Error::NoSpace));

        let nr0 = [BinaryDigit(0x4518af54u32), BinaryDigit(0xf6271615), BinaryDigit(0xa5617882)];
        let nr1 = [BinaryDigit(0x38278919u32), BinaryDigit(0xf6271615), BinaryDigit(0xa5617882)];
        let mut diff = [BinaryDigit(0); 2];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Err(Error::NoSpace));
    }

    #[test]
    fn test_sub_big_into_underflow()
    {
        let nr0 = [DecimalDigit(837_984_655u32), DecimalDigit(982_376_123)];
        let nr1 = [DecimalDigit(899_987_987u32), DecimalDigit(213_872_166), DecimalDigit(688_231_987)];
        let mut diff = [DecimalDigit(0); 3];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Err(Error::Underflow));

        let nr0 = [BinaryDigit(0x3518af54u32), BinaryDigit(0xf6271615), BinaryDigit(0xa5617882)];
        let nr1 = [BinaryDigit(0x38278919u32), BinaryDigit(0xf6271615), BinaryDigit(0xa5617882)];
        let mut diff = [BinaryDigit(0); 3];
        let n = sub_big_into(&nr0, &nr1, &mut diff);
        assert_eq!(n, Err(Error::Underflow));
    }

    #[test]
    fn test_sub_assign_big_abs_sign_binary()
    {
        let mut nr0: [BinaryDigit<u8>; 0] = [];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 0, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 0);
        assert_eq!(nr0, []);

        let mut nr0 = [BinaryDigit(1u8)];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 1, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 1);
        assert_eq!(nr0, [BinaryDigit(1)]);

        let mut nr0 = [BinaryDigit(0u8)];
        let nr1 = [BinaryDigit(1u8)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 0, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(nr0, [BinaryDigit(1)]);

        let mut nr0 = [BinaryDigit(0x40u16), BinaryDigit(0x43)];
        let nr1 = [BinaryDigit(0x41u16), BinaryDigit(0x43)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 2, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(nr0, [BinaryDigit(1), BinaryDigit(0)]);

        let mut nr0 = [
            BinaryDigit(0x672288af5189ff45u64),
            BinaryDigit(0xff453615af3f724d),
            BinaryDigit(0x282786fdf35eca)
        ];
        let nr1 = [BinaryDigit(0x71898279dfacdf33u64), BinaryDigit(0x6fd527ade516ee12)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 3, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 3);
        assert_eq!(nr0, [
            BinaryDigit(0xf599063571dd2012),
            BinaryDigit(0x8f700e67ca28843a),
            BinaryDigit(0x282786fdf35eca)
        ]);

        let mut nr0 = [BinaryDigit(0x71898279dfacdf33u64), BinaryDigit(0x6fd527ade516ee12), BinaryDigit(0)];
        let nr1 = [BinaryDigit(0x672288af5189ff45u64), BinaryDigit(0xff453615af3f724d), BinaryDigit(0x282786fdf35eca)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 2, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 3);
        assert_eq!(nr0, [
            BinaryDigit(0xf599063571dd2012),
            BinaryDigit(0x8f700e67ca28843a),
            BinaryDigit(0x282786fdf35eca)
        ]);
    }

    #[test]
    fn test_sub_assign_big_abs_sign_decimal()
    {
        let mut nr0: [DecimalDigit<u8>; 0] = [];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 0, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 0);
        assert_eq!(nr0, []);

        let mut nr0 = [DecimalDigit(1u8)];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 1, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 1);
        assert_eq!(nr0, [DecimalDigit(1)]);

        let mut nr0 = [DecimalDigit(0u8)];
        let nr1 = [DecimalDigit(1u8)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 0, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(nr0, [DecimalDigit(1)]);

        let mut nr0 = [DecimalDigit(4_000u16), DecimalDigit(4_321)];
        let nr1 = [DecimalDigit(4_001u16), DecimalDigit(4_321)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 2, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(nr0, [DecimalDigit(1), DecimalDigit(0)]);

        let mut nr0 = [
            DecimalDigit(5_748_918_999_164_244_199u64),
            DecimalDigit(9_332_982_876_466_454_782),
            DecimalDigit(123)
        ];
        let nr1 = [DecimalDigit(5_983_299_918_982_872_456u64), DecimalDigit(9_564_555_736_893_987_342)];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 3, &nr1);
        assert_eq!(sign, false);
        assert_eq!(len, 3);
        assert_eq!(nr0, [
            DecimalDigit(9_765_619_080_181_371_743),
            DecimalDigit(9_768_427_139_572_467_439),
            DecimalDigit(122)
        ]);

        let mut nr0 = [
            DecimalDigit(5_983_299_918_982_872_456u64),
            DecimalDigit(9_564_555_736_893_987_342),
            DecimalDigit(0)
        ];
        let nr1 = [
            DecimalDigit(5_748_918_999_164_244_199u64),
            DecimalDigit(9_332_982_876_466_454_782),
            DecimalDigit(123)
        ];
        let (sign, len) = sub_assign_big_abs_sign(&mut nr0, 3, &nr1);
        assert_eq!(sign, true);
        assert_eq!(len, 3);
        assert_eq!(nr0, [
            DecimalDigit(9_765_619_080_181_371_743),
            DecimalDigit(9_768_427_139_572_467_439),
            DecimalDigit(122)
        ]);
    }

    #[test]
    fn test_sub_big_into_abs_sign_binary()
    {
        let nr0: [BinaryDigit<u8>; 0] = [];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let mut abs_diff = [BinaryDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 0);
        assert_eq!(abs_diff, [BinaryDigit(0)]);

        let nr0 = [BinaryDigit(1u8)];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let mut abs_diff = [BinaryDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [BinaryDigit(1)]);

        let nr0: [BinaryDigit<u8>; 0] = [];
        let nr1 = [BinaryDigit(1u8)];
        let mut abs_diff = [BinaryDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [BinaryDigit(1)]);

        let nr0 = [BinaryDigit(0x40u16), BinaryDigit(0x43)];
        let nr1 = [BinaryDigit(0x41u16), BinaryDigit(0x43)];
        let mut abs_diff = [BinaryDigit(0); 2];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [BinaryDigit(1), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0x672288af5189ff45u64), BinaryDigit(0xff453615af3f724d), BinaryDigit(0x282786fdf35eca)];
        let nr1 = [BinaryDigit(0x71898279dfacdf33u64), BinaryDigit(0x6fd527ade516ee12)];
        let mut abs_diff = [BinaryDigit(0); 3];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 3);
        assert_eq!(abs_diff, [BinaryDigit(0xf599063571dd2012), BinaryDigit(0x8f700e67ca28843a), BinaryDigit(0x282786fdf35eca)]);

        let nr0 = [BinaryDigit(0x71898279dfacdf33u64), BinaryDigit(0x6fd527ade516ee12)];
        let nr1 = [BinaryDigit(0x672288af5189ff45u64), BinaryDigit(0xff453615af3f724d), BinaryDigit(0x282786fdf35eca)];
        let mut abs_diff = [BinaryDigit(0); 3];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 3);
        assert_eq!(abs_diff, [BinaryDigit(0xf599063571dd2012), BinaryDigit(0x8f700e67ca28843a), BinaryDigit(0x282786fdf35eca)]);
    }

    #[test]
    fn test_sub_big_into_abs_sign_decimal()
    {
        let nr0: [DecimalDigit<u8>; 0] = [];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let mut abs_diff = [DecimalDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 0);
        assert_eq!(abs_diff, [DecimalDigit(0)]);

        let nr0 = [DecimalDigit(1u8)];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let mut abs_diff = [DecimalDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [DecimalDigit(1)]);

        let nr0: [DecimalDigit<u8>; 0] = [];
        let nr1 = [DecimalDigit(1u8)];
        let mut abs_diff = [DecimalDigit(0); 1];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [DecimalDigit(1)]);

        let nr0 = [DecimalDigit(4_000u16), DecimalDigit(4_321)];
        let nr1 = [DecimalDigit(4_001u16), DecimalDigit(4_321)];
        let mut abs_diff = [DecimalDigit(0); 2];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 1);
        assert_eq!(abs_diff, [DecimalDigit(1), DecimalDigit(0)]);

        let nr0 = [
            DecimalDigit(5_748_918_999_164_244_199u64),
            DecimalDigit(9_332_982_876_466_454_782),
            DecimalDigit(123)
        ];
        let nr1 = [DecimalDigit(5_983_299_918_982_872_456u64), DecimalDigit(9_564_555_736_893_987_342)];
        let mut abs_diff = [DecimalDigit(0); 3];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, false);
        assert_eq!(len, 3);
        assert_eq!(abs_diff, [
            DecimalDigit(9_765_619_080_181_371_743),
            DecimalDigit(9_768_427_139_572_467_439),
            DecimalDigit(122)
        ]);

        let nr0 = [DecimalDigit(5_983_299_918_982_872_456u64), DecimalDigit(9_564_555_736_893_987_342)];
        let nr1 = [
            DecimalDigit(5_748_918_999_164_244_199u64),
            DecimalDigit(9_332_982_876_466_454_782),
            DecimalDigit(123)
        ];
        let mut abs_diff = [DecimalDigit(0); 3];
        let (sign, len) = sub_big_into_abs_sign(&nr0, &nr1, &mut abs_diff);
        assert_eq!(sign, true);
        assert_eq!(len, 3);
        assert_eq!(abs_diff, [
            DecimalDigit(9_765_619_080_181_371_743),
            DecimalDigit(9_768_427_139_572_467_439),
            DecimalDigit(122)
        ]);
    }
}
