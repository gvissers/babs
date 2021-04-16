use crate::digit::Digit;
use crate::result::{Error, Result};

/// Increment the numer or number part represented by the digits in `nr` by one, and return
/// whether the number overflows.
pub fn inc_assign<T>(nr: &mut [T]) -> bool
where T: Digit
{
    for digit in nr.iter_mut()
    {
        if !digit.inc()
        {
            return false;
        }
    }
    true
}

/// Add the single digit `digit` to the number or number part represented by the digits in `nr`,
/// and return the carry on overflow, or `None` if the number does not overflow.
pub fn add_assign_digit<T>(nr: &mut [T], digit: T) -> Option<T>
where T: Digit
{
    if digit.is_zero()
    {
        None
    }
    else if nr.is_empty()
    {
        Some(digit)
    }
    else if nr[0].add_carry_assign(digit, false)
    {
        inc_assign(&mut nr[1..]).then(T::one)
    }
    else
    {
        None
    }
}

/// Add the big number represented by the digits in `n1` to the number or number part represented
/// by `n0`, and return whether the number overflows. The length of `nr1` must not be greater than
/// the length of `nr0`.
pub fn add_assign_big<T>(nr0: &mut [T], nr1: &[T]) -> bool
where T: Digit
{
    assert!(nr1.len() <= nr0.len());

    let mut carry = false;
    for (d0, &d1) in nr0.iter_mut().zip(nr1)
    {
        carry = d0.add_carry_assign(d1, carry);
    }

    carry && inc_assign(&mut nr0[nr1.len()..])
}

/// Add the big numbers represented by the digits in `nr0` and `nr1`, and store the result in
/// `sum`. Returns the number of digits used by the sum, or a `NoSpace` error if the result will
/// not fit in `sum`.
pub fn add_big_into<T>(nr0: &[T], nr1: &[T], sum: &mut [T]) -> Result<usize>
where T: Digit
{
    let n0 = nr0.len();
    let n1 = nr1.len();
    let nmin = n0.min(n1);
    let nmax = n0.max(n1);
    if sum.len() < nmax
    {
        Err(Error::NoSpace)
    }
    else
    {
        let mut carry = false;
        for ((&d0, &d1), dr) in nr0.iter().zip(nr1).zip(sum.iter_mut())
        {
            *dr = d0;
            carry = dr.add_carry_assign(d1, carry);
        }

        match n0.cmp(&n1)
        {
            std::cmp::Ordering::Equal   => { /* do nothing */ },
            std::cmp::Ordering::Less    => { sum[nmin..nmax].copy_from_slice(&nr1[nmin..]); },
            std::cmp::Ordering::Greater => { sum[nmin..nmax].copy_from_slice(&nr0[nmin..]); }
        }

        if carry && inc_assign(&mut sum[nmin..nmax])
        {
            if sum.len() <= nmax
            {
                Err(Error::NoSpace)
            }
            else
            {
                sum[nmax] = T::one();
                Ok(nmax + 1)
            }
        }
        else
        {
            Ok(nmax)
        }
    }
}

#[cfg(test)]
mod tests
{
    use crate::digit::{DecimalDigit, BinaryDigit};
    use super::*;

    #[test]
    fn test_inc_assign_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, []);
        assert!(overflow);

        let mut nr = [BinaryDigit(1u8)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(2)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffu8)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0)]);
        assert!(overflow);

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(1)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(2)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(1), BinaryDigit(3)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(2), BinaryDigit(3)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(0xff), BinaryDigit(3)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(4)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffu8), BinaryDigit(0xff), BinaryDigit(0xff)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)]);
        assert!(overflow);

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xff)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0x100), BinaryDigit(0xff)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffffffffu32), BinaryDigit(0xff)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(0x100)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xffffffff)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0x100), BinaryDigit(0xffffffff)]);
        assert!(!overflow);

        let mut nr = [BinaryDigit(0xffffffffu32), BinaryDigit(0xffffffff)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0), BinaryDigit(0)]);
        assert!(overflow);
    }

    #[test]
    fn test_inc_assign_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, []);
        assert!(overflow);

        let mut nr = [DecimalDigit(1u8)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(2)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(99u8)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0)]);
        assert!(overflow);

        let mut nr = [DecimalDigit(99u8), DecimalDigit(1)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(2)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(99u8), DecimalDigit(1), DecimalDigit(3)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(2), DecimalDigit(3)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(99u8), DecimalDigit(99), DecimalDigit(3)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(4)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(99u8), DecimalDigit(99), DecimalDigit(99)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)]);
        assert!(overflow);

        let mut nr = [DecimalDigit(99u32), DecimalDigit(99)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(100), DecimalDigit(99)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(999_999_999u32), DecimalDigit(99)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(100)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(99u32), DecimalDigit(999_999_999)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(100), DecimalDigit(999_999_999)]);
        assert!(!overflow);

        let mut nr = [DecimalDigit(999_999_999u32), DecimalDigit(999_999_999)];
        let overflow = inc_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0), DecimalDigit(0)]);
        assert!(overflow);
    }

    #[test]
    fn test_add_assign_digit_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, []);
        assert_eq!(overflow, None);

        let mut nr: [BinaryDigit<u8>; 0] = [];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, []);
        assert_eq!(overflow, Some(BinaryDigit(47)));

        let mut nr = [BinaryDigit(1u8)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, [BinaryDigit(1)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(1u8)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, [BinaryDigit(48)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0x80u8)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5)]);
        assert_eq!(overflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(1)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0xff), BinaryDigit(0xfe)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0xff)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0xff), BinaryDigit(0xff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(overflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x80u16), BinaryDigit(0xff), BinaryDigit(0xff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x105), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0xff80u16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(overflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x80u32), BinaryDigit(0xff), BinaryDigit(0xff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x105), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0xffffff80u32), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(0x10000), BinaryDigit(0xffff)]);
        assert_eq!(overflow, None);

        let mut nr = [BinaryDigit(0xffffff80u32), BinaryDigit(0xffffffff), BinaryDigit(0xffffffff)];
        let overflow = add_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0)]);
        assert_eq!(overflow, Some(BinaryDigit(1)));
    }

    #[test]
    fn test_add_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, []);
        assert_eq!(overflow, None);

        let mut nr: [DecimalDigit<u8>; 0] = [];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, []);
        assert_eq!(overflow, Some(DecimalDigit(47)));

        let mut nr = [DecimalDigit(1u8)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, [DecimalDigit(1)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(1u8)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, [DecimalDigit(48)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(50u8)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5)]);
        assert_eq!(overflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(50u8), DecimalDigit(0)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(1)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(50u8), DecimalDigit(99), DecimalDigit(98)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(0), DecimalDigit(99)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(50u8), DecimalDigit(99), DecimalDigit(99)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(overflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(50u16), DecimalDigit(99), DecimalDigit(99)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(105), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(9_950u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(overflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(50u32), DecimalDigit(99), DecimalDigit(99)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(105), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(999_999_950u32), DecimalDigit(9_999), DecimalDigit(9_999)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(10_000), DecimalDigit(9_999)]);
        assert_eq!(overflow, None);

        let mut nr = [DecimalDigit(999_999_950u32), DecimalDigit(999_999_999), DecimalDigit(999_999_999)];
        let overflow = add_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(5), DecimalDigit(0), DecimalDigit(0)]);
        assert_eq!(overflow, Some(DecimalDigit(1)));
    }

    #[test]
    fn test_add_assign_big_binary()
    {
        let mut nr0 = [BinaryDigit(1u8)];
        let nr1 = [];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert!(!overflow);

        let mut nr0 = [BinaryDigit(1u8)];
        let nr1 = [BinaryDigit(0xfeu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xff)]);
        assert!(!overflow);

        let mut nr0 = [BinaryDigit(1u8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0)]);
        assert!(overflow);

        let mut nr0 = [BinaryDigit(0x80u8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x7f)]);
        assert!(overflow);

        let mut nr0 = [BinaryDigit(0x80u8), BinaryDigit(2)];
        let nr1 = [BinaryDigit(0xffu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x7f), BinaryDigit(3)]);
        assert!(!overflow);

        let mut nr0 = [BinaryDigit(0x80u8), BinaryDigit(0xff), BinaryDigit(0xfe), BinaryDigit(0xff)];
        let nr1 = [BinaryDigit(0xffu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x7f), BinaryDigit(0), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert!(!overflow);

        let mut nr0 = [BinaryDigit(0x80u8), BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)];
        let nr1 = [BinaryDigit(0xffu8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x7f), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)]);
        assert!(overflow);
    }

    #[test]
    fn test_add_assign_big_decimal()
    {
        let mut nr0 = [DecimalDigit(1u8)];
        let nr1 = [];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert!(!overflow);

        let mut nr0 = [DecimalDigit(1u8)];
        let nr1 = [DecimalDigit(98u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(99)]);
        assert!(!overflow);

        let mut nr0 = [DecimalDigit(1u8)];
        let nr1 = [DecimalDigit(99u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(0)]);
        assert!(overflow);

        let mut nr0 = [DecimalDigit(50u8)];
        let nr1 = [DecimalDigit(99u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(49)]);
        assert!(overflow);

        let mut nr0 = [DecimalDigit(50u8), DecimalDigit(2)];
        let nr1 = [DecimalDigit(99u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(49), DecimalDigit(3)]);
        assert!(!overflow);

        let mut nr0 = [DecimalDigit(50u8), DecimalDigit(99), DecimalDigit(98), DecimalDigit(99)];
        let nr1 = [DecimalDigit(99u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(49), DecimalDigit(0), DecimalDigit(99), DecimalDigit(99)]);
        assert!(!overflow);

        let mut nr0 = [DecimalDigit(50u8), DecimalDigit(99), DecimalDigit(99), DecimalDigit(99)];
        let nr1 = [DecimalDigit(99u8)];
        let overflow = add_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(49), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)]);
        assert!(overflow);
    }

    #[test]
    fn test_add_big_into_binary()
    {
        let nr0: [BinaryDigit<u16>; 0] = [];
        let nr1 = [BinaryDigit(0x1234u16)];
        let mut sum = [BinaryDigit(0u16); 2];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(1));
        assert_eq!(sum, [BinaryDigit(0x1234), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0xedcbu16)];
        let nr1 = [BinaryDigit(0x1234u16)];
        let mut sum = [BinaryDigit(0u16); 2];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(1));
        assert_eq!(sum, [BinaryDigit(0xffff), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0xfffeu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16)];
        let mut sum = [BinaryDigit(0u16); 4];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(3));
        assert_eq!(sum, [BinaryDigit(0xffff), BinaryDigit(0xffff), BinaryDigit(0xffff), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0xffffu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16)];
        let mut sum = [BinaryDigit(0u16); 4];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(4));
        assert_eq!(sum, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(1)]);

        let nr0 = [BinaryDigit(0xffffu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16), BinaryDigit(0), BinaryDigit(0), BinaryDigit(22)];
        let mut sum = [BinaryDigit(0u16); 5];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(4));
        assert_eq!(sum, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(23), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0xffffu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0xffff)];
        let mut sum = [BinaryDigit(0u16); 5];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(5));
        assert_eq!(sum, [BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0), BinaryDigit(1)]);
    }

    #[test]
    fn test_add_big_into_binary_overflow()
    {
        let nr0 = [BinaryDigit(0xffffu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16), BinaryDigit(0), BinaryDigit(0), BinaryDigit(22)];
        let mut sum = [BinaryDigit(0u16); 3];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Err(Error::NoSpace));

        let nr0 = [BinaryDigit(0xffffu16), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let nr1 = [BinaryDigit(1u16), BinaryDigit(0), BinaryDigit(0)];
        let mut sum = [BinaryDigit(0u16); 3];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Err(Error::NoSpace));
    }

    #[test]
    fn test_add_big_into_decimal()
    {
        let nr0: [DecimalDigit<u16>; 0] = [];
        let nr1 = [DecimalDigit(1_234u16)];
        let mut sum = [DecimalDigit(0u16); 2];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(1));
        assert_eq!(sum, [DecimalDigit(1234), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(8_765u16)];
        let nr1 = [DecimalDigit(1_234u16)];
        let mut sum = [DecimalDigit(0u16); 2];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(1));
        assert_eq!(sum, [DecimalDigit(9_999), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(9_998u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16)];
        let mut sum = [DecimalDigit(0u16); 4];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(3));
        assert_eq!(sum, [DecimalDigit(9_999), DecimalDigit(9_999), DecimalDigit(9_999), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(9_999u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16)];
        let mut sum = [DecimalDigit(0u16); 4];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(4));
        assert_eq!(sum, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1)]);

        let nr0 = [DecimalDigit(9_999u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16), DecimalDigit(0), DecimalDigit(0), DecimalDigit(22)];
        let mut sum = [DecimalDigit(0u16); 5];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(4));
        assert_eq!(sum, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(23), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(9_999u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16), DecimalDigit(0), DecimalDigit(0), DecimalDigit(9_999)];
        let mut sum = [DecimalDigit(0u16); 5];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Ok(5));
        assert_eq!(sum, [DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1)]);
    }

    #[test]
    fn test_add_big_into_decimal_overflow()
    {
        let nr0 = [DecimalDigit(9_999u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16), DecimalDigit(0), DecimalDigit(0), DecimalDigit(22)];
        let mut sum = [DecimalDigit(0u16); 3];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Err(Error::NoSpace));

        let nr0 = [DecimalDigit(9_999u16), DecimalDigit(9_999), DecimalDigit(9_999)];
        let nr1 = [DecimalDigit(1u16), DecimalDigit(0), DecimalDigit(0)];
        let mut sum = [DecimalDigit(0u16); 3];
        let n = add_big_into(&nr0, &nr1, &mut sum);
        assert_eq!(n, Err(Error::NoSpace));
    }
}
