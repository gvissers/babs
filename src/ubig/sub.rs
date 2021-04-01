use crate::digit::Digit;

/// Decrement the numer or number part represented by the digits in `nr` by one, and return the
/// carry on underflow, or `None` if the number does not underflow.
pub fn dec_assign<T>(nr: &mut [T]) -> Option<T>
where T: Digit
{
    for digit in nr.iter_mut()
    {
        if !digit.dec()
        {
            return None;
        }
    }
    Some(T::one())
}

/// Subtract the single digit `digit` from the number or number part represented by the digits in
/// `nr`, and return the carry on underflow, or `None` if the number does not underflow.
pub fn sub_assign_digit<T>(nr: &mut [T], digit: T) -> Option<T>
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
    else if nr[0].sub_assign(digit)
    {
        dec_assign(&mut nr[1..])
    }
    else
    {
        None
    }
}

/// Subtract the big number represented by te digits in `n1` from the number or number part represented
/// by `n0`, and return the carry on underflow, or `None` if the number does not underflow. The length
/// of `nr1` must not be greater than the length of `nr0`.
pub fn sub_assign_big<T>(nr0: &mut [T], nr1: &[T]) -> Option<T>
where T: Digit
{
    assert!(nr1.len() <= nr0.len());

    let mut carry = false;
    for (d0, &d1) in nr0.iter_mut().zip(nr1)
    {
        if carry
        {
            carry = d0.dec();
        }
        carry |= d0.sub_assign(d1)
    }

    if carry
    {
        dec_assign(&mut nr0[nr1.len()..])
    }
    else
    {
        None
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
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, []);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(1u8)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u8)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0u8), BinaryDigit(1)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u8), BinaryDigit(1), BinaryDigit(3)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0), BinaryDigit(3)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(3)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(2)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u8), BinaryDigit(0), BinaryDigit(0)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xff)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u32), BinaryDigit(0xff)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xffffffff), BinaryDigit(0xfe)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0xffu32), BinaryDigit(0xffffffff)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xfe), BinaryDigit(0xffffffff)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0u32), BinaryDigit(0)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [BinaryDigit(0xffffffff), BinaryDigit(0xffffffff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));
    }

    #[test]
    fn test_dec_assign_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, []);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(1u8)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u8)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(0u8), DecimalDigit(1)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u8), DecimalDigit(1), DecimalDigit(3)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(0), DecimalDigit(3)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(3)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(99), DecimalDigit(2)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u8), DecimalDigit(0), DecimalDigit(0)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(99), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(99u32), DecimalDigit(99)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(98), DecimalDigit(99)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u32), DecimalDigit(99)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(999_999_999), DecimalDigit(98)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(99u32), DecimalDigit(999_999_999)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(98), DecimalDigit(999_999_999)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(0u32), DecimalDigit(0)];
        let underflow = dec_assign(&mut nr);
        assert_eq!(nr, [DecimalDigit(999_999_999), DecimalDigit(999_999_999)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));
    }

    #[test]
    fn test_sub_assign_digit_binary()
    {
        let mut nr: [BinaryDigit<u8>; 0] = [];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, []);
        assert_eq!(underflow, None);

        let mut nr: [BinaryDigit<u8>; 0] = [];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, []);
        assert_eq!(underflow, Some(BinaryDigit(47)));

        let mut nr = [BinaryDigit(1u8)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0));
        assert_eq!(nr, [BinaryDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(48u8)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(47));
        assert_eq!(nr, [BinaryDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(1u8)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x7c)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(1)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0), BinaryDigit(0xfe)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0xff), BinaryDigit(0xfd)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(0x80u8), BinaryDigit(0), BinaryDigit(0)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xfb), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x105u16), BinaryDigit(0xff), BinaryDigit(0xff)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(5u16), BinaryDigit(0), BinaryDigit(0)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xff80), BinaryDigit(0xffff), BinaryDigit(0xffff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr = [BinaryDigit(0x105u32), BinaryDigit(0xff), BinaryDigit(0xff)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(5u32), BinaryDigit(0xffff), BinaryDigit(0xffff)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xffffff80), BinaryDigit(0xfffe), BinaryDigit(0xffff)]);
        assert_eq!(underflow, None);

        let mut nr = [BinaryDigit(5), BinaryDigit(0), BinaryDigit(0)];
        let underflow = sub_assign_digit(&mut nr, BinaryDigit(0x85));
        assert_eq!(nr, [BinaryDigit(0xffffff80u32), BinaryDigit(0xffffffff), BinaryDigit(0xffffffff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));
    }

    #[test]
    fn test_sub_assign_digit_decimal()
    {
        let mut nr: [DecimalDigit<u8>; 0] = [];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, []);
        assert_eq!(underflow, None);

        let mut nr: [DecimalDigit<u8>; 0] = [];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, []);
        assert_eq!(underflow, Some(DecimalDigit(47)));

        let mut nr = [DecimalDigit(1u8)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(0));
        assert_eq!(nr, [DecimalDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(48u8)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(47));
        assert_eq!(nr, [DecimalDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5u8)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(5u8), DecimalDigit(1)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(0)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5u8), DecimalDigit(0), DecimalDigit(99)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(98)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5u8), DecimalDigit(0), DecimalDigit(0)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(105u16), DecimalDigit(99), DecimalDigit(99)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5u16), DecimalDigit(0), DecimalDigit(0)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(9_950), DecimalDigit(9_999), DecimalDigit(9_999)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr = [DecimalDigit(105u32), DecimalDigit(99), DecimalDigit(99)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5u32), DecimalDigit(10_000), DecimalDigit(9_999)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(999_999_950), DecimalDigit(9_999), DecimalDigit(9_999)]);
        assert_eq!(underflow, None);

        let mut nr = [DecimalDigit(5), DecimalDigit(0), DecimalDigit(0)];
        let underflow = sub_assign_digit(&mut nr, DecimalDigit(55));
        assert_eq!(nr, [DecimalDigit(999_999_950u32), DecimalDigit(999_999_999), DecimalDigit(999_999_999)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));
    }

    #[test]
    fn test_sub_assign_big_binary()
    {
        let mut nr0 = [BinaryDigit(1u8)];
        let nr1 = [];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [BinaryDigit(0xffu8)];
        let nr1 = [BinaryDigit(0xfeu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [BinaryDigit(0u8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(1)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr0 = [BinaryDigit(0x7fu8)];
        let nr1 = [BinaryDigit(0xffu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(2)];
        let nr1 = [BinaryDigit(0xffu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0), BinaryDigit(0xff), BinaryDigit(0xff)];
        let nr1 = [BinaryDigit(0xffu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert_eq!(underflow, None);

        let mut nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0)];
        let nr1 = [BinaryDigit(0xffu8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x80), BinaryDigit(0xff), BinaryDigit(0xff), BinaryDigit(0xff)]);
        assert_eq!(underflow, Some(BinaryDigit(1)));
    }

    #[test]
    fn test_sub_assign_big_decimal()
    {
        let mut nr0 = [DecimalDigit(1u8)];
        let nr1 = [];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [DecimalDigit(99u8)];
        let nr1 = [DecimalDigit(98u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [DecimalDigit(0u8)];
        let nr1 = [DecimalDigit(99u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(1)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr0 = [DecimalDigit(49u8)];
        let nr1 = [DecimalDigit(99u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(2)];
        let nr1 = [DecimalDigit(99u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(1)]);
        assert_eq!(underflow, None);

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(0), DecimalDigit(99), DecimalDigit(99)];
        let nr1 = [DecimalDigit(99u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(98), DecimalDigit(99)]);
        assert_eq!(underflow, None);

        let mut nr0 = [DecimalDigit(49u8), DecimalDigit(0), DecimalDigit(0), DecimalDigit(0)];
        let nr1 = [DecimalDigit(99u8)];
        let underflow = sub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(50), DecimalDigit(99), DecimalDigit(99), DecimalDigit(99)]);
        assert_eq!(underflow, Some(DecimalDigit(1)));
    }
}
