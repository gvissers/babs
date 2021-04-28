mod add;
mod cmp;
mod div;
mod mul;
mod ops;
mod rsub;
mod shl;
mod shr;
mod sub;
mod support;

use crate::digit::{BinaryDigit, Digit, DigitStorage, DecimalDigit};
use crate::result::{Error, Result};
use num_traits::{Zero, One};
use std::fmt::Write;

/// Structure describing a big number as a series of digits. The base of the number is determined
/// by the digit type `T`. The digits are stored in little-endian order, i.e. the least significant
/// digit is the first.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UBig<T>
{
    /// The digits making up the umber
    digits: Vec<T>
}

impl<T> UBig<T>
{
    /// Create a new big number from the digits in `digits`. The digits should be stored in
    /// little endian order.
    pub fn new(digits: Vec<T>) -> Self
    where T: Zero
    {
        let mut result = UBig { digits };
        result.drop_leading_zeros();
        result
    }

    /// Return the number of digits in this number
    pub fn nr_digits(&self) -> usize
    {
        self.digits.len()
    }

    /// Return the digits this number is made up of
    pub fn digits(&self) -> &[T]
    {
        &self.digits
    }

    /// Remove leading zero from this number, if any
    fn drop_leading_zeros(&mut self)
    where T: Zero
    {
        let cur_n = self.digits.len();
        let new_n = support::drop_leading_zeros(&self.digits, self.digits.len());
        if new_n < cur_n
        {
            self.digits.truncate(new_n);
        }
    }

    /// Add `other * b`<sup>`offset`</sup> to this number, where `b` is the base of this number.
    fn add_assign_big_at_offset(&mut self, other: &Self, offset: usize) -> &mut Self
    where T: Digit
    {
        let n0 = self.nr_digits();
        let n1 = other.nr_digits();
        if n0 <= offset
        {
            self.digits.extend(std::iter::repeat(T::zero()).take(offset - n0));
            self.digits.extend_from_slice(&other.digits);
        }
        else if n1 <= n0 - offset
        {
            if add::add_assign_big(&mut self.digits[offset..], &other.digits)
            {
                self.digits.push(T::one());
            }
        }
        else
        {
            self.digits.extend_from_slice(&other.digits[n0-offset..]);
            if add::add_assign_big(&mut self.digits[offset..], &other.digits[..n0-offset])
            {
                self.digits.push(T::one());
            }
        }

        self
    }

    /// Subtract `other * b`<sup>`offset`</sup> from this number, where `b` is the base of this
    /// number. Returns an `Underflow` error when `other > self`.
    fn sub_assign_big_at_offset(&mut self, other: &Self, offset: usize) -> Result<&mut Self>
    where T: Digit
    {
        let n0 = self.nr_digits();
        let n1 = other.nr_digits();
        if n0 < n1 + offset
            || sub::sub_assign_big(&mut self.digits[offset..], &other.digits)
        {
            Err(Error::Underflow)
        }
        else
        {
            self.drop_leading_zeros();
            Ok(self)
        }
    }

    /// Multiply this number by single digit `fac`, and add digit `offset` to the result
    fn mul_add_assign_digit(&mut self, fac: T, offset: T)
    where T: Digit
    {
        let carry = if fac.is_zero()
            {
                self.digits.clear();
                offset
            }
            else
            {
                mul::mul_add_assign_digit(&mut self.digits, fac, offset)
            };
        if !carry.is_zero()
        {
            self.digits.push(carry);
        }
    }

    /// Multiply this number by the two-digit number `fac_low+b*fac_high`, where `b` is the base
    /// of this number, and add digit `offset` to the result.
    fn mul_pair_add_assign_digit(&mut self, fac_low: T, fac_high: T, offset: T)
    where T: Digit
    {
        let (carry0, carry1) = mul::mul_pair_add_assign_digit(&mut self.digits, fac_low, fac_high, offset);
        if !carry0.is_zero() || !carry1.is_zero()
        {
            self.digits.push(carry0);
            if !carry1.is_zero()
            {
                self.digits.push(carry1);
            }
        }
        self.drop_leading_zeros();
    }

    /// Multiply this number by `other` and return the result
    fn mul_big(&self, other: &Self) -> Self
    where T: Digit
    {
        if self.is_zero() || other.is_zero()
        {
            Self::zero()
        }
        else
        {
            let n0 = self.nr_digits();
            let n1 = other.nr_digits();
            let mut digits = vec![T::zero(); n0+n1];
            let n = mul::mul_big_into(&self.digits, &other.digits(), &mut digits);
            digits.truncate(n);
            UBig { digits }
        }
    }

    /// Return the square of this number
    pub fn square(&self) -> Self
    where T: Digit
    {
        if self.is_zero()
        {
            Self::zero()
        }
        else
        {
            let n0 = self.nr_digits();
            let mut digits = vec![T::zero(); 2*n0];
            let n = mul::square_into(&self.digits, &mut digits);
            digits.truncate(n);
            UBig { digits }
        }
    }

    /// Divide this number by single digit `fac`, and return the remainder. If `fac` is zero,
    /// a `DivisionByZero` error is returned.
    fn div_assign_digit(&mut self, fac: T) -> Result<T>
    where T: Digit
    {
        let (nquot, rem) = div::div_assign_digit(&mut self.digits, fac)?;
        if nquot < self.nr_digits()
        {
            self.digits.truncate(nquot);
        }
        Ok(rem)
    }

    /// Divide this number by the two-digit number `fac_low+b*fac_high`, where `b` is the base
    /// of this number, and return the remainder. If both fac_low and fac_high are zero,
    /// a DivisionByZero error is returned.
    fn div_assign_digit_pair(&mut self, fac_low: T, fac_high: T) -> Result<(T, T)>
    where T: Digit
    {
        let (nquot, rem_low, rem_high) = div::div_assign_digit_pair(&mut self.digits, fac_low, fac_high)?;
        if nquot < self.nr_digits()
        {
            self.digits.truncate(nquot);
        }
        Ok((rem_low, rem_high))
    }

    /// Divide this number by `other`, store the quotient in `self`, and return the remainder. If
    /// `other` is zero, a `DivisionByZero` error is returned.
    pub fn div_assign_big(&mut self, other: &Self) -> Result<Self>
    where T: Digit
    {
        let nnum = self.nr_digits();
        let nden = other.nr_digits();

        if nnum < nden
        {
            let rem = std::mem::replace(&mut self.digits, vec![]);
            Ok(Self::new(rem))
        }
        else
        {
            let mut rem = std::mem::replace(&mut self.digits, vec![T::zero(); nnum-nden+1]);
            let (nquot, nrem) = crate::ubig::div::div_big(&mut rem, &other.digits, &mut self.digits)?;
            self.digits.truncate(nquot);
            rem.truncate(nrem);
            Ok(Self::new(rem))
        }
    }

    /// Divide this number by `other` and store the remainder in `self`. If `other` is zero,
    /// a `DivisionByZero` error is returned.
    pub fn rem_assign_big(&mut self, other: &Self) -> Result<()>
    where T: Digit
    {
        let nnum = self.nr_digits();
        let nden = other.nr_digits();
        if nnum >= nden
        {
            let mut quot = vec![T::zero(); nnum-nden+1];
            let (_, nrem) = crate::ubig::div::div_big(&mut self.digits, &other.digits, &mut quot)?;
            self.digits.truncate(nrem);
        }
        Ok(())
    }
}

impl<T> UBig<BinaryDigit<T>>
{
    /// Convert this binary big number to decimal form.
    pub fn to_decimal(&self) -> UBig<DecimalDigit<T>>
    where T: DigitStorage, DecimalDigit<T>: Digit
    {
        match self.nr_digits()
        {
            0|1 => Self::build_decimal(&self.digits, &[]),
            n   => {
                let half_nr_bits = BinaryDigit::<T>::NR_BITS / 2;
                let pow_max = 8 * std::mem::size_of::<usize>() as u32 - n.leading_zeros() - 1;
                let mut scale = (UBig::one() << half_nr_bits) << half_nr_bits;
                let mut scales = vec![];
                for _ in 0..pow_max-1
                {
                    let scale_sq = scale.square();
                    scales.push(scale);
                    scale = scale_sq;
                }
                scales.push(scale);
                Self::build_decimal(&self.digits, &scales)
            }
        }
    }

    /// Convert the binary big number represented by digits `digits` to decimal form. Array
    /// `scales` contains successive squares of the radix of the binary number, expressed in
    /// decimal digits.
    fn build_decimal(digits: &[BinaryDigit<T>], scales: &[UBig<DecimalDigit<T>>]) -> UBig<DecimalDigit<T>>
    where T: DigitStorage, DecimalDigit<T>: Digit
    {
        match digits.len()
        {
            0 => UBig::zero(),
            1 => UBig::<DecimalDigit<T>>::from(digits[0].0),
            n => {
                let mut pow_idx = 8 * std::mem::size_of::<usize>() - n.leading_zeros() as usize - 2;
                let mut split = 1 << pow_idx;
                if 3*split > 2*n
                {
                    pow_idx -= 1;
                    split >>= 1;
                }
                let nlow = support::drop_leading_zeros(digits, split);
                let low = Self::build_decimal(&digits[..nlow], scales);
                let high = Self::build_decimal(&digits[split..], scales);
                high * &scales[pow_idx] + low
            }
        }
    }
}

impl<T> Zero for UBig<T>
where T: Digit
{
    fn zero() -> Self
    {
        UBig { digits: vec![] }
    }

    fn is_zero(&self) -> bool
    {
        self.digits.is_empty()
    }
}

impl<T> One for UBig<T>
where T: Digit
{
    fn one() -> Self
    {
        UBig { digits: vec![T::one()] }
    }
}

impl<T> From<T> for UBig<BinaryDigit<T>>
where T: Zero, BinaryDigit<T>: Digit
{
    fn from(n: T) -> Self
    {
        if n.is_zero()
        {
            UBig::zero()
        }
        else
        {
            UBig { digits: vec![BinaryDigit(n)] }
        }
    }
}

impl<T> From<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn from(n: T) -> Self
    {
        if n.is_zero()
        {
            UBig::zero()
        }
        else if DecimalDigit::fits_single(n)
        {
            UBig { digits: vec![DecimalDigit(n)] }
        }
        else
        {
            let (high, low) = DecimalDigit::split(n);
            UBig { digits: vec![low, high] }
        }
    }
}

impl<T> std::str::FromStr for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Self>
    {
        if !s.is_ascii()
        {
            Err(Error::InvalidNumber)
        }
        else if let Some(s) = s.strip_prefix("0x")
        {
            let mut digits = Vec::with_capacity(s.len() / BinaryDigit::<T>::NR_HEX_PLACES + 1);
            for part in s.as_bytes().rchunks(BinaryDigit::<T>::NR_HEX_PLACES)
            {
                let digit = BinaryDigit::<T>::from_hexadecimal_str(std::str::from_utf8(part).unwrap())?;
                digits.push(digit);
            }
            Ok(UBig::new(digits))
        }
        else
        {
            // FIXME: this could probably be done more efficiently then one digit at a time.
            let ten = (T::one() << 3) + (T::one() << 1);
            let scale = BinaryDigit(ten.pow(BinaryDigit::<T>::MAX_DECIMAL_PLACES));
            let mut result = Self::zero();
            for part in s.as_bytes().rchunks(BinaryDigit::<T>::MAX_DECIMAL_PLACES).rev()
            {
                let digit = BinaryDigit::<T>::from_decimal_str(std::str::from_utf8(part).unwrap())?;
                result.mul_add_assign_digit(scale, digit);
            }
            Ok(result)
        }
    }
}

impl<T> std::str::FromStr for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Self>
    {
        if !s.is_ascii()
        {
            Err(Error::InvalidNumber)
        }
        else if let Some(s) = s.strip_prefix("0x")
        {
            // FIXME: this could probably be done more efficiently then one digit at a time.
            let scale = DecimalDigit(T::one() << (4 * DecimalDigit::<T>::MAX_HEX_PLACES));
            let mut result = Self::zero();
            for part in s.as_bytes().rchunks(DecimalDigit::<T>::MAX_HEX_PLACES).rev()
            {
                let digit = DecimalDigit::<T>::from_hexadecimal_str(std::str::from_utf8(part).unwrap())?;
                result.mul_add_assign_digit(scale, digit);
            }
            Ok(result)
        }
        else
        {
            let mut digits = Vec::with_capacity(s.len() / DecimalDigit::<T>::NR_DECIMAL_PLACES + 1);
            for part in s.as_bytes().rchunks(DecimalDigit::<T>::NR_DECIMAL_PLACES)
            {
                let digit = DecimalDigit::<T>::from_decimal_str(std::str::from_utf8(part).unwrap())?;
                digits.push(digit);
            }
            Ok(UBig::new(digits))
        }
    }
}

impl<T> std::fmt::LowerHex for UBig<BinaryDigit<T>>
where T: DigitStorage + std::fmt::LowerHex
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        match self.nr_digits()
        {
            0 => { T::zero().fmt(f) },
            1 => { self.digits[0].0.fmt(f) },
            n => {
                let mut s = String::with_capacity(n * BinaryDigit::<T>::NR_HEX_PLACES);
                write!(s, "{:x}", self.digits.last().unwrap().0)?;
                for d in self.digits.iter().rev().skip(1)
                {
                    write!(s, "{:0width$x}", d.0, width=BinaryDigit::<T>::NR_HEX_PLACES)?;
                }
                f.pad_integral(true, "0x", &s)
            }
        }
    }
}

impl<T> std::fmt::UpperHex for UBig<BinaryDigit<T>>
where T: DigitStorage + std::fmt::UpperHex
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        match self.nr_digits()
        {
            0 => { T::zero().fmt(f) },
            1 => { self.digits[0].0.fmt(f) },
            n => {
                let mut s = String::with_capacity(n * BinaryDigit::<T>::NR_HEX_PLACES);
                write!(s, "{:X}", self.digits.last().unwrap().0)?;
                for d in self.digits.iter().rev().skip(1)
                {
                    write!(s, "{:0width$X}", d.0, width=BinaryDigit::<T>::NR_HEX_PLACES)?;
                }
                f.pad_integral(true, "0x", &s)
            }
        }
    }
}

impl<T> std::fmt::Display for UBig<BinaryDigit<T>>
where T: DigitStorage + std::fmt::Display, DecimalDigit<T>: Digit
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        self.to_decimal().fmt(f)
    }
}

impl<T> std::fmt::Display for UBig<DecimalDigit<T>>
where T: DigitStorage + std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        match self.nr_digits()
        {
            0 => { T::zero().fmt(f) },
            1 => { self.digits[0].0.fmt(f) },
            n => {
                let mut s = String::with_capacity(n * DecimalDigit::<T>::NR_DECIMAL_PLACES);
                write!(s, "{}", self.digits.last().unwrap().0)?;
                for d in self.digits.iter().rev().skip(1)
                {
                    write!(s, "{:0width$}", d.0, width=DecimalDigit::<T>::NR_DECIMAL_PLACES)?;
                }
                f.pad_integral(true, "", &s)
            }
        }
    }
}

impl<T> PartialOrd for UBig<T>
where T: Eq + Ord
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering>
    {
        Some(self.cmp(other))
    }
}

impl<T> Ord for UBig<T>
where T: Eq + Ord
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering
    {
        cmp::cmp(&self.digits, &other.digits)
    }
}

#[cfg(test)]
mod test
{
    use super::{Error, UBig};
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::{Zero, One};

    #[test]
    fn test_new()
    {
        let digits = vec![DecimalDigit(1u32), DecimalDigit(2)];
        let n = UBig::new(digits);
        assert_eq!(n.digits(), &[DecimalDigit(1), DecimalDigit(2)]);

        let digits = vec![DecimalDigit(1u8), DecimalDigit(2), DecimalDigit(0)];
        let n = UBig::new(digits);
        assert_eq!(n.digits(), &[DecimalDigit(1), DecimalDigit(2)]);

        let digits = vec![BinaryDigit(1u8), BinaryDigit(2), BinaryDigit(0), BinaryDigit(3)];
        let n = UBig::new(digits);
        assert_eq!(n.digits(), &[BinaryDigit(1), BinaryDigit(2), BinaryDigit(0), BinaryDigit(3)]);

        let digits = vec![BinaryDigit(1u8), BinaryDigit(2), BinaryDigit(0), BinaryDigit(0)];
        let n = UBig::new(digits);
        assert_eq!(n.digits(), &[BinaryDigit(1), BinaryDigit(2)]);

        let digits = vec![DecimalDigit(0u8), DecimalDigit(2), DecimalDigit(0)];
        let n = UBig::new(digits);
        assert_eq!(n.digits(), &[DecimalDigit(0), DecimalDigit(2)]);
    }

    #[test]
    fn test_zero()
    {
        let n = UBig::<BinaryDigit<u32>>::zero();
        assert_eq!(n.digits(), &[]);

        let n = UBig::<DecimalDigit<u8>>::zero();
        assert_eq!(n.digits(), &[]);
    }

    #[test]
    fn test_is_zero()
    {
        let digits: Vec<DecimalDigit<u32>> = vec![];
        let n = UBig { digits };
        assert!(n.is_zero());

        let digits: Vec<DecimalDigit<u8>> = vec![DecimalDigit(12), DecimalDigit(16)];
        let n = UBig { digits };
        assert!(!n.is_zero());

        let n = UBig::<BinaryDigit<u16>>::zero();
        assert!(n.is_zero());
    }

    #[test]
    fn test_one()
    {
        let n = UBig::<BinaryDigit<u32>>::one();
        assert_eq!(n.digits(), &[BinaryDigit(1)]);

        let n = UBig::<DecimalDigit<u8>>::one();
        assert_eq!(n.digits(), &[DecimalDigit(1)]);
    }

    #[test]
    fn test_from_digit_binary()
    {
        let n = UBig::<BinaryDigit<u8>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<BinaryDigit<u8>>::from(0x7f);
        assert_eq!(n.digits(), &[BinaryDigit(0x7f)]);

        let n = UBig::<BinaryDigit<u16>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<BinaryDigit<u16>>::from(0xf37f);
        assert_eq!(n.digits(), &[BinaryDigit(0xf37f)]);

        let n = UBig::<BinaryDigit<u32>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<BinaryDigit<u32>>::from(0x12345678);
        assert_eq!(n.digits(), &[BinaryDigit(0x12345678)]);
    }

    #[test]
    fn test_from_digit_decimal()
    {
        let n = UBig::<DecimalDigit<u8>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<DecimalDigit<u8>>::from(57);
        assert_eq!(n.digits(), &[DecimalDigit(57)]);

        let n = UBig::<DecimalDigit<u8>>::from(204);
        assert_eq!(n.digits(), &[DecimalDigit(4), DecimalDigit(2)]);

        let n = UBig::<DecimalDigit<u16>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<DecimalDigit<u16>>::from(7_352);
        assert_eq!(n.digits(), &[DecimalDigit(7_352)]);

        let n = UBig::<DecimalDigit<u16>>::from(25_352);
        assert_eq!(n.digits(), &[DecimalDigit(5_352), DecimalDigit(2)]);

        let n = UBig::<DecimalDigit<u32>>::from(0);
        assert_eq!(n.digits(), &[]);

        let n = UBig::<DecimalDigit<u32>>::from(237_651_987);
        assert_eq!(n.digits(), &[DecimalDigit(237_651_987)]);

        let n = UBig::<DecimalDigit<u32>>::from(3_237_651_987);
        assert_eq!(n.digits(), &[DecimalDigit(237_651_987), DecimalDigit(3)]);
    }

    #[test]
    fn test_from_decimal_str_binary()
    {
        let res = "123456789012345678901234567890".parse::<UBig<BinaryDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0x4e3f0ad2),
            BinaryDigit(0xc373e0ee),
            BinaryDigit(0x8ee90ff6),
            BinaryDigit(0x1)
        ]);

        let res = "0000000000000000000123456789012345678901234567890".parse::<UBig<BinaryDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0x4e3f0ad2),
            BinaryDigit(0xc373e0ee),
            BinaryDigit(0x8ee90ff6),
            BinaryDigit(0x1)
        ]);

        let res = "123456789012345678901234567890".parse::<UBig<BinaryDigit<u8>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0xd2), BinaryDigit(0x0a), BinaryDigit(0x3f), BinaryDigit(0x4e),
            BinaryDigit(0xee), BinaryDigit(0xe0), BinaryDigit(0x73), BinaryDigit(0xc3),
            BinaryDigit(0xf6), BinaryDigit(0x0f), BinaryDigit(0xe9), BinaryDigit(0x8e),
            BinaryDigit(0x1)
        ]);

        let res = "123hello".parse::<UBig<DecimalDigit<u32>>>();
        assert_eq!(res, Err(Error::InvalidNumber));
    }

    #[test]
    fn test_from_hex_str_binary()
    {
        let res = "0x123456789012345678901234567890".parse::<UBig<BinaryDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0x34567890),
            BinaryDigit(0x56789012),
            BinaryDigit(0x78901234),
            BinaryDigit(0x123456)
        ]);

        let res = "0x0000000000000000000123456789012345678901234567890".parse::<UBig<BinaryDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0x34567890),
            BinaryDigit(0x56789012),
            BinaryDigit(0x78901234),
            BinaryDigit(0x123456)
        ]);

        let res = "0x123456789abcdeffedcba0987654321".parse::<UBig<BinaryDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            BinaryDigit(0x87654321),
            BinaryDigit(0xfedcba09),
            BinaryDigit(0x89abcdef),
            BinaryDigit(0x1234567)
        ]);

        let res = "0x123hello".parse::<UBig<BinaryDigit<u32>>>();
        assert_eq!(res, Err(Error::InvalidNumber));
    }

    #[test]
    fn test_from_decimal_str_decimal()
    {
        let res = "123456789012345678901234567890".parse::<UBig<DecimalDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(),
            &[DecimalDigit(234_567_890), DecimalDigit(345_678_901), DecimalDigit(456_789_012), DecimalDigit(123)]);

        let res = "0000000000000000000123456789012345678901234567890".parse::<UBig<DecimalDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(),
            &[DecimalDigit(234_567_890), DecimalDigit(345_678_901), DecimalDigit(456_789_012), DecimalDigit(123)]);

        let res = "123hello".parse::<UBig<DecimalDigit<u32>>>();
        assert_eq!(res, Err(Error::InvalidNumber));
    }

    #[test]
    fn test_from_hex_str_decimal()
    {
        let res = "0x123456789012345678901234567890".parse::<UBig<DecimalDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            DecimalDigit(743_484_560),
            DecimalDigit(552_814_062),
            DecimalDigit(687_365_475),
            DecimalDigit(945_228_79)
        ]);

        let res = "0x0000000000000000000123456789012345678901234567890".parse::<UBig<DecimalDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            DecimalDigit(743_484_560),
            DecimalDigit(552_814_062),
            DecimalDigit(687_365_475),
            DecimalDigit(945_228_79)
        ]);

        let res = "0x123456789abcdeffedcba0987654321".parse::<UBig<DecimalDigit<u32>>>();
        assert!(res.is_ok());
        assert_eq!(res.unwrap().digits(), &[
            DecimalDigit(789_144_865),
            DecimalDigit(332_354_755),
            DecimalDigit(204_170_947),
            DecimalDigit(512_366_075),
            DecimalDigit(1)
        ]);

        let res = "0x123hello".parse::<UBig<DecimalDigit<u32>>>();
        assert_eq!(res, Err(Error::InvalidNumber));
    }

    #[test]
    fn test_lowerhex_binary()
    {
        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:x}", n);
        assert_eq!(s, "0");

        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:#x}", n);
        assert_eq!(s, "0x0");

        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:#016x}", n);
        assert_eq!(s, "0x00000000000000");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:x}", n);
        assert_eq!(s, "1f2e3d4c");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:#x}", n);
        assert_eq!(s, "0x1f2e3d4c");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:#016x}", n);
        assert_eq!(s, "0x0000001f2e3d4c");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:x}", n);
        assert_eq!(s, "30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#x}", n);
        assert_eq!(s, "0x30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:16x}", n);
        assert_eq!(s, "           30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#16x}", n);
        assert_eq!(s, "         0x30201");
        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#016x}", n);
        assert_eq!(s, "0x00000000030201");
    }

    #[test]
    fn test_upperhex_binary()
    {
        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:X}", n);
        assert_eq!(s, "0");

        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:#X}", n);
        assert_eq!(s, "0x0");

        let n = UBig::<BinaryDigit<u32>>::new(vec![]);
        let s = format!("{:#016X}", n);
        assert_eq!(s, "0x00000000000000");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:X}", n);
        assert_eq!(s, "1F2E3D4C");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:#X}", n);
        assert_eq!(s, "0x1F2E3D4C");

        let n = UBig::new(vec![BinaryDigit(0x1f2e3d4cu32)]);
        let s = format!("{:#016X}", n);
        assert_eq!(s, "0x0000001F2E3D4C");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:X}", n);
        assert_eq!(s, "30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#X}", n);
        assert_eq!(s, "0x30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:16X}", n);
        assert_eq!(s, "           30201");

        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#16X}", n);
        assert_eq!(s, "         0x30201");
        let n = UBig::new(vec![BinaryDigit(0x01u8), BinaryDigit(0x02u8), BinaryDigit(0x03u8)]);
        let s = format!("{:#016X}", n);
        assert_eq!(s, "0x00000000030201");
    }

    #[test]
    fn test_display_decimal()
    {
        let n = UBig::<DecimalDigit<u32>>::new(vec![]);
        let s = format!("{}", n);
        assert_eq!(s, "0");

        let n = UBig::new(vec![DecimalDigit(123_456_789u32)]);
        let s = format!("{}", n);
        assert_eq!(s, "123456789");

        let n = UBig::new(vec![DecimalDigit(123_456_789u32), DecimalDigit(987_654_321)]);
        let s = format!("{}", n);
        assert_eq!(s, "987654321123456789");

        let n = UBig::new(vec![DecimalDigit(123u32), DecimalDigit(987_654_321)]);
        let s = format!("{}", n);
        assert_eq!(s, "987654321000000123");

        let n = UBig::new(vec![DecimalDigit(123_456_789u32), DecimalDigit(987)]);
        let s = format!("{}", n);
        assert_eq!(s, "987123456789");

        let n = UBig::new(vec![DecimalDigit(1u16), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)]);
        let s = format!("{}", n);
        assert_eq!(s, "4000300020001");

        let n = UBig::new(vec![DecimalDigit(1u16), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)]);
        let s = format!("{:020}", n);
        assert_eq!(s, "00000004000300020001");

        let n = UBig::new(vec![DecimalDigit(1u16), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)]);
        let s = format!("{:0<20}", n);
        assert_eq!(s, "40003000200010000000");

        let n = UBig::new(vec![DecimalDigit(1u16), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)]);
        let s = format!("{:0^20}", n);
        assert_eq!(s, "00040003000200010000");

        let n = UBig::new(vec![DecimalDigit(1u16)]);
        let s = format!("{:_>20}", n);
        assert_eq!(s, "___________________1");
        let n = UBig::new(vec![DecimalDigit(1u16), DecimalDigit(2), DecimalDigit(3), DecimalDigit(4)]);
        let s = format!("{:_>20}", n);
        assert_eq!(s, "_______4000300020001");
    }

    #[test]
    fn test_binary_to_decimal()
    {
        let n = UBig::<BinaryDigit<u8>>::new(vec![]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[]);

        let n = UBig::new(vec![BinaryDigit(75u8)]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[DecimalDigit(75)]);

        let n = UBig::new(vec![BinaryDigit(203u8)]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[DecimalDigit(3), DecimalDigit(2)]);

        let n = UBig::new(vec![BinaryDigit(0xacu8), BinaryDigit(0x12), BinaryDigit(0x73)]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[DecimalDigit(20), DecimalDigit(14), DecimalDigit(54), DecimalDigit(7)]);

        let n = UBig::new(vec![BinaryDigit(0x01u64), BinaryDigit(0x02), BinaryDigit(0x03)]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[
            DecimalDigit(7_017_310_442_723_737_601),
            DecimalDigit(2_084_710_076_281_539_042),
            DecimalDigit(10)
        ]);

        let n = UBig::new(vec![
            BinaryDigit(0x29afaf36281f19adu64),
            BinaryDigit(0x9fafffe73627f24d),
            BinaryDigit(0xdeeef45261ac4524)
        ]);
        let m = n.to_decimal();
        assert_eq!(m.digits(), &[
            DecimalDigit(8_816_494_390_609_385_901),
            DecimalDigit(6_506_631_539_302_871_684),
            DecimalDigit(4_663_114_439_650_396_764),
            DecimalDigit(5)
        ]);
    }
}
