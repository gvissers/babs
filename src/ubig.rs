mod add;
mod mul;

use crate::digit::{BinaryDigit, Digit, DigitStorage, DecimalDigit};
use crate::result::Error;
use num_traits::{Zero, One};
use std::fmt::Write;

/// Structure describing a big number as a series of digits. The base of the number is determined
/// by the digit type `T`. The digits are stored in little-endian order, i.e. the least significant
/// digit is the first.
#[derive(Clone, Debug, PartialEq)]
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
    pub fn drop_leading_zeros(&mut self)
    where T: Zero
    {
        while let Some(d) = self.digits.last()
        {
            if d.is_zero()
            {
                self.digits.pop();
            }
            else
            {
                break;
            }
        }
    }

    /// Multiply this number by single digit `scale`, and add digit `offset` to the result
    fn mul_add_assign_digit(&mut self, scale: T, offset: T)
    where T: Digit
    {
        if let Some(digit) = mul::mul_add_assign_digit(&mut self.digits, scale, offset)
        {
            self.digits.push(digit);
        }
    }
}

impl<T> std::str::FromStr for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err>
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

    fn from_str(s: &str) -> Result<Self, Self::Err>
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

impl<T> Zero for UBig<T>
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
where T: One
{
    fn one() -> Self
    {
        UBig { digits: vec![T::one()] }
    }
}

impl<T> std::ops::AddAssign<T> for UBig<T>
where T: Digit + One + Zero
{
    fn add_assign(&mut self, digit: T)
    {
        if let Some(carry) = add::add_assign_digit(&mut self.digits, digit)
        {
            self.digits.push(carry);
        }
    }
}

impl<T> std::ops::Add<T> for UBig<T>
where T: Clone + Digit + One + Zero
{
    type Output = Self;
    fn add(self, digit: T) -> Self::Output
    {
        &self + digit
    }
}

impl<T> std::ops::Add<T> for &UBig<T>
where T: Clone + Digit + One + Zero
{
    type Output = UBig<T>;
    fn add(self, digit: T) -> Self::Output
    {
        let mut sum = self.clone();
        sum += digit;
        sum
    }
}

impl<T> std::ops::Add<UBig<T>> for UBig<T>
{
    type Output = Self;
    fn add(self, other: UBig<T>) -> Self
    {
        unimplemented!()
    }
}

impl<T> std::ops::Mul<UBig<T>> for UBig<T>
{
    type Output = Self;
    fn mul(self, other: UBig<T>) -> Self
    {
        unimplemented!()
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
}
