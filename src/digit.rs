use crate::result::{Error, Result};

/// Trait for the underlying type of a digit
pub trait DigitStorage:
      Clone + Copy
    + num_traits::One
    + num_traits::Zero
    + num_traits::Pow<usize, Output=Self>
    + std::ops::Shl<usize, Output=Self>
{}

impl DigitStorage for u8 {}
impl DigitStorage for u16 {}
impl DigitStorage for u32 {}

/// Trait for a type that can be used as a digit in a big number
pub trait Digit:
      Clone + Copy
    + num_traits::One
    + num_traits::Zero
{
    /// The maximum value a digit can take
    const MAX: Self;

    /// Convert a string `s` describing a number in base `base` to a digit
    fn from_base_str(s: &str, base: u32) -> Result<Self>;
    /// Convert a string `s` describing a number in hexadecimal base to a digit
    fn from_hexadecimal_str(s: &str) -> Result<Self>
    {
        Self::from_base_str(s, 16)
    }
    /// Convert a string `s` describing a number in decimal base to a digit
    fn from_decimal_str(s: &str) -> Result<Self>
    {
        Self::from_base_str(s, 10)
    }

    /// Increment this number by one, wrapping around to zero on overflow. Returns `true` on
    /// overflow, `false` otherwise.
    fn inc(&mut self) -> bool;

    /// Add `other` to this digit, wrapping around to zero on overflow. Returns `true` on overflow,
    /// `false` otherwise.
    fn add_assign(&mut self, other: Self) -> bool;
    /// Multiply this digit by `fac` and add `off`. The lower part of the result is stored in `self`,
    /// the upper part is returned as carry.
    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self;
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BinaryDigit<T>(pub T);

impl<T> BinaryDigit<T>
{
    /// The size of the digit in bits
    const NR_BITS: usize = 8 * std::mem::size_of::<T>();
    /// The size of the digit in hexadecimal digits
    pub const NR_HEX_PLACES: usize = 2 * std::mem::size_of::<T>();
    /// The maximum decimal number that fits into a single digit
    pub const MAX_DECIMAL_PLACES: usize = std::mem::size_of::<T>() * 643 / 267;
}

impl Digit for BinaryDigit<u8>
{
    const MAX: Self = BinaryDigit(u8::max_value());

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u8::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        Ok(BinaryDigit(d))
    }

    fn inc(&mut self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(1);
        self.0 = n;
        overflow
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(other.0);
        self.0 = n;
        overflow
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u16 * fac.0 as u16 + off.0 as u16;
        self.0 = (tmp & Self::MAX.0 as u16) as u8;
        BinaryDigit((tmp >> Self::NR_BITS) as u8)
    }
}

impl Digit for BinaryDigit<u16>
{
    const MAX: Self = BinaryDigit(u16::max_value());

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u16::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        Ok(BinaryDigit(d))
    }

    fn inc(&mut self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(1);
        self.0 = n;
        overflow
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(other.0);
        self.0 = n;
        overflow
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u32 * fac.0 as u32 + off.0 as u32;
        self.0 = (tmp & Self::MAX.0 as u32) as u16;
        BinaryDigit((tmp >> Self::NR_BITS) as u16)
    }
}

impl Digit for BinaryDigit<u32>
{
    const MAX: Self = BinaryDigit(u32::max_value());

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u32::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        Ok(BinaryDigit(d))
    }

    fn inc(&mut self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(1);
        self.0 = n;
        overflow
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        let (n, overflow) = self.0.overflowing_add(other.0);
        self.0 = n;
        overflow
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u64 * fac.0 as u64 + off.0 as u64;
        self.0 = (tmp & Self::MAX.0 as u64) as u32;
        BinaryDigit((tmp >> Self::NR_BITS) as u32)
    }
}

impl<T> num_traits::Zero for BinaryDigit<T>
where T: num_traits::Zero
{
    fn zero() -> Self
    {
        BinaryDigit(T::zero())
    }

    fn is_zero(&self) -> bool
    {
        self.0.is_zero()
    }
}

impl<T> num_traits::One for BinaryDigit<T>
where T: num_traits::One
{
    fn one() -> Self
    {
        BinaryDigit(T::one())
    }
}

impl<T> std::ops::Add for BinaryDigit<T>
where T: std::ops::Add<Output=T>
{
    type Output = Self;
    fn add(self, other: Self) -> Self::Output
    {
        BinaryDigit(self.0 + other.0)
    }
}

impl<T> std::ops::Mul for BinaryDigit<T>
where T: std::ops::Mul<Output=T>
{
    type Output = Self;
    fn mul(self, other: Self) -> Self::Output
    {
        BinaryDigit(self.0 * other.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct DecimalDigit<T>(pub T);

impl<T> DecimalDigit<T>
where T: DigitStorage
{
    /// The maximum number of decimal places used to denote a single digit
    pub const NR_DECIMAL_PLACES: usize = std::mem::size_of::<T>() * 643 / 267;
    /// The maximum length of a hexadecimal number that still fits in a single digit
    pub const MAX_HEX_PLACES: usize = 2 * std::mem::size_of::<T>() - 1;
}

impl DecimalDigit<u8>
{
    const RADIX: u8 = 10u8.pow(Self::NR_DECIMAL_PLACES as u32);
}

impl DecimalDigit<u16>
{
    const RADIX: u16 = 10u16.pow(Self::NR_DECIMAL_PLACES as u32);
}

impl DecimalDigit<u32>
{
    const RADIX: u32 = 10u32.pow(Self::NR_DECIMAL_PLACES as u32);
}

impl Digit for DecimalDigit<u8>
{
    const MAX: Self = DecimalDigit(Self::RADIX - 1);

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u8::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        if d < Self::RADIX
        {
            Ok(DecimalDigit(d))
        }
        else
        {
            Err(Error::InvalidNumber)
        }
    }

    fn inc(&mut self) -> bool
    {
        if *self == Self::MAX
        {
            self.0 = 0;
            true
        }
        else
        {
            self.0 += 1;
            false
        }
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        self.0 += other.0;
        if self.0 >= Self::RADIX
        {
            self.0 -= Self::RADIX;
            true
        }
        else
        {
            false
        }
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u16 * fac.0 as u16 + off.0 as u16;
        self.0 = (tmp % Self::RADIX as u16) as u8;
        DecimalDigit((tmp / Self::RADIX as u16) as u8)
    }
}

impl Digit for DecimalDigit<u16>
{
    const MAX: Self = DecimalDigit(Self::RADIX - 1);

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u16::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        if d < Self::RADIX
        {
            Ok(DecimalDigit(d))
        }
        else
        {
            Err(Error::InvalidNumber)
        }
    }

    fn inc(&mut self) -> bool
    {
        if *self == Self::MAX
        {
            self.0 = 0;
            true
        }
        else
        {
            self.0 += 1;
            false
        }
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        self.0 += other.0;
        if self.0 >= Self::RADIX
        {
            self.0 -= Self::RADIX;
            true
        }
        else
        {
            false
        }
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u32 * fac.0 as u32 + off.0 as u32;
        self.0 = (tmp % Self::RADIX as u32) as u16;
        DecimalDigit((tmp / Self::RADIX as u32) as u16)
    }
}

impl Digit for DecimalDigit<u32>
{
    const MAX: Self = DecimalDigit(Self::RADIX - 1);

    fn from_base_str(s: &str, base: u32) -> Result<Self>
    {
        let d = u32::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
        if d < Self::RADIX
        {
            Ok(DecimalDigit(d))
        }
        else
        {
            Err(Error::InvalidNumber)
        }
    }

    fn inc(&mut self) -> bool
    {
        if *self == Self::MAX
        {
            self.0 = 0;
            true
        }
        else
        {
            self.0 += 1;
            false
        }
    }

    fn add_assign(&mut self, other: Self) -> bool
    {
        self.0 += other.0;
        if self.0 >= Self::RADIX
        {
            self.0 -= Self::RADIX;
            true
        }
        else
        {
            false
        }
    }

    fn mul_add_assign(&mut self, fac: Self, off: Self) -> Self
    {
        let tmp = self.0 as u64 * fac.0 as u64 + off.0 as u64;
        self.0 = (tmp % Self::RADIX as u64) as u32;
        DecimalDigit((tmp / Self::RADIX as u64) as u32)
    }
}

impl<T> num_traits::Zero for DecimalDigit<T>
where T: num_traits::Zero
{
    fn zero() -> Self
    {
        DecimalDigit(T::zero())
    }

    fn is_zero(&self) -> bool
    {
        self.0.is_zero()
    }
}

impl<T> num_traits::One for DecimalDigit<T>
where T: num_traits::One
{
    fn one() -> Self
    {
        DecimalDigit(T::one())
    }
}

impl<T> std::ops::Add for DecimalDigit<T>
where T: std::ops::Add<Output=T>
{
    type Output = Self;
    fn add(self, other: Self) -> Self::Output
    {
        DecimalDigit(self.0 + other.0)
    }
}

impl<T> std::ops::Mul for DecimalDigit<T>
where T: std::ops::Mul<Output=T>
{
    type Output = Self;
    fn mul(self, other: Self) -> Self::Output
    {
        DecimalDigit(self.0 * other.0)
    }
}

#[cfg(test)]
mod tests
{
    use super::{BinaryDigit, DecimalDigit, Digit};

    #[test]
    fn test_inc_binary()
    {
        let mut d = BinaryDigit(0u8);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(1));

        let mut d = BinaryDigit(0xfeu8);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0xffu8);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0xffu16);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0x100));

        let mut d = BinaryDigit(0xffffu16);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0xfffffu32);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0x100000));

        let mut d = BinaryDigit(0xffffffffu32);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));
    }

    #[test]
    fn test_inc_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(1));

        let mut d = DecimalDigit(98u8);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(99u8);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(99u16);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(100));

        let mut d = DecimalDigit(9_999u16);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(99_999_999u32);
        let overflow = d.inc();
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(100_000_000));

        let mut d = DecimalDigit(999_999_999u32);
        let overflow = d.inc();
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));
    }

    #[test]
    fn test_add_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let overflow = d.add_assign(BinaryDigit(47));
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(47));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_assign(BinaryDigit(0x7f));
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_assign(BinaryDigit(0x80));
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_assign(BinaryDigit(0x85));
        assert!(overflow);
        assert_eq!(d, BinaryDigit(5));

        let mut d = BinaryDigit(0x80u16);
        let overflow = d.add_assign(BinaryDigit(0xff00));
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff80));

        let mut d = BinaryDigit(0x8000u16);
        let overflow = d.add_assign(BinaryDigit(0xff00));
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x7f00));

        let mut d = BinaryDigit(0x80u32);
        let overflow = d.add_assign(BinaryDigit(0xff001100));
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff001180));

        let mut d = BinaryDigit(0x80001234u32);
        let overflow = d.add_assign(BinaryDigit(0xffab1234));
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x7fab2468));
    }

    #[test]
    fn test_add_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let overflow = d.add_assign(DecimalDigit(47));
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(47));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_assign(DecimalDigit(49));
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_assign(DecimalDigit(50));
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_assign(DecimalDigit(55));
        assert!(overflow);
        assert_eq!(d, DecimalDigit(5));

        let mut d = DecimalDigit(50u16);
        let overflow = d.add_assign(DecimalDigit(9_900));
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(9_950));

        let mut d = DecimalDigit(5000u16);
        let overflow = d.add_assign(DecimalDigit(9_900));
        assert!(overflow);
        assert_eq!(d, DecimalDigit(4_900));

        let mut d = DecimalDigit(50u32);
        let overflow = d.add_assign(DecimalDigit(999_001_100));
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(999_001_150));

        let mut d = DecimalDigit(1_001_234u32);
        let overflow = d.add_assign(DecimalDigit(999_781_234));
        assert!(overflow);
        assert_eq!(d, DecimalDigit(782_468));
    }

    #[test]
    fn test_mul_add_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let carry = d.mul_add_assign(BinaryDigit(0x47), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13u8);
        let carry = d.mul_add_assign(BinaryDigit(0), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13u8);
        let carry = d.mul_add_assign(BinaryDigit(0x47), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0x44));
        assert_eq!(carry, BinaryDigit(0x06));

        let mut d = BinaryDigit(0xffu8);
        let carry = d.mul_add_assign(BinaryDigit(0xff), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xff));

        let mut d = BinaryDigit(0u16);
        let carry = d.mul_add_assign(BinaryDigit(0x472a), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0xffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2u16);
        let carry = d.mul_add_assign(BinaryDigit(0), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0xffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2u16);
        let carry = d.mul_add_assign(BinaryDigit(0x472a), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0x63b3));
        assert_eq!(carry, BinaryDigit(0x058c));

        let mut d = BinaryDigit(0xffffu16);
        let carry = d.mul_add_assign(BinaryDigit(0xffff), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xffff));

        let mut d = BinaryDigit(0u32);
        let carry = d.mul_add_assign(BinaryDigit(0x472a16ff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0xffffffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2aa87u32);
        let carry = d.mul_add_assign(BinaryDigit(0), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0xffffffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2aa87u32);
        let carry = d.mul_add_assign(BinaryDigit(0x472a16ff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0x24857678));
        assert_eq!(carry, BinaryDigit(0x058b94e7));

        let mut d = BinaryDigit(0xffffffffu32);
        let carry = d.mul_add_assign(BinaryDigit(0xffffffff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xffffffff));
    }

    #[test]
    fn test_mul_add_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let carry = d.mul_add_assign(DecimalDigit(47), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13u8);
        let carry = d.mul_add_assign(DecimalDigit(0), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13u8);
        let carry = d.mul_add_assign(DecimalDigit(47), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(10));
        assert_eq!(carry, DecimalDigit(7));

        let mut d = DecimalDigit(99u8);
        let carry = d.mul_add_assign(DecimalDigit(99), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(99));

        let mut d = DecimalDigit(0u16);
        let carry = d.mul_add_assign(DecimalDigit(4_729), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(9_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(1_392u16);
        let carry = d.mul_add_assign(DecimalDigit(0), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(9_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(1392u16);
        let carry = d.mul_add_assign(DecimalDigit(4_729), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(2_767));
        assert_eq!(carry, DecimalDigit(659));

        let mut d = DecimalDigit(9_999u16);
        let carry = d.mul_add_assign(DecimalDigit(9_999), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(9_999));

        let mut d = DecimalDigit(0u32);
        let carry = d.mul_add_assign(DecimalDigit(647_211_698), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(999_999_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13_921_887u32);
        let carry = d.mul_add_assign(DecimalDigit(0), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(999_999_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13_921_887u32);
        let carry = d.mul_add_assign(DecimalDigit(647_211_698), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(124_634_125));
        assert_eq!(carry, DecimalDigit(9_010_409));

        let mut d = DecimalDigit(999_999_999u32);
        let carry = d.mul_add_assign(DecimalDigit(999_999_999), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(999_999_999));
    }
}
