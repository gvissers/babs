use crate::result::{Error, Result};

/// Trait for the underlying type of a digit
pub trait DigitStorage:
      Clone + Copy + Eq + Ord
    + num_traits::One
    + num_traits::Zero
    + num_traits::Pow<usize, Output=Self>
    + std::ops::Div<Output=Self>
    + std::ops::Rem<Output=Self>
    + std::ops::Sub<Output=Self>
    + std::ops::Shl<usize, Output=Self>
{
    const DECIMAL_RADIX: Self;
}

impl DigitStorage for u8
{
    const DECIMAL_RADIX: Self = 100;
}
impl DigitStorage for u16
{
    const DECIMAL_RADIX: Self = 10_000;
}
impl DigitStorage for u32
{
    const DECIMAL_RADIX: Self = 1_000_000_000;
}

/// Trait for a type that can be used as a digit in a big number
pub trait Digit:
      Clone + Copy + Eq + Ord
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

    /// Return the maximum number of places this digit can be shifted left before it overflows its base
    fn max_shift(&self) -> u32;

    /// Increment this number by one, wrapping around to zero on overflow. Returns `true` on
    /// overflow, `false` otherwise.
    fn inc(&mut self) -> bool;
    /// Decrement this number by one, wrapping around to zero on underflow. Returns `true` on
    /// underflow, `false` otherwise.
    fn dec(&mut self) -> bool;

    /// Add `other` + `carry` to this digit, wrapping around to zero on overflow. Returns `true`
    /// on overflow, `false` otherwise.
    fn add_carry_assign(&mut self, other: Self, carry: bool) -> bool;
    /// Subtract `other` + `carry` from this digit, wrapping around to zero on underflow. Returns
    /// `true` on underflow, `false` otherwise.
    fn sub_carry_assign(&mut self, other: Self, carry: bool) -> bool;

    /// Shift this digit left by `shift` bits, and add `carry` to the result. The carry `carry` must
    /// fit in  `shift` bits, which in turn must be smaller than the bit width of the digit, i.e.
    /// `carry` < 2<sup>`shift`</sup> < `b`, where `b` is the base of the digit. Returns the new
    /// carry after the left shift.
    fn shl_carry_assign(&mut self, shift: usize, carry: Self) -> Self;
    /// Shift this digit right by `shift` bits, and add `b*carry` to the result, where `b` is the
    /// base of the digit. The carry `carry` must fit in  `shift` bits, which in turn must be
    /// smaller than the bit width of the digit, i.e. `carry` < 2<sup>`shift`</sup> < `b`. Returns
    /// the new carry after the right shift.
    fn shr_carry_assign(&mut self, shift: usize, carry: Self) -> Self;

    /// Multiply this digit by `fac` and add `carry`. The lower part of the result is stored in
    /// `self`, the upper part is returned as carry.
    fn mul_carry_assign(&mut self, fac: Self, carry: Self) -> Self;
    /// Divide `carry`*`b` + this digit by `fac`, where `b` is the base of this digit, and store the
    /// result back into this digit . The remainder of the division is returned as carry. The
    /// divisor `fac` should not be zero, and the `carry` should be less than the divisor, i.e.
    /// `0 <= carry < fac`.
    fn div_carry_assign(&mut self, fac: Self, carry: Self) -> Self;

    /// Add the product of `fac0` and `fac1`, as well as the carry `carry` to this digit, and
    /// return the new carry.
    fn add_prod_carry_assign(&mut self, fac0: Self, fac1: Self, carry: Self) -> Self;
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BinaryDigit<T>(pub T);

impl<T> BinaryDigit<T>
{
    /// The size of the digit in bits
    pub const NR_BITS: usize = 8 * std::mem::size_of::<T>();
    /// The size of the digit in hexadecimal digits
    pub const NR_HEX_PLACES: usize = 2 * std::mem::size_of::<T>();
    /// The maximum decimal number that fits into a single digit
    pub const MAX_DECIMAL_PLACES: usize = std::mem::size_of::<T>() * 643 / 267;
}

macro_rules! impl_digit_binary
{
    ($dt:ty, $wdt:ty) => {
        impl Digit for BinaryDigit<$dt>
        {
            const MAX: Self = BinaryDigit(<$dt>::max_value());

            #[inline]
            fn from_base_str(s: &str, base: u32) -> Result<Self>
            {
                let d = <$dt>::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
                Ok(BinaryDigit(d))
            }

            #[inline]
            fn max_shift(&self) -> u32
            {
                self.0.leading_zeros()
            }

            #[inline]
            fn inc(&mut self) -> bool
            {
                let (n, overflow) = self.0.overflowing_add(1);
                self.0 = n;
                overflow
            }

            #[inline]
            fn dec(&mut self) -> bool
            {
                let (n, underflow) = self.0.overflowing_sub(1);
                self.0 = n;
                underflow
            }

            #[inline]
            fn add_carry_assign(&mut self, other: Self, carry: bool) -> bool
            {
                let (n, overflow0) = self.0.overflowing_add(other.0);
                let (n, overflow1) = n.overflowing_add(carry as $dt);
                self.0 = n;
                overflow0 || overflow1
            }

            #[inline]
            fn sub_carry_assign(&mut self, other: Self, carry: bool) -> bool
            {
                let (n, underflow0) = self.0.overflowing_sub(other.0);
                let (n, underflow1) = n.overflowing_sub(carry as $dt);
                self.0 = n;
                underflow0 || underflow1
            }

            #[inline]
            fn shl_carry_assign(&mut self, shift: usize, carry: Self) -> Self
            {
                let new_carry = self.0 >> (Self::NR_BITS - shift);
                self.0 = (self.0 << shift) | carry.0;
                BinaryDigit(new_carry)
            }

            #[inline]
            fn shr_carry_assign(&mut self, shift: usize, carry: Self) -> Self
            {
                let mask = (1 << (shift - 1)) | ((1 << (shift - 1)) - 1);
                let new_carry = self.0 & mask;
                self.0 = (carry.0 << Self::NR_BITS - shift) | (self.0 >> shift);
                BinaryDigit(new_carry)
            }

            #[inline]
            fn mul_carry_assign(&mut self, fac: Self, carry: Self) -> Self
            {
                let tmp = self.0 as $wdt * fac.0 as $wdt + carry.0 as $wdt;
                self.0 = (tmp & Self::MAX.0 as $wdt) as $dt;
                BinaryDigit((tmp >> Self::NR_BITS) as $dt)
            }

            #[inline]
            fn div_carry_assign(&mut self, fac: Self, carry: Self) -> Self
            {
                let tmp = (carry.0 as $wdt << Self::NR_BITS) | self.0 as $wdt;
                self.0 = (tmp / fac.0 as $wdt) as $dt;
                BinaryDigit((tmp % fac.0 as $wdt) as $dt)
            }

            #[inline]
            fn add_prod_carry_assign(&mut self, fac0: Self, fac1: Self, carry: Self) -> Self
            {
                let tmp = self.0 as $wdt + fac0.0 as $wdt * fac1.0 as $wdt + carry.0 as $wdt;
                self.0 = (tmp & Self::MAX.0 as $wdt) as $dt;
                BinaryDigit((tmp >> Self::NR_BITS) as $dt)
            }
        }
    }
}

impl_digit_binary!(u8, u16);
impl_digit_binary!(u16, u32);
impl_digit_binary!(u32, u64);

impl<T> num_traits::Zero for BinaryDigit<T>
where T: num_traits::Zero
{
    #[inline]
    fn zero() -> Self
    {
        BinaryDigit(T::zero())
    }

    #[inline]
    fn is_zero(&self) -> bool
    {
        self.0.is_zero()
    }
}

impl<T> num_traits::One for BinaryDigit<T>
where T: num_traits::One
{
    #[inline]
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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DecimalDigit<T>(pub T);

impl<T> DecimalDigit<T>
where T: DigitStorage
{
    /// The maximum number of decimal places used to denote a single digit
    pub const NR_DECIMAL_PLACES: usize = std::mem::size_of::<T>() * 643 / 267;
    /// The maximum length of a hexadecimal number that still fits in a single digit
    pub const MAX_HEX_PLACES: usize = 2 * std::mem::size_of::<T>() - 1;

    /// Return whether a value of the underlying storage type fits into a single decimal digit
    #[inline]
    pub fn fits_single(d: T) -> bool
    {
        d < T::DECIMAL_RADIX
    }
    /// Split a value of the underlying storage type that is greater than the radix into separate digits
    #[inline]
    pub fn split(d: T) -> (Self, Self)
    {
        (DecimalDigit(d / T::DECIMAL_RADIX), DecimalDigit(d % T::DECIMAL_RADIX))
    }
}

macro_rules! impl_digit_decimal
{
    ($dt:ty, $wdt:ty) => {
        impl Digit for DecimalDigit<$dt>
        {
            const MAX: Self = DecimalDigit(<$dt>::DECIMAL_RADIX - 1);

            #[inline]
            fn from_base_str(s: &str, base: u32) -> Result<Self>
            {
                let d = <$dt>::from_str_radix(s, base).map_err(|_| Error::InvalidNumber)?;
                if d < <$dt>::DECIMAL_RADIX
                {
                    Ok(DecimalDigit(d))
                }
                else
                {
                    Err(Error::InvalidNumber)
                }
            }

            #[inline]
            fn max_shift(&self) -> u32
            {
                let shift = self.0.leading_zeros() - Self::MAX.0.leading_zeros();
                if (self.0 << shift) <= Self::MAX.0 { shift } else { shift - 1 }
            }

            #[inline]
            fn inc(&mut self) -> bool
            {
                if self.0 == <$dt>::DECIMAL_RADIX - 1
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

            #[inline]
            fn dec(&mut self) -> bool
            {
                if self.0 == 0
                {
                    self.0 = <$dt>::DECIMAL_RADIX - 1;
                    true
                }
                else
                {
                    self.0 -= 1;
                    false
                }
            }

            #[inline]
            fn add_carry_assign(&mut self, other: Self, carry: bool) -> bool
            {
                self.0 += other.0 + carry as $dt;
                if self.0 >= <$dt>::DECIMAL_RADIX
                {
                    self.0 -= <$dt>::DECIMAL_RADIX;
                    true
                }
                else
                {
                    false
                }
            }

            #[inline]
            fn sub_carry_assign(&mut self, other: Self, carry: bool) -> bool
            {
                let diff = other.0 + carry as $dt;
                if self.0 < diff
                {
                    self.0 += <$dt>::DECIMAL_RADIX - diff;
                    true
                }
                else
                {
                    self.0 -= diff;
                    false
                }
            }

            #[inline]
            fn shl_carry_assign(&mut self, shift: usize, carry: Self) -> Self
            {
                let tmp = self.0 as $wdt << shift;
                self.0 = (tmp % <$dt>::DECIMAL_RADIX as $wdt) as $dt + carry.0;
                DecimalDigit((tmp / <$dt>::DECIMAL_RADIX as $wdt) as $dt)
            }

            #[inline]
            fn shr_carry_assign(&mut self, shift: usize, carry: Self) -> Self
            {
                let mask = (1 << (shift - 1)) | ((1 << (shift - 1)) - 1);
                let tmp = carry.0 as $wdt * <$dt>::DECIMAL_RADIX as $wdt + self.0 as $wdt;
                self.0 = (tmp >> shift) as $dt;
                DecimalDigit((tmp & mask) as $dt)
            }

            #[inline]
            fn mul_carry_assign(&mut self, fac: Self, carry: Self) -> Self
            {
                let tmp = self.0 as $wdt * fac.0 as $wdt + carry.0 as $wdt;
                self.0 = (tmp % <$dt>::DECIMAL_RADIX as $wdt) as $dt;
                DecimalDigit((tmp / <$dt>::DECIMAL_RADIX as $wdt) as $dt)
            }

            #[inline]
            fn div_carry_assign(&mut self, fac: Self, carry: Self) -> Self
            {
                let tmp = carry.0 as $wdt * <$dt>::DECIMAL_RADIX as $wdt + self.0 as $wdt;
                self.0 = (tmp / fac.0 as $wdt) as $dt;
                DecimalDigit((tmp % fac.0 as $wdt) as $dt)
            }

            #[inline]
            fn add_prod_carry_assign(&mut self, fac0: Self, fac1: Self, carry: Self) -> Self
            {
                let tmp = self.0 as $wdt + fac0.0 as $wdt * fac1.0 as $wdt + carry.0 as $wdt;
                self.0 = (tmp % <$dt>::DECIMAL_RADIX as $wdt) as $dt;
                DecimalDigit((tmp / <$dt>::DECIMAL_RADIX as $wdt) as $dt)
            }
        }
    }
}

impl_digit_decimal!(u8, u16);
impl_digit_decimal!(u16, u32);
impl_digit_decimal!(u32, u64);

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
    fn test_max_shift_binary()
    {
        assert_eq!(BinaryDigit(0x0u8).max_shift(), 8);
        assert_eq!(BinaryDigit(0x1u8).max_shift(), 7);
        assert_eq!(BinaryDigit(0x80u8).max_shift(), 0);

        assert_eq!(BinaryDigit(0x0u16).max_shift(), 16);
        assert_eq!(BinaryDigit(0x70u16).max_shift(), 9);
        assert_eq!(BinaryDigit(0xe2u16).max_shift(), 8);
        assert_eq!(BinaryDigit(0x58e2u16).max_shift(), 1);
        assert_eq!(BinaryDigit(0x80e2u16).max_shift(), 0);

        assert_eq!(BinaryDigit(0x0u32).max_shift(), 32);
        assert_eq!(BinaryDigit(0x70u32).max_shift(), 25);
        assert_eq!(BinaryDigit(0x58e2u32).max_shift(), 17);
        assert_eq!(BinaryDigit(0x80e2u32).max_shift(), 16);
        assert_eq!(BinaryDigit(0x76acd561u32).max_shift(), 1);
        assert_eq!(BinaryDigit(0xffffffffu32).max_shift(), 0);
    }

    #[test]
    fn test_max_shift_decimal()
    {
        assert_eq!(DecimalDigit(0u8).max_shift(), 7);
        assert_eq!(DecimalDigit(1u8).max_shift(), 6);
        assert_eq!(DecimalDigit(49u8).max_shift(), 1);
        assert_eq!(DecimalDigit(75u8).max_shift(), 0);

        assert_eq!(DecimalDigit(0u16).max_shift(), 14);
        assert_eq!(DecimalDigit(50u16).max_shift(), 7);
        assert_eq!(DecimalDigit(2_139u16).max_shift(), 2);
        assert_eq!(DecimalDigit(7_612u16).max_shift(), 0);

        assert_eq!(DecimalDigit(0u32).max_shift(), 30);
        assert_eq!(DecimalDigit(50u32).max_shift(), 24);
        assert_eq!(DecimalDigit(2_139u32).max_shift(), 18);
        assert_eq!(DecimalDigit(7_612u32).max_shift(), 17);
        assert_eq!(DecimalDigit(213_781_923u32).max_shift(), 2);
        assert_eq!(DecimalDigit(500_000_000u32).max_shift(), 0);
    }

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
    fn test_dec_binary()
    {
        let mut d = BinaryDigit(1u8);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0xffu8);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, BinaryDigit(0xfe));

        let mut d = BinaryDigit(0u8);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0x100u16);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0u16);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, BinaryDigit(0xffff));

        let mut d = BinaryDigit(0x100000u32);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, BinaryDigit(0xfffff));

        let mut d = BinaryDigit(0u32);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, BinaryDigit(0xffffffff));
    }

    #[test]
    fn test_dec_decimal()
    {
        let mut d = DecimalDigit(1u8);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(99u8);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, DecimalDigit(98));

        let mut d = DecimalDigit(0u8);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(100u16);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(0u16);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, DecimalDigit(9_999));

        let mut d = DecimalDigit(100_000_000u32);
        let underflow = d.dec();
        assert!(!underflow);
        assert_eq!(d, DecimalDigit(99_999_999));

        let mut d = DecimalDigit(0u32);
        let underflow = d.dec();
        assert!(underflow);
        assert_eq!(d, DecimalDigit(999_999_999));
    }

    #[test]
    fn test_add_carry_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let overflow = d.add_carry_assign(BinaryDigit(47), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(47));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_carry_assign(BinaryDigit(0x7f), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_carry_assign(BinaryDigit(0x7f), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_carry_assign(BinaryDigit(0x80), false);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.add_carry_assign(BinaryDigit(0x85), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(6));

        let mut d = BinaryDigit(0x80u16);
        let overflow = d.add_carry_assign(BinaryDigit(0xff00), true);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff81));

        let mut d = BinaryDigit(0x8000u16);
        let overflow = d.add_carry_assign(BinaryDigit(0xff00), false);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x7f00));

        let mut d = BinaryDigit(0x80u32);
        let overflow = d.add_carry_assign(BinaryDigit(0xff001100), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xff001180));

        let mut d = BinaryDigit(0x80001234u32);
        let overflow = d.add_carry_assign(BinaryDigit(0xffab1234), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x7fab2469));
    }

    #[test]
    fn test_add_carry_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let overflow = d.add_carry_assign(DecimalDigit(47), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(47));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_carry_assign(DecimalDigit(49), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_carry_assign(DecimalDigit(49), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_carry_assign(DecimalDigit(50), false);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(0));

        let mut d = DecimalDigit(50u8);
        let overflow = d.add_carry_assign(DecimalDigit(55), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(6));

        let mut d = DecimalDigit(50u16);
        let overflow = d.add_carry_assign(DecimalDigit(9_900), true);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(9_951));

        let mut d = DecimalDigit(5000u16);
        let overflow = d.add_carry_assign(DecimalDigit(9_900), false);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(4_900));

        let mut d = DecimalDigit(50u32);
        let overflow = d.add_carry_assign(DecimalDigit(999_001_100), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(999_001_150));

        let mut d = DecimalDigit(1_001_234u32);
        let overflow = d.add_carry_assign(DecimalDigit(999_781_234), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(782_469));
    }

    #[test]
    fn test_sub_carry_assign_binary()
    {
        let mut d = BinaryDigit(47u8);
        let overflow = d.sub_carry_assign(BinaryDigit(0), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(47));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.sub_carry_assign(BinaryDigit(0x7f), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(1));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.sub_carry_assign(BinaryDigit(0x7f), true);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.sub_carry_assign(BinaryDigit(0x80), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0x7fu8);
        let overflow = d.sub_carry_assign(BinaryDigit(0x80), false);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0xff));

        let mut d = BinaryDigit(0x80u8);
        let overflow = d.sub_carry_assign(BinaryDigit(0x85), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0xfa));

        let mut d = BinaryDigit(0xff00u16);
        let overflow = d.sub_carry_assign(BinaryDigit(0x80), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0xfe80));

        let mut d = BinaryDigit(0x8000u16);
        let overflow = d.sub_carry_assign(BinaryDigit(0xff00), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x80ff));

        let mut d = BinaryDigit(0xff001180u32);
        let overflow = d.sub_carry_assign(BinaryDigit(0xff001100), false);
        assert!(!overflow);
        assert_eq!(d, BinaryDigit(0x80));

        let mut d = BinaryDigit(0x7fab2468u32);
        let overflow = d.sub_carry_assign(BinaryDigit(0xffab1234), true);
        assert!(overflow);
        assert_eq!(d, BinaryDigit(0x80001233));
    }

    #[test]
    fn test_sub_carry_assign_decimal()
    {
        let mut d = DecimalDigit(47u8);
        let overflow = d.sub_carry_assign(DecimalDigit(0), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(47));

        let mut d = DecimalDigit(99u8);
        let overflow = d.sub_carry_assign(DecimalDigit(49), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(50));

        let mut d = DecimalDigit(99u8);
        let overflow = d.sub_carry_assign(DecimalDigit(99), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(99));

        let mut d = DecimalDigit(0u8);
        let overflow = d.sub_carry_assign(DecimalDigit(50), false);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(50));

        let mut d = DecimalDigit(5u8);
        let overflow = d.sub_carry_assign(DecimalDigit(55), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(49));

        let mut d = DecimalDigit(9_950u16);
        let overflow = d.sub_carry_assign(DecimalDigit(9_900), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(50));

        let mut d = DecimalDigit(4_900u16);
        let overflow = d.sub_carry_assign(DecimalDigit(9_900), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(4_999));

        let mut d = DecimalDigit(999_001_150u32);
        let overflow = d.sub_carry_assign(DecimalDigit(999_001_100), false);
        assert!(!overflow);
        assert_eq!(d, DecimalDigit(50));

        let mut d = DecimalDigit(782_468u32);
        let overflow = d.sub_carry_assign(DecimalDigit(999_781_234), true);
        assert!(overflow);
        assert_eq!(d, DecimalDigit(1_001_233));
    }

    #[test]
    fn test_shl_carry_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let carry = d.shl_carry_assign(5, BinaryDigit(0x10));
        assert_eq!(d, BinaryDigit(0x10));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x43u8);
        let carry = d.shl_carry_assign(5, BinaryDigit(0x10));
        assert_eq!(d, BinaryDigit(0x70));
        assert_eq!(carry, BinaryDigit(0x08));

        let mut d = BinaryDigit(0xffu8);
        let carry = d.shl_carry_assign(3, BinaryDigit(0x07));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0x07));

        let mut d = BinaryDigit(0xffu16);
        let carry = d.shl_carry_assign(3, BinaryDigit(0x07));
        assert_eq!(d, BinaryDigit(0x7ff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0xa3b4u16);
        let carry = d.shl_carry_assign(11, BinaryDigit(0x83));
        assert_eq!(d, BinaryDigit(0xa083));
        assert_eq!(carry, BinaryDigit(0x051d));

        let mut d = BinaryDigit(0xa3b4u32);
        let carry = d.shl_carry_assign(11, BinaryDigit(0x83));
        assert_eq!(d, BinaryDigit(0x051da083));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x7f99a3b4u32);
        let carry = d.shl_carry_assign(21, BinaryDigit(0x21483));
        assert_eq!(d, BinaryDigit(0x76821483));
        assert_eq!(carry, BinaryDigit(0x000ff334));
    }

    #[test]
    fn test_shl_carry_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let carry = d.shl_carry_assign(5, DecimalDigit(10));
        assert_eq!(d, DecimalDigit(10));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(43u8);
        let carry = d.shl_carry_assign(5, DecimalDigit(10));
        assert_eq!(d, DecimalDigit(86));
        assert_eq!(carry, DecimalDigit(13));

        let mut d = DecimalDigit(99u8);
        let carry = d.shl_carry_assign(3, DecimalDigit(7));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(7));

        let mut d = DecimalDigit(99u16);
        let carry = d.shl_carry_assign(3, DecimalDigit(7));
        assert_eq!(d, DecimalDigit(799));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(9_281u16);
        let carry = d.shl_carry_assign(11, DecimalDigit(83));
        assert_eq!(d, DecimalDigit(7_571));
        assert_eq!(carry, DecimalDigit(1_900));

        let mut d = DecimalDigit(9_281u32);
        let carry = d.shl_carry_assign(11, DecimalDigit(83));
        assert_eq!(d, DecimalDigit(19_007_571));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(781_187_923u32);
        let carry = d.shl_carry_assign(21, DecimalDigit(27_872));
        assert_eq!(d, DecimalDigit(815_123_168));
        assert_eq!(carry, DecimalDigit(1_638_269));
    }

    #[test]
    fn test_shr_carry_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let carry = d.shr_carry_assign(5, BinaryDigit(0x10));
        assert_eq!(d, BinaryDigit(0x80));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x43u8);
        let carry = d.shr_carry_assign(5, BinaryDigit(0x10));
        assert_eq!(d, BinaryDigit(0x82));
        assert_eq!(carry, BinaryDigit(0x03));

        let mut d = BinaryDigit(0xffu8);
        let carry = d.shl_carry_assign(3, BinaryDigit(0x07));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0x07));

        let mut d = BinaryDigit(0xffu16);
        let carry = d.shr_carry_assign(3, BinaryDigit(0x07));
        assert_eq!(d, BinaryDigit(0xe01f));
        assert_eq!(carry, BinaryDigit(0x07));

        let mut d = BinaryDigit(0xa3b4u16);
        let carry = d.shr_carry_assign(11, BinaryDigit(0x83));
        assert_eq!(d, BinaryDigit(0x1074));
        assert_eq!(carry, BinaryDigit(0x03b4));

        let mut d = BinaryDigit(0xa3b4u32);
        let carry = d.shr_carry_assign(11, BinaryDigit(0x83));
        assert_eq!(d, BinaryDigit(0x10600014));
        assert_eq!(carry, BinaryDigit(0x000003b4));

        let mut d = BinaryDigit(0x7f99a3b4u32);
        let carry = d.shr_carry_assign(21, BinaryDigit(0x21483));
        assert_eq!(d, BinaryDigit(0x10a41bfc));
        assert_eq!(carry, BinaryDigit(0x019a3b4));
    }

    #[test]
    fn test_shr_carry_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let carry = d.shr_carry_assign(5, DecimalDigit(10));
        assert_eq!(d, DecimalDigit(31));
        assert_eq!(carry, DecimalDigit(8));

        let mut d = DecimalDigit(43u8);
        let carry = d.shr_carry_assign(5, DecimalDigit(10));
        assert_eq!(d, DecimalDigit(32));
        assert_eq!(carry, DecimalDigit(19));

        let mut d = DecimalDigit(99u8);
        let carry = d.shl_carry_assign(3, DecimalDigit(7));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(7));

        let mut d = DecimalDigit(99u16);
        let carry = d.shr_carry_assign(3, DecimalDigit(7));
        assert_eq!(d, DecimalDigit(8_762));
        assert_eq!(carry, DecimalDigit(3));

        let mut d = DecimalDigit(9_281u16);
        let carry = d.shr_carry_assign(11, DecimalDigit(83));
        assert_eq!(d, DecimalDigit(409));
        assert_eq!(carry, DecimalDigit(1_649));

        let mut d = DecimalDigit(9_281u32);
        let carry = d.shr_carry_assign(11, DecimalDigit(83));
        assert_eq!(d, DecimalDigit(40_527_348));
        assert_eq!(carry, DecimalDigit(577));

        let mut d = DecimalDigit(781_187_923u32);
        let carry = d.shr_carry_assign(21, DecimalDigit(27_872));
        assert_eq!(d, DecimalDigit(13_290_777));
        assert_eq!(carry, DecimalDigit(1_620_819));
    }

    #[test]
    fn test_mul_carry_assign_binary()
    {
        let mut d = BinaryDigit(0u8);
        let carry = d.mul_carry_assign(BinaryDigit(0x47), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13u8);
        let carry = d.mul_carry_assign(BinaryDigit(0), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13u8);
        let carry = d.mul_carry_assign(BinaryDigit(0x47), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0x44));
        assert_eq!(carry, BinaryDigit(0x06));

        let mut d = BinaryDigit(0xffu8);
        let carry = d.mul_carry_assign(BinaryDigit(0xff), BinaryDigit(0xff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xff));

        let mut d = BinaryDigit(0u16);
        let carry = d.mul_carry_assign(BinaryDigit(0x472a), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0xffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2u16);
        let carry = d.mul_carry_assign(BinaryDigit(0), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0xffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2u16);
        let carry = d.mul_carry_assign(BinaryDigit(0x472a), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0x63b3));
        assert_eq!(carry, BinaryDigit(0x058c));

        let mut d = BinaryDigit(0xffffu16);
        let carry = d.mul_carry_assign(BinaryDigit(0xffff), BinaryDigit(0xffff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xffff));

        let mut d = BinaryDigit(0u32);
        let carry = d.mul_carry_assign(BinaryDigit(0x472a16ff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0xffffffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2aa87u32);
        let carry = d.mul_carry_assign(BinaryDigit(0), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0xffffffff));
        assert_eq!(carry, BinaryDigit(0));

        let mut d = BinaryDigit(0x13f2aa87u32);
        let carry = d.mul_carry_assign(BinaryDigit(0x472a16ff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0x24857678));
        assert_eq!(carry, BinaryDigit(0x058b94e7));

        let mut d = BinaryDigit(0xffffffffu32);
        let carry = d.mul_carry_assign(BinaryDigit(0xffffffff), BinaryDigit(0xffffffff));
        assert_eq!(d, BinaryDigit(0));
        assert_eq!(carry, BinaryDigit(0xffffffff));
    }

    #[test]
    fn test_mul_carry_assign_decimal()
    {
        let mut d = DecimalDigit(0u8);
        let carry = d.mul_carry_assign(DecimalDigit(47), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13u8);
        let carry = d.mul_carry_assign(DecimalDigit(0), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13u8);
        let carry = d.mul_carry_assign(DecimalDigit(47), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(10));
        assert_eq!(carry, DecimalDigit(7));

        let mut d = DecimalDigit(99u8);
        let carry = d.mul_carry_assign(DecimalDigit(99), DecimalDigit(99));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(99));

        let mut d = DecimalDigit(0u16);
        let carry = d.mul_carry_assign(DecimalDigit(4_729), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(9_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(1_392u16);
        let carry = d.mul_carry_assign(DecimalDigit(0), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(9_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(1392u16);
        let carry = d.mul_carry_assign(DecimalDigit(4_729), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(2_767));
        assert_eq!(carry, DecimalDigit(659));

        let mut d = DecimalDigit(9_999u16);
        let carry = d.mul_carry_assign(DecimalDigit(9_999), DecimalDigit(9_999));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(9_999));

        let mut d = DecimalDigit(0u32);
        let carry = d.mul_carry_assign(DecimalDigit(647_211_698), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(999_999_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13_921_887u32);
        let carry = d.mul_carry_assign(DecimalDigit(0), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(999_999_999));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(13_921_887u32);
        let carry = d.mul_carry_assign(DecimalDigit(647_211_698), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(124_634_125));
        assert_eq!(carry, DecimalDigit(9_010_409));

        let mut d = DecimalDigit(999_999_999u32);
        let carry = d.mul_carry_assign(DecimalDigit(999_999_999), DecimalDigit(999_999_999));
        assert_eq!(d, DecimalDigit(0));
        assert_eq!(carry, DecimalDigit(999_999_999));
    }

    #[test]
    fn test_div_carry_assign_binary()
    {
        let mut d = BinaryDigit(0x14u8);
        let carry = d.div_carry_assign(BinaryDigit(0x01), BinaryDigit(0x00));
        assert_eq!(d, BinaryDigit(0x14));
        assert_eq!(carry, BinaryDigit(0x00));

        let mut d = BinaryDigit(0xffu8);
        let carry = d.div_carry_assign(BinaryDigit(0x01), BinaryDigit(0x00));
        assert_eq!(d, BinaryDigit(0xff));
        assert_eq!(carry, BinaryDigit(0x00));

        let mut d = BinaryDigit(0u8);
        let carry = d.div_carry_assign(BinaryDigit(0x13), BinaryDigit(0x08));
        assert_eq!(d, BinaryDigit(0x6b));
        assert_eq!(carry, BinaryDigit(0x0f));

        let mut d = BinaryDigit(0x53u8);
        let carry = d.div_carry_assign(BinaryDigit(0x13), BinaryDigit(0x08));
        assert_eq!(d, BinaryDigit(0x70));
        assert_eq!(carry, BinaryDigit(0x03));

        let mut d = BinaryDigit(0x53u16);
        let carry = d.div_carry_assign(BinaryDigit(0x13), BinaryDigit(0x08));
        assert_eq!(d, BinaryDigit(0x6bce));
        assert_eq!(carry, BinaryDigit(0x09));

        let mut d = BinaryDigit(0x53u32);
        let carry = d.div_carry_assign(BinaryDigit(0x13), BinaryDigit(0x08));
        assert_eq!(d, BinaryDigit(0x6bca1af6));
        assert_eq!(carry, BinaryDigit(0x11));
    }

    #[test]
    fn test_div_carry_assign_decimal()
    {
        let mut d = DecimalDigit(14u8);
        let carry = d.div_carry_assign(DecimalDigit(1), DecimalDigit(0));
        assert_eq!(d, DecimalDigit(14));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(99u8);
        let carry = d.div_carry_assign(DecimalDigit(1), DecimalDigit(0));
        assert_eq!(d, DecimalDigit(99));
        assert_eq!(carry, DecimalDigit(0));

        let mut d = DecimalDigit(0u8);
        let carry = d.div_carry_assign(DecimalDigit(13), DecimalDigit(8));
        assert_eq!(d, DecimalDigit(61));
        assert_eq!(carry, DecimalDigit(7));

        let mut d = DecimalDigit(53u8);
        let carry = d.div_carry_assign(DecimalDigit(13), DecimalDigit(8));
        assert_eq!(d, DecimalDigit(65));
        assert_eq!(carry, DecimalDigit(8));

        let mut d = DecimalDigit(53u16);
        let carry = d.div_carry_assign(DecimalDigit(13), DecimalDigit(8));
        assert_eq!(d, DecimalDigit(6157));
        assert_eq!(carry, DecimalDigit(12));

        let mut d = DecimalDigit(53u32);
        let carry = d.div_carry_assign(DecimalDigit(13), DecimalDigit(8));
        assert_eq!(d, DecimalDigit(615384619));
        assert_eq!(carry, DecimalDigit(6));
    }

    #[test]
    fn test_add_prod_carry_assign_binary()
    {
        // digit, fac0, fac1, carry, new digit, new carry
        let cases = [
            (0x37u8, 0x00, 0xff, 0x00, 0x37, 0x00),
            (0x37u8, 0x00, 0xff, 0x23, 0x5a, 0x00),
            (0x37u8, 0xff, 0x00, 0x23, 0x5a, 0x00),
            (0xffu8, 0x21, 0x34, 0xac, 0x5f, 0x08),
            (0x23u8, 0xff, 0xff, 0x73, 0x97, 0xfe)
        ];
        for (idx, case) in cases.iter().enumerate()
        {
            let mut d = BinaryDigit(case.0);
            let carry = d.add_prod_carry_assign(BinaryDigit(case.1), BinaryDigit(case.2),
                BinaryDigit(case.3));
            assert_eq!(d, BinaryDigit(case.4), "wrong digit in u8 case {}", idx+1);
            assert_eq!(carry, BinaryDigit(case.5), "wrong carry in u8 case {}", idx+1);
        }

        // digit, fac0, fac1, carry, new digit, new carry
        let cases = [
            (0x37u32, 0x00, 0xff, 0x00, 0x37, 0x00),
            (0x37u32, 0x00, 0xff, 0x23, 0x5a, 0x00),
            (0xffu32, 0x21, 0x34, 0xac, 0x85f, 0x00),
            (0x23u32, 0xff, 0xff, 0x73, 0xfe97, 0x00),
            (0x716172cdu32, 0xf2413551, 0x82988190, 0xacd820ed, 0x08dd624a, 0x7b956e67),
            (0xffffffffu32, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff)
        ];
        for (idx, case) in cases.iter().enumerate()
        {
            let mut d = BinaryDigit(case.0);
            let carry = d.add_prod_carry_assign(BinaryDigit(case.1), BinaryDigit(case.2),
                BinaryDigit(case.3));
            assert_eq!(d, BinaryDigit(case.4), "wrong digit in u32 case {}", idx+1);
            assert_eq!(carry, BinaryDigit(case.5), "wrong carry in u32 case {}", idx+1);
        }
    }

    #[test]
    fn test_add_prod_carry_assign_decimal()
    {
        // digit, fac0, fac1, carry, new digit, new carry
        let cases = [
            (37u8, 00, 99, 00, 37,  0),
            (37u8, 00, 99, 23, 60,  0),
            (37u8, 99, 00, 23, 60,  0),
            (99u8, 21, 34, 75, 88,  8),
            (23u8, 99, 99, 73, 97, 98)
        ];
        for (idx, case) in cases.iter().enumerate()
        {
            let mut d = DecimalDigit(case.0);
            let carry = d.add_prod_carry_assign(DecimalDigit(case.1), DecimalDigit(case.2),
                DecimalDigit(case.3));
            assert_eq!(d, DecimalDigit(case.4), "wrong digit in u8 case {}", idx+1);
            assert_eq!(carry, DecimalDigit(case.5), "wrong carry in u8 case {}", idx+1);
        }

        // digit, fac0, fac1, carry, new digit, new carry
        let cases = [
            (37u32, 00, 99, 00, 37, 0),
            (37u32, 00, 99, 23, 60, 0),
            (99u32, 21, 34, 75, 888, 0),
            (23u32, 99, 99, 73, 9_897, 0),
            (983_109_582, 338_928_191, 233_922_929, 982_192_889, 124_693_910, 79_283_077),
            (999_999_999u32, 999_999_999, 999_999_999, 999_999_999, 999_999_999, 999_999_999)
        ];
        for (idx, case) in cases.iter().enumerate()
        {
            let mut d = DecimalDigit(case.0);
            let carry = d.add_prod_carry_assign(DecimalDigit(case.1), DecimalDigit(case.2),
                DecimalDigit(case.3));
            assert_eq!(d, DecimalDigit(case.4), "wrong digit in u32 case {}", idx+1);
            assert_eq!(carry, DecimalDigit(case.5), "wrong carry in u32 case {}", idx+1);
        }
    }
}
