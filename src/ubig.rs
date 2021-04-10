mod add;
mod div;
mod mul;
mod shl;
mod sub;

use crate::digit::{BinaryDigit, Digit, DigitStorage, DecimalDigit};
use crate::result::{Error, Result};
use num_traits::{Zero, One, Pow};
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
            if let Some(carry) = add::add_assign_big(&mut self.digits[offset..], &other.digits)
            {
                self.digits.push(carry);
            }
        }
        else
        {
            self.digits.extend_from_slice(&other.digits[n0-offset..]);
            if let Some(carry) = add::add_assign_big(&mut self.digits[offset..], &other.digits[..n0-offset])
            {
                self.digits.push(carry);
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
            || sub::sub_assign_big(&mut self.digits[offset..], &other.digits).is_some()
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
        if let Some(digit) = mul::mul_add_assign_digit(&mut self.digits, fac, offset)
        {
            self.digits.push(digit);
        }
        self.drop_leading_zeros();
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

    /// Divide this number by single digit `fac`, and return the remainder. If `fac` is zero,
    /// a `DivisionByZero` error is returned.
    fn div_assign_digit(&mut self, fac: T) -> Result<T>
    where T: Digit
    {
        if fac.is_zero()
        {
            Err(Error::DivisionByZero)
        }
        else
        {
            let rem = div::div_assign_digit(&mut self.digits, fac);
            self.drop_leading_zeros();
            Ok(rem)
        }
    }

    /// Divide this number by the two-digit number `fac_low+b*fac_high`, where `b` is the base
    /// of this number, and return the remainder. If both fac_low and fac_high are zero,
    /// a DivideByZero error is returned.
    fn div_pair_assign_digit(&mut self, fac_low: T, fac_high: T) -> Result<(T, T)>
    where T: Digit
    {
        if fac_high.is_zero()
        {
            self.div_assign_digit(fac_low).map(|rem| (rem, T::zero()))
        }
        else
        {
            let rem = div::div_pair_assign_digit(&mut self.digits, fac_low, fac_high);
            self.drop_leading_zeros();
            Ok(rem)
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
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    {
        // FIXME
        write!(f, "<unimplemented>")
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
    fn cmp(&self, other: &Self) -> std::cmp::Ordering
    {
        self.nr_digits().cmp(&other.nr_digits())
            .then_with(|| self.digits.iter().rev().cmp(other.digits.iter().rev()))
    }
}

impl<T> std::ops::AddAssign<T> for UBig<T>
where T: Digit
{
    fn add_assign(&mut self, digit: T)
    {
        if let Some(carry) = add::add_assign_digit(&mut self.digits, digit)
        {
            self.digits.push(carry);
        }
    }
}

impl<T> std::ops::AddAssign<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn add_assign(&mut self, digit: T)
    {
        *self += BinaryDigit(digit);
    }
}

impl<T> std::ops::AddAssign<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn add_assign(&mut self, n: T)
    {
        if DecimalDigit::fits_single(n)
        {
            *self += DecimalDigit(n);
        }
        else
        {
            let (high, low) = DecimalDigit::split(n);
            *self += low;
            if self.digits.is_empty()
            {
                self.digits.push(DecimalDigit::zero());
            }
            if let Some(carry) = add::add_assign_digit(&mut self.digits[1..], high)
            {
                self.digits.push(carry);
            }
        }
    }
}

impl<T> std::ops::AddAssign<UBig<T>> for UBig<T>
where T: Digit
{
    fn add_assign(&mut self, other: UBig<T>)
    {
        *self += &other;
    }
}

impl<T> std::ops::AddAssign<&UBig<T>> for UBig<T>
where T: Digit
{
    fn add_assign(&mut self, other: &UBig<T>)
    {
        self.add_assign_big_at_offset(other, 0);
    }
}

impl<T> std::ops::Add<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn add(self, digit: T) -> Self::Output
    {
        &self + digit
    }
}

impl<T> std::ops::Add<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, digit: T) -> Self::Output
    {
        let mut sum = self.clone();
        sum += digit;
        sum
    }
}

impl<T> std::ops::Add<T> for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = Self;
    fn add(self, digit: T) -> Self::Output
    {
        &self + digit
    }
}

impl<T> std::ops::Add<T> for &UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn add(self, digit: T) -> Self::Output
    {
        let mut sum = self.clone();
        sum += digit;
        sum
    }
}

impl<T> std::ops::Add<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn add(self, digit: T) -> Self::Output
    {
        &self + digit
    }
}

impl<T> std::ops::Add<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn add(self, digit: T) -> Self::Output
    {
        let mut sum = self.clone();
        sum += digit;
        sum
    }
}

impl<T> std::ops::Add<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn add(self, other: UBig<T>) -> Self::Output
    {
        &self + &other
    }
}

impl<T> std::ops::Add<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn add(self, other: &UBig<T>) -> Self::Output
    {
        &self + other
    }
}

impl<T> std::ops::Add<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, other: UBig<T>) -> Self::Output
    {
        self + &other
    }
}

impl<T> std::ops::Add<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, other: &UBig<T>) -> Self::Output
    {
        let mut n = self.clone();
        n += other;
        n
    }
}


impl<T> std::ops::DivAssign<T> for UBig<T>
where T: Digit
{
    fn div_assign(&mut self, digit: T)
    {
        if let Err(err) = self.div_assign_digit(digit)
        {
            panic!("Failed to perform division: {}", err);
        }
    }
}

impl<T> std::ops::DivAssign<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn div_assign(&mut self, digit: T)
    {
        *self /= BinaryDigit(digit);
    }
}

impl<T> std::ops::DivAssign<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn div_assign(&mut self, n: T)
    {
        if DecimalDigit::fits_single(n)
        {
            *self /= DecimalDigit(n);
        }
        else
        {
            let (high, low) = DecimalDigit::split(n);
            if let Err(err) = self.div_pair_assign_digit(low, high)
            {
                panic!("Failed to perform division: {}", err);
            }
        }
    }
}

impl<T> std::ops::Div<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn div(self, digit: T) -> Self::Output
    {
        &self / digit
    }
}

impl<T> std::ops::Div<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn div(self, digit: T) -> Self::Output
    {
        let mut quotient = self.clone();
        quotient /= digit;
        quotient
    }
}

impl<T> std::ops::Div<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = Self;
    fn div(self, digit: T) -> Self::Output
    {
        &self / digit
    }
}

impl<T> std::ops::Div<T> for &UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn div(self, digit: T) -> Self::Output
    {
        self / BinaryDigit(digit)
    }
}

impl<T> std::ops::Div<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn div(self, digit: T) -> Self::Output
    {
        &self / digit
    }
}

impl<T> std::ops::Div<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn div(self, n: T) -> Self::Output
    {
        let mut quotient = self.clone();
        quotient /= n;
        quotient
    }
}


impl<T> std::ops::MulAssign<T> for UBig<T>
where T: Digit
{
    fn mul_assign(&mut self, digit: T)
    {
        self.mul_add_assign_digit(digit, T::zero());
    }
}

impl<T> std::ops::MulAssign<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn mul_assign(&mut self, digit: T)
    {
        *self *= BinaryDigit(digit);
    }
}

impl<T> std::ops::MulAssign<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn mul_assign(&mut self, n: T)
    {
        if DecimalDigit::fits_single(n)
        {
            *self *= DecimalDigit(n);
        }
        else
        {
            let (high, low) = DecimalDigit::split(n);
            self.mul_pair_add_assign_digit(low, high, DecimalDigit::zero());
        }
    }
}

impl<T> std::ops::MulAssign<UBig<T>> for UBig<T>
where T: Digit
{
    fn mul_assign(&mut self, other: Self)
    {
        *self *= &other;
    }
}

impl<T> std::ops::MulAssign<&UBig<T>> for UBig<T>
where T: Digit
{
    fn mul_assign(&mut self, other: &UBig<T>)
    {
        *self = &*self * other;
    }
}

impl<T> std::ops::Mul<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn mul(self, digit: T) -> Self::Output
    {
        &self * digit
    }
}

impl<T> std::ops::Mul<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn mul(self, digit: T) -> Self::Output
    {
        let mut product = self.clone();
        product *= digit;
        product
    }
}

impl<T> std::ops::Mul<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = Self;
    fn mul(self, digit: T) -> Self::Output
    {
        &self * digit
    }
}

impl<T> std::ops::Mul<T> for &UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn mul(self, digit: T) -> Self::Output
    {
        let mut product = self.clone();
        product *= digit;
        product
    }
}

impl<T> std::ops::Mul<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn mul(self, digit: T) -> Self::Output
    {
        &self * digit
    }
}

impl<T> std::ops::Mul<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn mul(self, digit: T) -> Self::Output
    {
        let mut product = self.clone();
        product *= digit;
        product
    }
}

impl<T> std::ops::Mul<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn mul(self, other: UBig<T>) -> Self::Output
    {
        &self * &other
    }
}

impl<T> std::ops::Mul<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn mul(self, other: &UBig<T>) -> Self::Output
    {
        &self * other
    }
}

impl<T> std::ops::Mul<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn mul(self, other: UBig<T>) -> Self::Output
    {
        self * &other
    }
}

impl<T> std::ops::Mul<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn mul(self, other: &UBig<T>) -> Self::Output
    {
        self.mul_big(other)
    }
}


impl<T> std::ops::ShlAssign<usize> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn shl_assign(&mut self, n: usize)
    {
        let (high, low) = (n / BinaryDigit::<T>::NR_BITS, n % BinaryDigit::<T>::NR_BITS);
        if low != 0
        {
            let carry = shl::shl_add_assign_within_digit(&mut self.digits, low, BinaryDigit::zero());
            if !carry.is_zero()
            {
                self.digits.push(carry);
            }
        }
        if high != 0
        {
            self.digits.splice(..0, std::iter::repeat(BinaryDigit::zero()).take(high));
        }
    }
}

impl<T> std::ops::ShlAssign<usize> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn shl_assign(&mut self, n: usize)
    {
        if n <= 4 * DecimalDigit::<T>::MAX_HEX_PLACES
        {
            let carry = shl::shl_add_assign_within_digit(&mut self.digits, n, DecimalDigit::zero());
            if !carry.is_zero()
            {
                self.digits.push(carry);
            }
        }
        else
        {
            let two = UBig::one() + UBig::one();
            let scale = two.pow(n);
            *self *= scale;
        }
    }
}

impl<T> std::ops::Shl<usize> for UBig<T>
where T: Digit, UBig<T>: std::ops::ShlAssign<usize>
{
    type Output = Self;
    fn shl(self, n: usize) -> Self::Output
    {
        &self << n
    }
}

impl<T> std::ops::Shl<usize> for &UBig<T>
where T: Digit, UBig<T>: std::ops::ShlAssign<usize>
{
    type Output = UBig<T>;
    fn shl(self, n: usize) -> Self::Output
    {
        let mut shifted = self.clone();
        shifted <<= n;
        shifted
    }
}


impl<T> std::ops::SubAssign<T> for UBig<T>
where T: Digit
{
    fn sub_assign(&mut self, digit: T)
    {
        if sub::sub_assign_digit(&mut self.digits, digit).is_some()
        {
            panic!("Failed to subtract: {}", Error::Underflow);
        }
        self.drop_leading_zeros();
    }
}

impl<T> std::ops::SubAssign<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn sub_assign(&mut self, digit: T)
    {
        *self -= BinaryDigit(digit);
    }
}

impl<T> std::ops::SubAssign<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn sub_assign(&mut self, n: T)
    {
        if DecimalDigit::fits_single(n)
        {
            *self -= DecimalDigit(n);
        }
        else
        {
            let (high, low) = DecimalDigit::split(n);
            *self -= low;
            if sub::sub_assign_digit(&mut self.digits[1..], high).is_some()
            {
                panic!("Failed to subtract: {}", Error::Underflow);
            }
            self.drop_leading_zeros();
        }
    }
}

impl<T> std::ops::SubAssign<UBig<T>> for UBig<T>
where T: Digit
{
    fn sub_assign(&mut self, other: UBig<T>)
    {
        *self -= &other;
    }
}

impl<T> std::ops::SubAssign<&UBig<T>> for UBig<T>
where T: Digit
{
    fn sub_assign(&mut self, other: &UBig<T>)
    {
        if let Err(err) = self.sub_assign_big_at_offset(other, 0)
        {
            panic!("Failed to subtract: {}", err);
        }
    }
}

impl<T> std::ops::Sub<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn sub(self, digit: T) -> Self::Output
    {
        &self - digit
    }
}

impl<T> std::ops::Sub<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, digit: T) -> Self::Output
    {
        let mut difference = self.clone();
        difference -= digit;
        difference
    }
}

impl<T> std::ops::Sub<T> for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = Self;
    fn sub(self, digit: T) -> Self::Output
    {
        &self - digit
    }
}

impl<T> std::ops::Sub<T> for &UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn sub(self, digit: T) -> Self::Output
    {
        let mut difference = self.clone();
        difference -= digit;
        difference
    }
}

impl<T> std::ops::Sub<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn sub(self, digit: T) -> Self::Output
    {
        &self - digit
    }
}

impl<T> std::ops::Sub<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn sub(self, digit: T) -> Self::Output
    {
        let mut difference = self.clone();
        difference -= digit;
        difference
    }
}

impl<T> std::ops::Sub<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn sub(self, other: UBig<T>) -> Self::Output
    {
        &self - &other
    }
}

impl<T> std::ops::Sub<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn sub(self, other: &UBig<T>) -> Self::Output
    {
        &self - other
    }
}

impl<T> std::ops::Sub<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, other: UBig<T>) -> Self::Output
    {
        self - &other
    }
}

impl<T> std::ops::Sub<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, other: &UBig<T>) -> Self::Output
    {
        let mut difference = self.clone();
        difference -= other;
        difference
    }
}

impl<T> num_traits::Pow<usize> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn pow(self, exp: usize) -> Self::Output
    {
        (&self).pow(exp)
    }
}

impl<T> num_traits::Pow<usize> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn pow(self, exp: usize) -> Self::Output
    {
        match exp
        {
            0 => UBig::one(),
            1 => self.clone(),
//             2 => self.square(),
            _ => {
                let mut result = if exp % 2 == 0 { UBig::one() } else { self.clone() };
                let mut power = self.clone();
                let mut n = exp / 2;
                while n > 0
                {
//                     power = power.square();
                    power = &power * &power;
                    if n % 2 != 0
                    {
                        result *= &power;
                    }
                    n >>= 1;
                }
                result
            }
        }
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
}
