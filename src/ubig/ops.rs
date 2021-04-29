use super::UBig;
use crate::digit::{BinaryDigit, DecimalDigit, Digit, DigitStorage};
use crate::result::Error;
use num_traits::{Zero, One, Pow};

impl<T> std::ops::AddAssign<T> for UBig<T>
where T: Digit
{
    fn add_assign(&mut self, digit: T)
    {
        if let Some(carry) = super::add::add_assign_digit(&mut self.digits, digit)
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
            if let Some(carry) = super::add::add_assign_digit(&mut self.digits[1..], high)
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
    fn add(mut self, digit: T) -> Self::Output
    {
        self += digit;
        self
    }
}

impl<T> std::ops::Add<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, digit: T) -> Self::Output
    {
        self.clone() + digit
    }
}

impl<T> std::ops::Add<T> for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = Self;
    fn add(mut self, digit: T) -> Self::Output
    {
        self += digit;
        self
    }
}

impl<T> std::ops::Add<T> for &UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn add(self, digit: T) -> Self::Output
    {
        self.clone() + digit
    }
}

impl<T> std::ops::Add<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn add(mut self, digit: T) -> Self::Output
    {
        self += digit;
        self
    }
}

impl<T> std::ops::Add<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn add(self, digit: T) -> Self::Output
    {
        self.clone() + digit
    }
}

impl<T> std::ops::Add<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn add(self, other: UBig<T>) -> Self::Output
    {
        self + &other
    }
}

impl<T> std::ops::Add<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn add(mut self, other: &UBig<T>) -> Self::Output
    {
        self += other;
        self
    }
}

impl<T> std::ops::Add<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, other: UBig<T>) -> Self::Output
    {
        self.clone() + &other
    }
}

impl<T> std::ops::Add<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn add(self, other: &UBig<T>) -> Self::Output
    {
        self.clone() + other
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
            if let Err(err) = self.div_assign_digit_pair(low, high)
            {
                panic!("Failed to perform division: {}", err);
            }
        }
    }
}

impl<T> std::ops::DivAssign<UBig<T>> for UBig<T>
where T: Digit
{
    fn div_assign(&mut self, other: UBig<T>)
    {
        *self /= &other;
    }
}

impl<T> std::ops::DivAssign<&UBig<T>> for UBig<T>
where T: Digit
{
    fn div_assign(&mut self, other: &UBig<T>)
    {
        if let Err(err) = self.div_assign_big(other)
        {
            panic!("Failed to perform division: {}", err);
        }
    }
}

impl<T> std::ops::Div<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn div(mut self, digit: T) -> Self::Output
    {
        self /= digit;
        self
    }
}

impl<T> std::ops::Div<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn div(self, digit: T) -> Self::Output
    {
        self.clone() / digit
    }
}

impl<T> std::ops::Div<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = Self;
    fn div(mut self, digit: T) -> Self::Output
    {
        self /= digit;
        self
    }
}

impl<T> std::ops::Div<T> for &UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn div(self, digit: T) -> Self::Output
    {
        self.clone() / digit
    }
}

impl<T> std::ops::Div<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn div(mut self, digit: T) -> Self::Output
    {
        self /= digit;
        self
    }
}

impl<T> std::ops::Div<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn div(self, n: T) -> Self::Output
    {
        self.clone() / n
    }
}

impl<T> std::ops::Div<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn div(self, other: Self) -> Self::Output
    {
        self / &other
    }
}

impl<T> std::ops::Div<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn div(mut self, other: &UBig<T>) -> Self::Output
    {
        self /= other;
        self
    }
}

impl<T> std::ops::Div<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn div(self, other: UBig<T>) -> Self::Output
    {
        self.clone() / &other
    }
}

impl<T> std::ops::Div<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn div(self, other: &UBig<T>) -> Self::Output
    {
        self.clone() / other
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
    fn mul(mut self, digit: T) -> Self::Output
    {
        self *= digit;
        self
    }
}

impl<T> std::ops::Mul<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn mul(self, digit: T) -> Self::Output
    {
        self.clone() * digit
    }
}

impl<T> std::ops::Mul<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = Self;
    fn mul(mut self, digit: T) -> Self::Output
    {
        self *= digit;
        self
    }
}

impl<T> std::ops::Mul<T> for &UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn mul(self, digit: T) -> Self::Output
    {
        self.clone() * digit
    }
}

impl<T> std::ops::Mul<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn mul(mut self, digit: T) -> Self::Output
    {
        self *= digit;
        self
    }
}

impl<T> std::ops::Mul<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn mul(self, digit: T) -> Self::Output
    {
        self.clone() * digit
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


impl<T> std::ops::RemAssign<T> for UBig<T>
where T: Digit
{
    fn rem_assign(&mut self, digit: T)
    {
        match self.rem_digit(digit)
        {
            Ok(rem) => {
                self.digits.clear();
                if !rem.is_zero()
                {
                    self.digits.push(rem);
                }
            },
            Err(err) => { panic!("Failed to compute remainder: {}", err); }
        }
    }
}

impl<T> std::ops::RemAssign<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn rem_assign(&mut self, digit: T)
    {
        *self %= BinaryDigit(digit);
    }
}

impl<T> std::ops::RemAssign<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn rem_assign(&mut self, n: T)
    {
        if DecimalDigit::fits_single(n)
        {
            *self %= DecimalDigit(n);
        }
        else
        {
            // FIXME? Perhaps a non-detructive rem_digit_pair() function could be created. Not
            // worth the trouble for the moment, though.
            let (high, low) = DecimalDigit::split(n);
            match self.div_assign_digit_pair(low, high)
            {
                Ok((rem_low, rem_high)) => {
                    self.digits.clear();
                    if !rem_high.is_zero()
                    {
                        self.digits.push(rem_low);
                        self.digits.push(rem_high);
                    }
                    else if !rem_low.is_zero()
                    {
                        self.digits.push(rem_low);
                    }
                },
                Err(err) => { panic!("Failed to compute remainder: {}", err); }
            }
        }
    }
}

impl<T> std::ops::RemAssign<UBig<T>> for UBig<T>
where T: Digit
{
    fn rem_assign(&mut self, other: UBig<T>)
    {
        *self %= &other;
    }
}

impl<T> std::ops::RemAssign<&UBig<T>> for UBig<T>
where T: Digit
{
    fn rem_assign(&mut self, other: &UBig<T>)
    {
        if let Err(err) = self.rem_assign_big(other)
        {
            panic!("Failed to compute remainder: {}", err);
        }
    }
}

impl<T> std::ops::Rem<T> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn rem(self, digit: T) -> Self::Output
    {
        &self % digit
    }
}

impl<T> std::ops::Rem<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn rem(self, digit: T) -> Self::Output
    {
        match self.rem_digit(digit)
        {
            Ok(rem) => UBig::new(vec![rem]),
            Err(err) => { panic!("Failed to compute remainder: {}", err) }
        }
    }
}

impl<T> std::ops::Rem<T> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = Self;
    fn rem(self, digit: T) -> Self::Output
    {
        &self % digit
    }
}

impl<T> std::ops::Rem<T> for &UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn rem(self, digit: T) -> Self::Output
    {
        self % BinaryDigit(digit)
    }
}

impl<T> std::ops::Rem<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn rem(mut self, digit: T) -> Self::Output
    {
        self %= digit;
        self
    }
}

impl<T> std::ops::Rem<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn rem(self, digit: T) -> Self::Output
    {
        self.clone() % digit
    }
}

impl<T> std::ops::Rem<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn rem(self, other: Self) -> Self::Output
    {
        self % &other
    }
}

impl<T> std::ops::Rem<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn rem(mut self, other: &UBig<T>) -> Self::Output
    {
        self %= other;
        self
    }
}

impl<T> std::ops::Rem<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn rem(self, other: UBig<T>) -> Self::Output
    {
        self.clone() % &other
    }
}

impl<T> std::ops::Rem<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn rem(self, other: &UBig<T>) -> Self::Output
    {
        self.clone() % other
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
            let carry = super::shl::shl_carry_assign_within_digit(&mut self.digits, low, BinaryDigit::zero());
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
            let carry = super::shl::shl_carry_assign_within_digit(&mut self.digits, n, DecimalDigit::zero());
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
    fn shl(mut self, n: usize) -> Self::Output
    {
        self <<= n;
        self
    }
}

impl<T> std::ops::Shl<usize> for &UBig<T>
where T: Digit, UBig<T>: std::ops::ShlAssign<usize>
{
    type Output = UBig<T>;
    fn shl(self, n: usize) -> Self::Output
    {
        self.clone() << n
    }
}


impl<T> std::ops::ShrAssign<usize> for UBig<BinaryDigit<T>>
where BinaryDigit<T>: Digit
{
    fn shr_assign(&mut self, n: usize)
    {
        let (high, low) = (n / BinaryDigit::<T>::NR_BITS, n % BinaryDigit::<T>::NR_BITS);
        if high != 0
        {
            self.digits.drain(..high);
        }
        if low != 0
        {
            let (nd, _) = super::shr::shr_carry_assign_within_digit(&mut self.digits, low, BinaryDigit::zero());
            if nd < self.nr_digits()
            {
                self.digits.truncate(nd);
            }
        }
    }
}

impl<T> std::ops::ShrAssign<usize> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    fn shr_assign(&mut self, n: usize)
    {
        if n <= 4 * DecimalDigit::<T>::MAX_HEX_PLACES
        {
            let (nd, _) = super::shr::shr_carry_assign_within_digit(&mut self.digits, n, DecimalDigit::zero());
            if nd < self.nr_digits()
            {
                self.digits.truncate(nd);
            }
        }
        else
        {
            // FIXME
            unimplemented!()
        }
    }
}

impl<T> std::ops::Shr<usize> for UBig<T>
where T: Digit, UBig<T>: std::ops::ShrAssign<usize>
{
    type Output = Self;
    fn shr(mut self, n: usize) -> Self::Output
    {
        self >>= n;
        self
    }
}

impl<T> std::ops::Shr<usize> for &UBig<T>
where T: Digit, UBig<T>: std::ops::ShrAssign<usize>
{
    type Output = UBig<T>;
    fn shr(self, n: usize) -> Self::Output
    {
        self.clone() >> n
    }
}


impl<T> std::ops::SubAssign<T> for UBig<T>
where T: Digit
{
    fn sub_assign(&mut self, digit: T)
    {
        if super::sub::sub_assign_digit(&mut self.digits, digit).is_some()
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
            if super::sub::sub_assign_digit(&mut self.digits[1..], high).is_some()
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
    fn sub(mut self, digit: T) -> Self::Output
    {
        self -= digit;
        self
    }
}

impl<T> std::ops::Sub<T> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, digit: T) -> Self::Output
    {
        self.clone() - digit
    }
}

impl<T> std::ops::Sub<T> for UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = Self;
    fn sub(mut self, digit: T) -> Self::Output
    {
        self -= digit;
        self
    }
}

impl<T> std::ops::Sub<T> for &UBig<BinaryDigit<T>>
where T: DigitStorage, BinaryDigit<T>: Digit
{
    type Output = UBig<BinaryDigit<T>>;
    fn sub(self, digit: T) -> Self::Output
    {
        self.clone() - digit
    }
}

impl<T> std::ops::Sub<T> for UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = Self;
    fn sub(mut self, digit: T) -> Self::Output
    {
        self -= digit;
        self
    }
}

impl<T> std::ops::Sub<T> for &UBig<DecimalDigit<T>>
where T: DigitStorage, DecimalDigit<T>: Digit
{
    type Output = UBig<DecimalDigit<T>>;
    fn sub(self, digit: T) -> Self::Output
    {
        self.clone() - digit
    }
}

impl<T> std::ops::Sub<UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn sub(self, other: UBig<T>) -> Self::Output
    {
        self - &other
    }
}

impl<T> std::ops::Sub<&UBig<T>> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn sub(mut self, other: &UBig<T>) -> Self::Output
    {
        self -= other;
        self
    }
}

impl<T> std::ops::Sub<UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, other: UBig<T>) -> Self::Output
    {
        self.clone() - &other
    }
}

impl<T> std::ops::Sub<&UBig<T>> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn sub(self, other: &UBig<T>) -> Self::Output
    {
        self.clone() - other
    }
}


impl<T> num_traits::Pow<usize> for UBig<T>
where T: Digit
{
    type Output = Self;
    fn pow(self, exp: usize) -> Self::Output
    {
        match exp
        {
            0 => UBig::one(),
            1 => self,
            2 => self.square(),
            _ => {
                let mut result = if exp % 2 == 0 { UBig::one() } else { self.clone() };
                let mut power = self;
                let mut n = exp / 2;
                while n > 0
                {
                    power = power.square();
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

impl<T> num_traits::Pow<usize> for &UBig<T>
where T: Digit
{
    type Output = UBig<T>;
    fn pow(self, exp: usize) -> Self::Output
    {
        self.clone().pow(exp)
    }
}

