use crate::digit::Digit;

/// Compare two big numbers by their digits `nr0` and `nr1`.
#[inline]
pub fn cmp<T>(nr0: &[T], nr1: &[T]) -> std::cmp::Ordering
where T: Ord
{
    nr0.len().cmp(&nr1.len()).then_with(|| nr0.iter().rev().cmp(nr1.iter().rev()))
}

/// Compare two big numbers by their digits, returning whether `nr0 < nr1`.
#[inline]
pub fn lt<T>(nr0: &[T], nr1: &[T]) -> bool
where T: Digit
{
    cmp(nr0, nr1) == std::cmp::Ordering::Less
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_cmp()
    {
        let n: &[BinaryDigit<u8>; 0] = &[];
        let m: &[BinaryDigit<u8>; 0] = &[];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Equal);

        let n: &[BinaryDigit<u8>; 0] = &[];
        let m = &[BinaryDigit(1u8)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Less);
        assert_eq!(cmp(m, n), std::cmp::Ordering::Greater);

        let n = &[DecimalDigit(2u64)];
        let m = &[DecimalDigit(1u64)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Greater);
        assert_eq!(cmp(m, n), std::cmp::Ordering::Less);

        let n = &[BinaryDigit(2u64), BinaryDigit(1), BinaryDigit(3)];
        let m = &[BinaryDigit(2u64), BinaryDigit(1), BinaryDigit(3)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Equal);

        let n = &[BinaryDigit(1u64), BinaryDigit(1), BinaryDigit(3)];
        let m = &[BinaryDigit(2u64), BinaryDigit(1), BinaryDigit(3)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Less);
        assert_eq!(cmp(m, n), std::cmp::Ordering::Greater);

        let n = &[BinaryDigit(1u64), BinaryDigit(1), BinaryDigit(3)];
        let m = &[BinaryDigit(0u64), BinaryDigit(0), BinaryDigit(4)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Less);
        assert_eq!(cmp(m, n), std::cmp::Ordering::Greater);

        let n = &[DecimalDigit(1u32), DecimalDigit(1), DecimalDigit(3)];
        let m = &[DecimalDigit(0u32), DecimalDigit(0), DecimalDigit(0), DecimalDigit(1)];
        assert_eq!(cmp(n, m), std::cmp::Ordering::Less);
        assert_eq!(cmp(m, n), std::cmp::Ordering::Greater);
    }
}
