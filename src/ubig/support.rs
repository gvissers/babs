use num_traits::Zero;

/// Return the length of the segment in `nr[..len]` without leading zeros. Since numbers are
/// stored in lttle endian order, leading zeros occur at the the end of the segment.
#[inline]
pub fn drop_leading_zeros<T>(nr: &[T], len: usize) -> usize
where T: Zero
{
    let mut n = len;
    while n > 0 && nr[n-1].is_zero()
    {
        n -= 1
    }
    n
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_drop_leading_zeros()
    {
        let nr = &[BinaryDigit(0x7fu8), BinaryDigit(0), BinaryDigit(0), BinaryDigit(0x23)];
        assert_eq!(drop_leading_zeros(nr, 4), 4);
        assert_eq!(drop_leading_zeros(nr, 3), 1);
        assert_eq!(drop_leading_zeros(nr, 2), 1);
        assert_eq!(drop_leading_zeros(nr, 1), 1);
        assert_eq!(drop_leading_zeros(nr, 0), 0);

        let nr = &[DecimalDigit(23u64), DecimalDigit(0), DecimalDigit(987_654_321_123_456_789), DecimalDigit(0), DecimalDigit(1)];
        assert_eq!(drop_leading_zeros(nr, 5), 5);
        assert_eq!(drop_leading_zeros(nr, 4), 3);
        assert_eq!(drop_leading_zeros(nr, 3), 3);
        assert_eq!(drop_leading_zeros(nr, 2), 1);
        assert_eq!(drop_leading_zeros(nr, 1), 1);
        assert_eq!(drop_leading_zeros(nr, 0), 0);
    }
}
