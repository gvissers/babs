use crate::digit::Digit;

/// Subtract the big number represented by te digits in `n0` from the number or number part represented
/// by `n1`, and store the result back in `nr0`. Returns the carry on underflow, or `None` if the
/// number does not underflow. The lengths of `nr0` must be equal to that of `nr1`.
pub fn rsub_assign_big<T>(nr0: &mut [T], nr1: &[T]) -> bool
where T: Digit
{
    assert!(nr1.len() == nr0.len());

    let mut carry = false;
    for (d0, mut d1) in nr0.iter_mut().zip(nr1.iter().copied())
    {
        carry = d1.sub_carry_assign(*d0, carry);
        *d0 = d1;
    }

    carry
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};

    #[test]
    fn test_rsub_assign_big_binary()
    {
        let mut nr0: [BinaryDigit<u8>; 0] = [];
        let nr1: [BinaryDigit<u8>; 0] = [];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, []);
        assert!(!underflow);

        let mut nr0 = [BinaryDigit(0x34u8), BinaryDigit(0x12)];
        let nr1 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0x02), BinaryDigit(0x04)]);
        assert!(!underflow);

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x12)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0xfb)]);
        assert!(underflow);

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x17)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0)]);
        assert!(!underflow);

        let mut nr0 = [BinaryDigit(0x36u8), BinaryDigit(0x16)];
        let nr1 = [BinaryDigit(0x34u8), BinaryDigit(0x16)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xfe), BinaryDigit(0xff)]);
        assert!(underflow);

        let mut nr0 = [BinaryDigit(0x81fe61acu32), BinaryDigit(0xf352e1a3), BinaryDigit(0x729100ac)];
        let nr1 = [BinaryDigit(0x6ffe6215u32), BinaryDigit(0xa625f3dc), BinaryDigit(0xd612f42f)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [BinaryDigit(0xee000069), BinaryDigit(0xb2d31238), BinaryDigit(0x6381f382)]);
        assert!(!underflow);
    }

    #[test]
    fn test_rsub_assign_big_decimal()
    {
        let mut nr0: [DecimalDigit<u8>; 0] = [];
        let nr1: [DecimalDigit<u8>; 0] = [];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, []);
        assert!(!underflow);

        let mut nr0 = [DecimalDigit(34u8), DecimalDigit(12)];
        let nr1 = [DecimalDigit(36u8), DecimalDigit(16)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(2), DecimalDigit(4)]);
        assert!(!underflow);

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(12)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(95)]);
        assert!(underflow);

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(17)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(0)]);
        assert!(!underflow);

        let mut nr0 = [DecimalDigit(36u8), DecimalDigit(16)];
        let nr1 = [DecimalDigit(34u8), DecimalDigit(16)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(98), DecimalDigit(99)]);
        assert!(underflow);

        let mut nr0 = [DecimalDigit(287_091_918u32), DecimalDigit(827_909_001), DecimalDigit(275_599_012)];
        let nr1 = [DecimalDigit(874_762_199u32), DecimalDigit(564_887_009), DecimalDigit(387_764_666)];
        let underflow = rsub_assign_big(&mut nr0, &nr1);
        assert_eq!(nr0, [DecimalDigit(587_670_281), DecimalDigit(736_978_008), DecimalDigit(112_165_653)]);
        assert!(!underflow);
    }
}
