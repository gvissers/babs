use crate::digit::Digit;

/// Multiply the number represented by `nr0` by `nr1` using long multiplication, and store the
/// result in `result`. The result array must have space for at least `n0+n1` digits,  where `n0`
/// denotes the number of digits in `nr0`, and `n1` the number of digits in `nr1`. Returns the
/// number of digits in the product.
pub fn mul_big_long_into<T>(nr0: &[T], nr1: &[T], result: &mut [T]) -> usize
where T: Digit
{
    let nd0 = nr0.len();
    let nd1 = nr1.len();
    let nd = nd0 + nd1;

    result[..nd].fill(T::zero());
    for (offset, &d1) in nr1.iter().enumerate()
    {
        let carry = nr0.iter()
            .zip(&mut result[offset..offset+nd0])
            .fold(T::zero(), |carry, (&d0, rd)| rd.add_prod_carry_assign(d0, d1, carry));
        result[offset+nd0] = carry;
    }

    crate::ubig::support::drop_leading_zeros(result, nd)
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::digit::{BinaryDigit, DecimalDigit};
    use num_traits::Zero;

    #[test]
    fn test_mul_big_long_into_binary()
    {
        let nr0: [BinaryDigit<u8>; 0] = [];
        let nr1 = [BinaryDigit(0x7f), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 3];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 0);
        assert_eq!(result, [BinaryDigit(0); 3]);

        let nr0 = [BinaryDigit(0x80u8)];
        let nr1 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 4];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 4);
        assert_eq!(result, [BinaryDigit(0x80), BinaryDigit(0x3f), BinaryDigit(0x9b), BinaryDigit(0x11)]);

        let nr0 = [BinaryDigit(0x80u8), BinaryDigit(0x65), BinaryDigit(0x21), BinaryDigit(0xfe), BinaryDigit(0x9c)];
        let nr1 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let mut result = [BinaryDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            BinaryDigit(0x80),
            BinaryDigit(0x5a),
            BinaryDigit(0x7a),
            BinaryDigit(0xfe),
            BinaryDigit(0x0d),
            BinaryDigit(0x2a),
            BinaryDigit(0x98),
            BinaryDigit(0x15)
        ]);

        let nr0 = [BinaryDigit(0x7fu8), BinaryDigit(0x36), BinaryDigit(0x23)];
        let nr1 = [BinaryDigit(0x80u8), BinaryDigit(0x65), BinaryDigit(0x21), BinaryDigit(0xfe), BinaryDigit(0x9c)];
        let mut result = [BinaryDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            BinaryDigit(0x80),
            BinaryDigit(0x5a),
            BinaryDigit(0x7a),
            BinaryDigit(0xfe),
            BinaryDigit(0x0d),
            BinaryDigit(0x2a),
            BinaryDigit(0x98),
            BinaryDigit(0x15)
        ]);

        let nr0 = [BinaryDigit(0x7f32u16), BinaryDigit(0x367d), BinaryDigit(0x23a0)];
        let nr1 = [BinaryDigit(0x8008u16), BinaryDigit(0x6543), BinaryDigit(0x21ff), BinaryDigit(0xfe)];
        let mut result = [BinaryDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 7);
        assert_eq!(result, [
            BinaryDigit(0xf990),
            BinaryDigit(0x779a),
            BinaryDigit(0x2315),
            BinaryDigit(0x4242),
            BinaryDigit(0x4238),
            BinaryDigit(0x5db1),
            BinaryDigit(0x23),
        ]);

        let nr0 = [BinaryDigit(0x7f32u32), BinaryDigit(0x367d), BinaryDigit(0x23a0)];
        let nr1 = [BinaryDigit(0x8008u32), BinaryDigit(0x6543), BinaryDigit(0x21ff), BinaryDigit(0xfe)];
        let mut result = [BinaryDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 6);
        assert_eq!(result, [
            BinaryDigit(0x3f9cf990),
            BinaryDigit(0x4d9037fe),
            BinaryDigit(0x3842d585),
            BinaryDigit(0x15d209ff),
            BinaryDigit(0x04f12c66),
            BinaryDigit(0x2358c0),
            BinaryDigit(0)
        ]);
    }

    #[test]
    fn test_mul_big_long_into_decimal()
    {
        let nr0: [DecimalDigit<u8>; 0] = [];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 3];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 0);
        assert_eq!(result, [DecimalDigit(0); 3]);

        let nr0 = [DecimalDigit(50u8)];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 4];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 4);
        assert_eq!(result, [DecimalDigit(50), DecimalDigit(24), DecimalDigit(68), DecimalDigit(11)]);

        let nr0 = [DecimalDigit(50u8), DecimalDigit(65), DecimalDigit(21), DecimalDigit(98), DecimalDigit(95)];
        let nr1 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let mut result = [DecimalDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            DecimalDigit(50),
            DecimalDigit(9),
            DecimalDigit(69),
            DecimalDigit(98),
            DecimalDigit(36),
            DecimalDigit(61),
            DecimalDigit(42),
            DecimalDigit(22)
        ]);

        let nr0 = [DecimalDigit(49u8), DecimalDigit(36), DecimalDigit(23)];
        let nr1 = [DecimalDigit(50u8), DecimalDigit(65), DecimalDigit(21), DecimalDigit(98), DecimalDigit(95)];
        let mut result = [DecimalDigit::zero(); 8];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 8);
        assert_eq!(result, [
            DecimalDigit(50),
            DecimalDigit(9),
            DecimalDigit(69),
            DecimalDigit(98),
            DecimalDigit(36),
            DecimalDigit(61),
            DecimalDigit(42),
            DecimalDigit(22)
        ]);

        let nr0 = [DecimalDigit(7_932u16), DecimalDigit(3_677), DecimalDigit(2_380)];
        let nr1 = [DecimalDigit(8_008u16), DecimalDigit(6_543), DecimalDigit(2_155), DecimalDigit(98)];
        let mut result = [DecimalDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 7);
        assert_eq!(result, [
            DecimalDigit(9456),
            DecimalDigit(843),
            DecimalDigit(9246),
            DecimalDigit(9632),
            DecimalDigit(1673),
            DecimalDigit(3789),
            DecimalDigit(23),
        ]);

        let nr0 = [DecimalDigit(7_932u32), DecimalDigit(3_677), DecimalDigit(2_380)];
        let nr1 = [DecimalDigit(8_008u32), DecimalDigit(6_543), DecimalDigit(2_155), DecimalDigit(98)];
        let mut result = [DecimalDigit::zero(); 7];
        let n = mul_big_long_into(&nr0, &nr1, &mut result);
        assert_eq!(n, 6);
        assert_eq!(result, [
            DecimalDigit(63_519_456),
            DecimalDigit(81_344_492),
            DecimalDigit(60_211_111),
            DecimalDigit(24_273_611),
            DecimalDigit(5_489_246),
            DecimalDigit(233_240),
            DecimalDigit(0)
        ]);
    }
}
