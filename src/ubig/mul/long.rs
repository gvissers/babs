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

/// Square the number represented by `nr0` using long multiplication, and store the
/// result in `square`. The result array must have space for at least `2*n0` digits,  where `n0`
/// denotes the number of digits in `nr0`. Returns the number of digits in the square.
pub fn square_long_into<T>(nr0: &[T], square: &mut [T]) -> usize
where T: Digit
{
    let nd0 = nr0.len();
    let nd = 2*nd0;

    square[..nd].fill(T::zero());
    for (n1, &d1) in nr0.iter().enumerate().skip(1)
    {
        let carry = nr0[..n1].iter()
            .zip(&mut square[n1..2*n1])
            .fold(T::zero(), |carry, (&d0, rd)| rd.add_prod_carry_assign(d0, d1, carry));
        square[2*n1] = carry;
    }
    crate::ubig::shl::shl_carry_assign_within_digit(&mut square[..nd], 1, T::zero());
    let mut carry = false;
    for (&d, rds) in nr0.iter().zip(square[..nd].chunks_exact_mut(2))
    {
        let carry2 = rds[0].add_prod_carry_assign(d, d, T::from_bit(carry));
        carry = rds[1].add_carry_assign(carry2, false);
    }
    debug_assert!(!carry);

    crate::ubig::support::drop_leading_zeros(square, nd)
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

    #[test]
    fn test_square_long_into_binary()
    {
        let nr0: [BinaryDigit<u8>; 0] = [];
        let mut square = [];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 0);
        assert_eq!(square, []);

        let nr0 = [BinaryDigit(0x09_u8)];
        let mut square = [BinaryDigit::zero(); 2];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 1);
        assert_eq!(square, [BinaryDigit(0x51), BinaryDigit(0)]);

        let nr0 = [BinaryDigit(0x2f_u8)];
        let mut square = [BinaryDigit::zero(); 2];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 2);
        assert_eq!(square, [BinaryDigit(0xa1), BinaryDigit(0x08)]);

        let nr0 = [BinaryDigit(0x2f_u8), BinaryDigit(0xf4), BinaryDigit(0x89), BinaryDigit(0x12)];
        let mut square = [BinaryDigit::zero(); 8];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 8);
        assert_eq!(square, [
            BinaryDigit(0xa1),
            BinaryDigit(0xa0),
            BinaryDigit(0x37),
            BinaryDigit(0xdf),
            BinaryDigit(0xad),
            BinaryDigit(0xb0),
            BinaryDigit(0x57),
            BinaryDigit(0x01)
        ]);

        let nr0 = [BinaryDigit(0x7292df34_u32), BinaryDigit(0x839d52fa), BinaryDigit(0x2673feda)];
        let mut square = [BinaryDigit::zero(); 6];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 6);
        assert_eq!(square, [
            BinaryDigit(0xa9eba290),
            BinaryDigit(0x0ee8649d),
            BinaryDigit(0xc11f938f),
            BinaryDigit(0x834b3bb9),
            BinaryDigit(0xd51b4bab),
            BinaryDigit(0x5c6a437)
        ]);

        let nr0 = [BinaryDigit(0xffffffffffffffff_u64); 7];
        let mut square = [BinaryDigit::zero(); 14];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 14);
        assert_eq!(square, [
            BinaryDigit(1),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0),
            BinaryDigit(0xfffffffffffffffe),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff),
            BinaryDigit(0xffffffffffffffff)
        ]);
    }

    #[test]
    fn test_square_long_into_decimal()
    {
        let nr0: [DecimalDigit<u8>; 0] = [];
        let mut square = [];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 0);
        assert_eq!(square, []);

        let nr0 = [DecimalDigit(9_u8)];
        let mut square = [DecimalDigit::zero(); 2];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 1);
        assert_eq!(square, [DecimalDigit(81), DecimalDigit(0)]);

        let nr0 = [DecimalDigit(27_u8)];
        let mut square = [DecimalDigit::zero(); 2];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 2);
        assert_eq!(square, [DecimalDigit(29), DecimalDigit(7)]);

        let nr0 = [DecimalDigit(27_u8), DecimalDigit(86), DecimalDigit(93), DecimalDigit(2)];
        let mut square = [DecimalDigit::zero(); 8];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 7);
        assert_eq!(square, [
            DecimalDigit(29),
            DecimalDigit(51),
            DecimalDigit(64),
            DecimalDigit(28),
            DecimalDigit(55),
            DecimalDigit(63),
            DecimalDigit(8),
            DecimalDigit(0)
        ]);

        let nr0 = [DecimalDigit(872_201_010_u32), DecimalDigit(9_872_664), DecimalDigit(23_987_345)];
        let mut square = [DecimalDigit::zero(); 6];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 6);
        assert_eq!(square, [
            DecimalDigit(845_020_100),
            DecimalDigit(785_115_881),
            DecimalDigit(584_115_691),
            DecimalDigit(036_815_202),
            DecimalDigit(720_622_663),
            DecimalDigit(    575_392)
        ]);

        let nr0 = [DecimalDigit(9_876_543_210_123_456_789_u64); 7];
        let mut square = [DecimalDigit::zero(); 14];
        let n = square_long_into(&nr0, &mut square);
        assert_eq!(n, 14);
        assert_eq!(square, [
            DecimalDigit(2_267_946_958_750_190_521),
            DecimalDigit(4_290_504_495_643_956_714),
            DecimalDigit(6_313_062_032_537_722_908),
            DecimalDigit(8_335_619_569_431_489_102),
            DecimalDigit(  358_177_106_325_255_296),
            DecimalDigit(2_380_734_643_219_021_491),
            DecimalDigit(4_403_292_180_112_787_685),
            DecimalDigit(1_889_955_799_506_172_837),
            DecimalDigit(9_867_398_262_612_406_645),
            DecimalDigit(7_844_840_725_718_640_450),
            DecimalDigit(5_822_283_188_824_874_256),
            DecimalDigit(3_799_725_651_931_108_062),
            DecimalDigit(1_777_168_115_037_341_868),
            DecimalDigit(9_754_610_578_143_575_674)
        ]);
    }
}
