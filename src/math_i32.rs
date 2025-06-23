#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Provides I32. i32 already exists in Rust, but this module
/// is a verified implementation of a Move module which does not
/// provide native i32.
/// We use the reference Rust i32 to prove that the I32 operations
/// are correct.
mod math_i32 {
    use vstd::prelude::*;

    // Import the add/sub and truncate (for i32 etc) from prelude
    use vstd::prelude::add as add_and_truncate;
    use vstd::prelude::sub as sub_and_truncate;

    // use vstd::calc_macro::*;
    // const E_OVERFLOW: &str = "0";
    /// Encoding of the i32::MIN as an unsigned. -2^31, 0x80000000
    const MIN_AS_U32: u32 = 1 << 31;

    /// Encoding of the i32::MAX, 2^31 - 1 as an unsigned
    const MAX_AS_U32: u32 = 0x7FFFFFFF;

    // spec const TWO_TO_THE_31: nat = 0x1000_0000;
    spec const TWO_TO_THE_32: int = 0x1_0000_0000;

    /// An I32 represented over 32 bits
    struct I32 {
        bits: u32,
    }

    /// The I32 zero
    fn zero() -> (r: I32)
        ensures
            r.bits as i32 == 0,
    {
        I32 { bits: 0 }
    }

    /// Create an I32 from bits of a u32
    fn from_u32(v: u32) -> I32 {
        I32 { bits: v }
    }

    /// Performs a bitwise negation of a u8 value.
    fn u8_neg(v: u8) -> (r: u8)
        ensures
            v + r == 0xff,
            v as u8 + r as u8 == 0xff as u8,
    {
        assert(v + (v ^ 0xFF) == 0xFF) by (bit_vector);
        assert(v as i8 + (v ^ 0xFF) as i8 == 0xFF as i8) by (bit_vector);
        v ^ 0xff
    }

    /// Performs a bitwise negation of a u32 value.
    fn u32_neg(v: u32) -> (r: u32)
        ensures
            v + r == 0xFFFF_FFFF,
            v as i32 + r as i32 == 0xFFFF_FFFF as i32,
            ((r + 1) as u32) as i32 == -(v as i32) as i32,
    {
        assert(v + (v ^ 0xFFFF_FFFF) == 0xFFFF_FFFF) by (bit_vector);
        assert(v as i32 + (v ^ 0xFFFF_FFFF) as i32 == 0xFFFF_FFFF as i32) by (bit_vector);
        assert((((v ^ 0xFFFF_FFFF) + 1) as u32) as i32 == -(v as i32) as i32) by (bit_vector);
        v ^ 0xFFFF_FFFF
    }

    /// Converts a u32 value to an I32 value.
    /// Returns a non-negative integer with no overflow.
    fn from(v: u32) -> (r: I32)
        requires
            v <= MAX_AS_U32,
        ensures
            v == r.bits,
            0 <= v as i32 == r.bits as i32,
    {
        // assert!(v <= MAX_AS_U32, "{E_OVERFLOW}");
        I32 { bits: v }
    }

    /// Computes the sign of a 32-bit integer.
    fn sign(v: &I32) -> (r: u8)
        ensures
            0 <= r <= 1,
            r == sign_spec_i32(v.bits as i32),
    {
        proof {
            let a = v.bits;
            assert(a >> 31 <= 1) by (bit_vector);
            assert((a >> 31) >= 1 <==> (a as i32) < 0) by (bit_vector);
        }
        ((v.bits >> 31) as u8)
    }

    // Arithmetic operations
    /// Adds two I32s with wrapping.
    /// This uses the Verus reference specification `add` (imported
    /// as `add_and_truncate` that performs addition modulo k
    /// on fixed-size signed or unsigend integers.
    /// As can be seen in the post conditions, this is the same
    /// as addition modulo 2^32.
    fn wrapping_add(num1: &I32, num2: &I32) -> (r: I32)
        ensures
    // r.bits == (num1.bits + num2.bits) % 0x1_0000_0000,

            r.bits == (num1.bits + num2.bits) % TWO_TO_THE_32,
            r.bits as i32 == add_and_truncate(num1.bits as i32, num2.bits as i32),
    {
        // Compute the sum of the u32 using 64 bits and truncate.
        let sum = I32 { bits: (((num1.bits as u64) + (num2.bits as u64)) % 0x1_0000_0000) as u32 };
        // Proof section
        proof {
            // proof that add_and_truncate is same as sum
            add_u64_mod(num1.bits, num2.bits);
            // proof that the result in bits for add on signed
            // is the same as for unsigned.
            addition_is_same_in_i32_and_u32(num1.bits, num2.bits);
        }
        sum
    }

    /// Add two I32s and indicate overflow
    /// Result is in r.0 and overflow in r.1 (true indicates overflow)
    fn add(num1: &I32, num2: &I32) -> (r: (I32, bool))
        ensures
            r.0.bits as i32 == add_and_truncate(num1.bits as i32, num2.bits as i32),
            !r.1 <==> (num1.bits as i32) + (num2.bits as i32) == add_and_truncate(
                num1.bits as i32,
                num2.bits as i32,
            ),
    {
        let sum = wrapping_add(num1, num2);
        let overflow = (sign(num1) == sign(num2) && sign(num1) != sign(&sum));
        proof {
            cns_for_add_overflow_i32(num1.bits as i32, num2.bits as i32);
            assert(overflow <==> (num1.bits as i32) as int + (num2.bits as i32) as int
                != add_and_truncate(num1.bits as i32, num2.bits as i32));
        }
        (sum, overflow)
    }

    /// Subtraction modulo  2^32}
    /// a - b is a + (-b) and (-b) is !b + 1
    fn wrapping_sub(num1: &I32, num2: &I32) -> (r: I32)
        ensures
            r.bits == (num1.bits - num2.bits) % TWO_TO_THE_32,
            r.bits as i32 == sub_and_truncate(num1.bits as i32, num2.bits as i32),
    {
        // !num2 + 1 == -num2
        let sub_num = wrapping_add(&I32 { bits: u32_neg(num2.bits) }, &from(1));
        // num1 + (-num2)
        let res = wrapping_add(num1, &sub_num);
        proof {
            sub_add_truncate_lemma(num1.bits as i32, num2.bits as i32);
            assert(sub_and_truncate(num1.bits as i32, num2.bits as i32) == add_and_truncate(
                num1.bits as i32,
                -(num2.bits as i32) as i32,
            ));
        }
        res
    }

    fn sub(num1: &I32, num2: &I32) -> (r: (I32, bool))
        ensures
            r.0.bits as i32 == sub_and_truncate(num1.bits as i32, num2.bits as i32),
            !r.1 <==> (num1.bits as i32) - (num2.bits as i32) == sub_and_truncate(
                num1.bits as i32,
                num2.bits as i32,
            ),
    {
        let v = wrapping_sub(num1, num2);
        let overflow = sign(num1) != sign(num2) && sign(num1) != sign(&v);
        proof {
            cns_for_sub_overflow_i32(num1.bits as i32, num2.bits as i32);
            assert(overflow <==> (num1.bits as i32) as int - (num2.bits as i32) as int
                != sub_and_truncate(num1.bits as i32, num2.bits as i32));
        }
        (v, overflow)
    }

    fn mul(num1: &I32, num2: &I32) -> (r: (I32, bool)) 
        // ensures !r.1 ==> r.0.bits as i32 == num1.bits as i32 * num2.bits as i32
    {
        let a = abs_u32(num1) as u64;
        let b = abs_u32(num2) as u64;
        proof {
            assert(a * b <= 0xFFFF_FFFF * 0xFFFF_FFFF) by (nonlinear_arith)
                requires
                    a <= 0xFFFF_FFFF,
                    b <= 0xFFFF_FFFF,
            ;
        }
        let product: u64 = a * b;
        if product > MAX_AS_U32 as u64 {
            return (I32 { bits: 0 }, true);
        } else if (sign(num1) != sign(num2)) {
            let k = u32_neg(product as u32);
            assert( ((k + 1) as u32) as i32 == -(product as i32) as i32);
            assert((-(product as i32) as i32) >= -(MAX_AS_U32 as i32));
            // assert(k + 1 < 0x1_0000_0000) by(bit_vector);
            //     requires k < 0x7FFF_FFFF;
            // let s = u32_neg(product as u32) + 1;
            let s = k + 1;
            return (I32 { bits: s }, false);
        } else {
            // assert (product as i32 == num1.bits as i32 * num2.bits as i32) by(bit_vector);
            return (I32 { bits: product as u32 }, false);
        }
    }

    /// The absolute value of an I32. Not defined for 2^31 (MIN_AS_U32)
    fn abs_u32(v: &I32) -> (r: u32)
        ensures
            v.bits as i32 >= 0 ==> r as i32 == v.bits as i32,
            (v.bits as i32) < 0 ==> r as i32 == -(v.bits as i32) as i32,
            r <= 0xFFFF_FFFF,
    {
        if (sign(v) == 0) {
            v.bits
        } else {
            u32_neg(v.bits) + 1
        }
    }

    #[verifier::bit_vector]
    // proof fn twos_complement(a: u32)
    //     requires a != 1 << 31
    //     ensures (u32_neg(a) + 1) as i32 == -(a as i32) as i32
    // {
    // }
    //-------------------------------------------------------------------------
    // Lemmas and specs
    //-------------------------------------------------------------------------
    // Compute a +_u32 b and interpret it as i32 is the same as
    // interpret as i32 and add a +_i32 b
    #[verifier::bit_vector]
    proof fn addition_is_same_in_i32_and_u32(a: u32, b: u32)
        ensures
            add_and_truncate(a, b) as i32 == add_and_truncate(a as i32, b as i32),
    {
    }

    // For u32, adding in u64 modulo 0x1000_00000 is the same as adding in mathematical
    #[verifier::bit_vector]
    proof fn add_u64_mod(a: u32, b: u32)
        ensures
            (((a as u64) + (b as u64)) % 0x1_0000_0000) == add_and_truncate(a, b),
            ((a + b) % 0x1_0000_0000) == add_and_truncate(a, b),
    {
    }

    // #[verifier::bit_vector]
    // proof fn subtraction_is_same_in_i32_and_u32(a: u32, b: u32)
    //     ensures
    //         sub_and_truncate(a, b) as i32 == sub_and_truncate(
    //             a as i32,
    //             b as i32,
    //         ),
    //     // sub_and_truncate(a as i32, b as i32) as i32 == add_and_truncate(a as i32, -(b as i32)) as i32,
    // {
    // }
    #[verifier::bit_vector]
    proof fn sub_add_truncate_lemma(a: i32, b: i32)
        ensures
            sub_and_truncate(a, b) == add_and_truncate(a as i32, -b as i32),
    {
    }

    spec fn u8_neg_spec(v: u8) -> (r: u8) {
        (0xFF - v) as u8
    }

    spec fn u32_neg_spec(v: u32) -> (r: u32) {
        (0xFFFF_FFFF - v) as u32
    }

    // #[verifier::bit_vector]
    // proof fn sum_is_same_as_disjunct(x: u8, y: u8)
    //     ensures
    //         (x + y) > 0 <==> (x | y) > 0,
    // {
    // }
    /// The sign (definition) of a 32-bit integer.
    // spec fn sign_spec(v: &I32) -> (r: u8) {
    //     if v.bits as i32 >= 0 {
    //         0
    //     } else {
    //         1
    //     }
    // }
    spec fn sign_spec_i32(v: i32) -> (r: u8) {
        if v >= 0 {
            0
        } else {
            1
        }
    }

    // #[verifier::bit_vector]
    // proof fn cns_for_add_overflow_u32(a: i32, b: i32)
    //     ensures
    //         ((a < 0) && (b < 0) && (vstd::prelude::add(a, b) >= 0)) || ((a >= 0) && (b >= 0) && (
    //         vstd::prelude::add(a, b) < 0)) <==> a + b != vstd::prelude::add(a, b),
    // {
    // }
    /// Necessary and sufficient condition for add to overflow in i32.
    ///
    /// add_and_truncate(a, b) is the truncating add function over i32 whereas a + b
    /// operates on ints (mathematical unbounded integers) and is: a as int + b as int
    proof fn cns_for_add_overflow_i32(a: i32, b: i32)
        ensures
            (sign_spec_i32(a) == sign_spec_i32(b) && sign_spec_i32(a) != sign_spec_i32(
                add_and_truncate(a, b),
            )) <==> a + b != add_and_truncate(a, b),
    {
        // Expand the meaning of sign_spec_i32 and use bit_vector mode
        assert(((a < 0) && (b < 0) && (add_and_truncate(a, b) >= 0)) || ((a >= 0) && (b >= 0) && (
        add_and_truncate(a, b) < 0)) <==> a + b != add_and_truncate(a, b)) by (bit_vector);
    }

    /// Necessary and sufficient condition for sub overflow in i32.
    ///
    /// sub(a, b) is the truncating add function over i32 whereas a - b
    /// operates on ints (mathematical unbounded integers).
    #[verifier::bit_vector]
    proof fn cns_for_sub_overflow_i32(a: i32, b: i32)
        ensures
            (a >= 0) && (b < 0) && (a >= 0) && (sub_and_truncate(a, b) < 0) || (a < 0) && (b >= 0)
                && (a < 0) && (sub_and_truncate(a, b) >= 0) <==> a - b != sub_and_truncate(a, b),
    {
    }

    proof fn foo1(a: u8, b: u8, c: u8)
        requires
            a <= 1 || b <= 1 || c <= 1,
        ensures
            a & b & c <= 1,
    {
        assert(a & b & c <= 1) by (bit_vector)
            requires
                a <= 1 || b <= 1 || c <= 1,
        ;
    }

    // The necessary and sufficient condition (nsc) for the addition of two i32 values to not overflow is:
    // If both operands have the same sign, the result must not have a different sign.
    // Formally:
    //   If sign(num1) == sign(num2), then sign(num1) == sign(num1 + num2)
    // Or equivalently, overflow occurs if sign(num1) == sign(num2) && sign(num1) != sign(num1 + num2)
    //
    // In code:
    //   let sum = num1.wrapping_add(num2);
    //   let overflow = (num1 >= 0 && num2 >= 0 && sum < 0) || (num1 < 0 && num2 < 0 && sum >= 0);
    //   // No overflow if !overflow
    #[verifier::exec_allows_no_decreases_clause]
    // fn wrapping_add_old(num1: &I32, num2: &I32) -> I32 {
    //     let mut sum = num1.bits ^ num2.bits;
    //     let mut carry = (num1.bits & num2.bits) << 1;
    //     // assert ((sum + carry) % 0x1_0000_0000 == (num1.bits + num2.bits) % 0x1_0000_0000) by(bit_vector);
    //     let ghost x = num1.bits;
    //     let ghost y = num2.bits;
    //     assert((sum + carry) % 0x1_0000_0000 == (x + y) % 0x1_0000_0000) by (bit_vector)
    //         requires
    //             sum == num1.bits ^ num2.bits,
    //             carry == (num1.bits & num2.bits) << 1,
    //     ;
    //     while (carry != 0)
    //     // decreases i32::MAX - carry
    //     // invariant (sum as nat + carry as nat) % 0x1_0000_0000 == (num1.bits + num2.bits) % 0x1_0000_0000
    //     // invariant (sum as nat + carry as nat) % 0x1_0000_0000 == (num1.bits + num2.bits) % 0x1_0000_0000
    //      {
    //         let a = sum;
    //         let b = carry;
    //         sum = a ^ b;
    //         carry = (a & b) << 1;
    //     };
    //     I32 { bits: sum }
    // }
    proof fn foo(k: u8, n: u8)
        requires
            0 <= k <= 1,
        ensures
            0 <= k & n <= 1,
    {
        assert(0 <= (k & n) <= 1) by (bit_vector)
            requires
                0 <= k <= 1,
        ;
    }

    // fn add(num1: &I32, num2: &I32) -> (r: (I32, u8)) {
    //     let sum = wrapping_add(num1, num2);
    //     // assert ( 0 <= u8_neg(sign(&sum)) <= 1);
    //     // foo(sign_of(num2.bits), u8_neg(sign_of(&sum)));
    //     let x = sign(num2) & u8_neg(2);
    //     let y = sign(num1);
    //     // assert (0 <= y <= 1) by(bit_vector)
    //     //     requires ;
    //     assert(0 <= (y & x) <= 1) by (bit_vector)
    //         requires
    //             0 <= y <= 1,
    //     ;
    //     let w = u8_neg(sign(num1)) & u8_neg(sign(num2));
    //     let z = sign(&sum);
    //     assert(0 <= (w & z) <= 1) by (bit_vector)
    //         requires
    //             0 <= z <= 1,
    //     ;
    //     // assert (x & y == (sign(num1) & sign(num2) & u8_neg(sign(&sum))));
    //     // assert (0 <= (sign(num1) & sign(num2) & u8_neg(sign(&sum))) <= 1);
    //     // assert (0 <= sign_of(num1) & sign_of(num2) & u8_neg(sign(&sum)) <= 1) by(bit_vector);
    //     let overflow = (sign(num1) & sign(num2) & u8_neg(sign(&sum))) as u16 + (u8_neg(sign(num1))
    //         & u8_neg(sign(num2)) & sign(&sum)) as u16;
    //     // assert(overflow <= 0xff);
    //     // assert!(overflow == 0, EOverflow);
    //     (sum, overflow as u8)
    // }
    // fn wrapping_sub(num1: &I32, num2: &I32) -> (r: I32)
    //     ensures
    //         r.bits == (num1.bits - num2.bits)
    //             % 0x1000_00000,
    // // (sign_spec(&num1) == sign_spec(&num2)) ==> i32::MIN <= num1.bits - num2.bits <= i32::MAX
    // // sign_spec(num1) == sign_spec(num2) ==> r.bits == (num1.bits - num2.bits),
    // {
    //     // assume (sign_spec(&num1) == sign_spec(&num2) ==> )
    //     let sub_num = wrapping_add(&I32 { bits: u32_neg(num2.bits) }, &from(1));
    //     // assert
    //     wrapping_add(num1, &sub_num)
    // }
    // fn sub(num1: &I32, num2: &I32) -> (r: (
    //     I32,
    //     bool,
    // ))
    // // ensures !r.1 ==> r.0.bits as i32 == num1.bits as i32 - num2.bits as i32
    // {
    //     let v = wrapping_sub(num1, num2);
    //     let overflow = sign(num1) != sign(num2) && sign(num1) != sign(&v);
    //     // assert!(!overflow, "{E_OVERFLOW}");
    //     (v, overflow)
    // }
    // proof fn nsc_for_add_i32_overflow(
    //     num1: i32,
    //     num2: i32,
    // )
    // // ensures MIN_AS_U32 <= num1 + *num2 <= MAX_AS_U32
    // // ensures
    // //     sign_of(num1) != sign_of(num2) ==> i32::MIN <= num1 + num2 <= i32::MAX,
    // //     sign_of(num1) == sign_of(num2) == sign_of((num1 as i32 + num2 as i32) as i32) ==> i32::MIN <= num1 + num2 <= i32::MAX,
    // {
    //     assert(sign_spec(num1) != sign_spec(num2) ==> i32::MIN <= num1 + num2 <= i32::MAX);
    //     assert(sign_spec(num1) == sign_spec(num2) && sign_spec(num2) != sign_spec(
    //         (num1 as i32 + num2 as i32) as i32,
    //     ) ==> !(i32::MIN <= num1 + num2 <= i32::MAX));
    //     // #[verifier::truncate]
    //     // assert (sign_of(num1) ==  sign_of(num2) && sign_of(num2) == sign_of(( (num1 as i32 + num2 as i32) as i32)) ==> (i32::MIN <= num1 + num2 <= i32::MAX));
    //     if (sign_spec(num1) == sign_spec(num2)) {
    //         let k = (num1 as i32 + num2 as i32) as i32;
    //         if (sign_spec(num2) == sign_spec(k)) {
    //             if sign_spec(num1) == 0 {
    //                 assert(i32::MIN <= num1 + num2);
    //                 assert(num1 + num2 <= 2 * i32::MAX);
    //             } else {
    //                 // assert(i32::MIN <= num1 + num2);
    //                 assert(num1 + num2 <= i32::MAX);
    //             }
    //             // assert(i32::MIN <= num1 + num2 <= i32::MAX);
    //             // assert(i32::MIN <= num1 + num2);
    //             // assert(num1 + num2 <= i32::MAX);
    //             // assert(num1 + num2 <= );
    //         } else {
    //             assert(!(i32::MIN <= num1 + num2 <= i32::MAX));
    //         }
    //     } else {
    //         assert(i32::MIN <= num1 + num2 <= i32::MAX);
    //     }
    // }
    // proof fn nsc_for_sub_i32_overflow(num1: i32, num2: i32) {
    //     if (sign_spec(num1) != sign_spec(num2)) {
    //         #[verifier::truncate]
    //         let k: i32 = (num1 as i32 - num2 as i32) as i32;
    //         if (sign_spec(num1) != sign_spec(k)) {
    //             assert(!(i32::MIN <= num1 - num2 <= i32::MAX));
    //         } else {
    //             // assert(num1 - num2 <= i32::MAX);
    //             // assert(i32::MIN <= num1 - num2);
    //         }
    //     } else {
    //         assert(i32::MIN <= num1 - num2 <= i32::MAX);
    //     }
    // }
    // proof fn foo_i32_overflow(num1: &I32, num2: &I32)
    //     // ensures MIN_AS_U32 <= num1 + *num2 <= MAX_AS_U32
    //     ensures
    //         (sign_spec(num1) != sign_spec(num2)) ==> i32::MIN <= num1.bits + num2.bits <= i32::MAX,
    //         // sign_of(num1) == sign_of(num2) == sign( wrapping_add(num1, num2)) ==> i32::MIN <= *num1 + *num2 <= i32::MAX,
    // {
    //     // let x = *num1 as i64 + *num2 as i64;
    //     // x > MAX_AS_U32 as
    //     // !(
    //     //     ((*num1 < 0) && (*num2 > 0))
    //     //     ||
    //     //     ((*num1 > 0) && (*num2 < 0)))
    //     // (sign_of(num1) == sign_of(num2) && sign_of(num1) != sign(&wrapping_add(& I32{ bits: num1 }, &I32 { bits: num2 })))
    //     // sign_of(num1) != sign_of(num2)
    // }
    //-------------------------------------------------------------------------
    fn foo2(a: u64) {
        let mask_lo_u64: u32 = 0xFFFF_FFFF;
        // let r : u32 = 256 * 256;
        // assert (0xFFFF == r - 1);
        assert(a & 0xFFFF_FFFF == a % 0x1_0000_0000) by (bit_vector);
    }

    fn foo3(a: u128) {
        let mask_lo_128: u128 = 0xFFFF_FFFF_FFFF_FFFF;
        let two_to_the_64: u128 = 0x1_0000_0000_0000_0000u128;
        // let r : u32 = 256 * 256;
        // assert (0xFFFF == r - 1);
        assert(a & 0xFFFF_FFFF_FFFF_FFFFu128 == a % 0x1_0000_0000_0000_0000u128) by (bit_vector);
        assert(a & 0xFFFF_FFFF_FFFF_FFFFu128 == a % two_to_the_64) by (bit_vector)
            requires
                two_to_the_64 == 0x1_0000_0000_0000_0000u128,
        ;
        assert(mask_lo_128 == 0xFFFF_FFFF_FFFF_FFFF);
        assert(a & 0xFFFF_FFFF_FFFF_FFFF == a & mask_lo_128) by (bit_vector)
            requires
                mask_lo_128 == 0xFFFF_FFFF_FFFF_FFFF,
        ;
        // assert (a & mask_lo_128 == a % mask_lo_128) by (bit_vector) {

        // };
    }

    const MAX_U64: u64 = 0xFFFF_FFFFffffffff;

    const TWO_TO_THE_64: u128 = 0x1000_00000_00000000;

    const HI_64_MASK: u128 = 0xFFFF_FFFFffffffff0000000000000000;

    const LO_64_MASK: u128 = 0x0000000000000000ffffffffffffffff;

    // Powers of two
    // const TWO_TO_THE_64: u256 = 0x1000_00000_00000000;
    // const TWO_TO_THE_192: u256 = 0x1000_00000_00000000_00000000_00000000_00000000_00000000;
    // fn wrapping_add(n1: u64, n2: u64) -> (r: u64)
    //     ensures
    //         r == (n1 + n2) % (TWO_TO_THE_64 as int),
    // {
    //     let (sum, _) = overflowing_add(n1, n2);
    //     sum
    // }
    // fn overflowing_add(n1: u64, n2: u64) -> (r: (u64, bool))
    //     ensures
    //         r.1 <==> (n1 as u128) + (n2 as u128) > MAX_U64,
    //         r.0 == (n1 + n2) % (TWO_TO_THE_64 as int),
    // {
    //     let sum: u128 = (n1 as u128) + (n2 as u128);
    //     if sum > (MAX_U64 as u128) {
    //         assert(sum & 0xFFFF_FFFF_FFFF_FFFF == sum % 0x1000_00000_00000000) by (bit_vector);
    //         assert(sum & LO_64_MASK == sum % TWO_TO_THE_64);
    //         (((sum & LO_64_MASK) as u64), true)
    //     } else {
    //         ((sum as u64), false)
    //     }
    // }
    #[test]
    fn test_mex0() {
        let k = vec![-3, 1, 4, -7, 0, 1];
        let r = mex0(k);
        print!("{r}");
        assert!(r == 3);
    }

    proof fn foo12(v: u8, w: u8)
        requires
            0 <= v <= 1,
            0 <= w <= 1,
        ensures
            v == 0 ==> u8_neg_spec(v) & w == w,
            v == 1 ==> u8_neg_spec(v) & w == 0,
    // u8_neg_spec(v) & w ==

    {
        if (v == 0) {
            assert((0xff & w) == w) by (bit_vector);
            assert(u8_neg_spec(v) & w == w);
        } else {
            assert(v == 1);
            let a: u8 = (0xff - 1) as u8;
            assert(u8_neg_spec(v) == 254);
            if (w == 0) {
                assert((254 & w) == 0) by (bit_vector)
                    requires
                        w == 0,
                ;
            } else {
                assert((254 & w) == 0) by (bit_vector)
                    requires
                        w == 1,
                ;
            }
            assert(u8_neg_spec(v) & w == 0);
        }
    }

    proof fn foo11(v: u8, w: u8, x: u8)
        requires
            0 <= v <= 1,
            0 <= w <= 1,
            0 <= x <= 1,
        ensures
            (v & w & u8_neg_spec(x)) + (u8_neg_spec(v) & u8_neg_spec(w) & x) > 0 <==> (v == w) && (v
                != x),
    {
        // proof of ==>
        if (v & w & u8_neg_spec(x) > 0) {
            assert(v >= 1 && w >= 1) by (bit_vector)
                requires
                    0 <= v <= 1,
                    0 <= w <= 1,
                    v & w & (0xff - x) as u8 > 0,
            ;
            assert(v & w == 1) by (bit_vector)
                requires
                    v == w == 1,
            ;
            assert((v == w) && (v != x) == (v != x));
            let a = (0xff - x) as u8;
            let k: u8 = 1;
            assert(u8_neg_spec(x) >= 254);
            if (u8_neg_spec(x) == 255) {
                let k: u8 = u8_neg_spec(x);
                assert((v & w) & k == 1) by (bit_vector)
                    requires
                        k == 255,
                        v & w == 1,
                ;
                assert(v & w & u8_neg_spec(x) == 1);
            } else {
                let k: u8 = u8_neg_spec(x);
                assert(k == 254);
                assert((v & w) & k == 0) by (bit_vector)
                    requires
                        k == 254,
                        v & w == 1,
                ;
                assert(v & w & u8_neg_spec(x) == 0);
            }
        }
        if ((u8_neg_spec(v) & u8_neg_spec(w) & x) > 0) {
            let a = u8_neg_spec(v);
            let b = u8_neg_spec(w);
            assert(a >= 1 && b >= 1 && x >= 1) by (bit_vector)
                requires
                    0 <= x <= 1,
                    a & b & x > 0,
            ;
            assert(x == 1);
            if (v == 1 || w == 1) {
                assert(a == 254 || b == 254);
                assert((a & b & x) == 0) by (bit_vector)
                    requires
                        a == 254 || b == 254,
                        x == 1,
                ;
                assert(false);
            }
            assert(v == 0 && w == 0);
            assert(a == 255 && b == 255);
            assert((v == w) && (v != x));
        }
        // Other direction <==

        if ((v == w) && (v != x)) {
            assert((v == w));
            assert((v != x));
            if (v == 0) {
                // (u8_neg_spec(v) & u8_neg_spec(w) & x) > 0
                assert(x == 1);
                let a = u8_neg_spec(v);
                let b = u8_neg_spec(w);
                assert(a == b == 0xff);
                assert(a & b & x == x) by (bit_vector)
                    requires
                        a == b == 0xff,
                ;
                assert((a & b & x) > 0);
            } else {
                // v & w & u8_neg_spec(x)) > 0
                assert(x == 0);
                assert(v == w == 1);
                let a = u8_neg_spec(x);
                // let b = u8_neg_spec(w);
                assert(a == 0xff);
                assert(v & w & a > 0) by (bit_vector)
                    requires
                        a == 0xff,
                        v == w == 1,
                ;
                assert((v & w & a) > 0);
            }
        }
    }

}

} // verus!
fn main() {
    println!("Hello, world!");
}
