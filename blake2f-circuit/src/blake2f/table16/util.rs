// todo fix islesp and lebs2ip 128 bits or 64bits

use group::ff::{Field, PrimeField};

use halo2_proofs::{
    circuit::{Chip, Layouter, Region, Value, AssignedCell},
    pasta::pallas,
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn, Any, Assigned},
    poly::Rotation,
};
use std::convert::TryInto;
use std::marker::PhantomData;

pub const MASK_EVEN_32: u32 = 0x55555555;

/// The sequence of bits representing a u64 in little-endian order.
///
/// # Panics
///
/// Panics if the expected length of the sequence `NUM_BITS` exceeds
/// 64.
pub fn i2lebsp<const NUM_BITS: usize>(int: u128) -> [bool; NUM_BITS] {
    /// Takes in an FnMut closure and returns a constant-length array with elements of
    /// type `Output`.
    fn gen_const_array<Output: Copy + Default, const LEN: usize>(
        closure: impl FnMut(usize) -> Output,
    ) -> [Output; LEN] {
        gen_const_array_with_default(Default::default(), closure)
    }

    fn gen_const_array_with_default<Output: Copy, const LEN: usize>(
        default_value: Output,
        closure: impl FnMut(usize) -> Output,
    ) -> [Output; LEN] {
        let mut ret: [Output; LEN] = [default_value; LEN];
        for (bit, val) in ret.iter_mut().zip((0..LEN).map(closure)) {
            *bit = val;
        }
        ret
    }

    assert!(NUM_BITS <= 128);
    gen_const_array(|mask: usize| (int & (1 << mask)) != 0)
}

/// Returns the integer representation of a little-endian bit-array.
/// Panics if the number of bits exceeds 64.
pub fn lebs2ip<const K: usize>(bits: &[bool; K]) -> u64 {
    assert!(K <= 64);
    bits.iter()
        .enumerate()
        .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

/// Helper function that interleaves a little-endian bit-array with zeros
/// in the odd indices. That is, it takes the array
///         [b_0, b_1, ..., b_n]
/// to
///         [b_0, 0, b_1, 0, ..., b_n, 0].
/// Panics if bit-array is longer than 16 bits.
pub fn spread_bits<const DENSE: usize, const SPREAD: usize>(
    bits: impl Into<[bool; DENSE]>,
) -> [bool; SPREAD] {
    assert_eq!(DENSE * 2, SPREAD);
    assert!(DENSE <= 16);

    let bits: [bool; DENSE] = bits.into();
    let mut spread = [false; SPREAD];

    for (idx, bit) in bits.iter().enumerate() {
        spread[idx * 2] = *bit;
    }

    spread
}

/// Negates the even bits in a spread bit-array.
pub fn negate_spread<const LEN: usize>(arr: [bool; LEN]) -> [bool; LEN] {
    assert_eq!(LEN % 2, 0);

    let mut neg = arr;
    for even_idx in (0..LEN).step_by(2) {
        let odd_idx = even_idx + 1;
        assert!(!arr[odd_idx]);

        neg[even_idx] = !arr[even_idx];
    }

    neg
}

/// Returns even bits in a bit-array
pub fn even_bits<const LEN: usize, const HALF: usize>(bits: [bool; LEN]) -> [bool; HALF] {
    assert_eq!(LEN % 2, 0);
    let mut even_bits = [false; HALF];
    for idx in 0..HALF {
        even_bits[idx] = bits[idx * 2]
    }
    even_bits
}

/// Returns odd bits in a bit-array
pub fn odd_bits<const LEN: usize, const HALF: usize>(bits: [bool; LEN]) -> [bool; HALF] {
    assert_eq!(LEN % 2, 0);
    let mut odd_bits = [false; HALF];
    for idx in 0..HALF {
        odd_bits[idx] = bits[idx * 2 + 1]
    }
    odd_bits
}

/// todo check converted carry to 64bits - change the carry implementation elsewhere
/// Given a vector of words as vec![(lo: u16, mo: u16, el: u16, hi: u16)], returns their sum: u64, along
/// with a carry bit.
pub fn sum_with_carry(words: Vec<(Value<u16>, Value<u16>,Value<u16>, Value<u16>)>) -> (Value<u64>, Value<u64>) {
    let words_lo: Value<Vec<u128>> = words.iter().map(|(lo, _,_,_)| lo.map(|lo| lo as u128)).collect();
    let words_mo: Value<Vec<u128>> = words.iter().map(|(_, mo,_,_)| mo.map(|mo| mo as u128)).collect();
    let words_el: Value<Vec<u128>> = words.iter().map(|(_, _,el,_)| el.map(|el| el as u128)).collect();
    let words_hi: Value<Vec<u128>> = words.iter().map(|(_,_,_, hi)| hi.map(|hi| hi as u128)).collect();

    let sum: Value<u128> = {
        let sum_lo: Value<u128> = words_lo.map(|vec| vec.iter().sum());
        let sum_mo: Value<u128> = words_mo.map(|vec| vec.iter().sum());
        let sum_el: Value<u128> = words_el.map(|vec| vec.iter().sum());
        let sum_hi: Value<u128> = words_hi.map(|vec| vec.iter().sum());
        sum_lo
        .zip(sum_mo)
        .zip(sum_el)
        .zip(sum_hi)
        .map(|(((lo,mo),el), hi)| lo + (1 << 16) * mo + (1 << 32) * el + (1 << 64) * hi)
    };

    let carry = sum.map(|sum| (sum >> 64) as u64);
    let sum = sum.map(|sum| sum as u64);

    (sum, carry)
}