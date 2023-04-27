// todo fix chain error

use crate::blake2f::table16::gate::Gate;

use super::super::util::*;

use group::ff::{Field, PrimeField};
use halo2_proofs::plonk::{Constraint, Constraints, Expression};
use std::marker::PhantomData;

pub struct CompressionGate<F: Field>(PhantomData<F>);

impl<F: PrimeField> CompressionGate<F> {
    fn ones() -> Expression<F> {
        Expression::Constant(F::ONE)
    }

    // Decompose `A,B,C,D` words
    // (16, 16, 16, 16)-bit chunks
    // no tag required for 16bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_decompose_abcd(
        s_decompose_abcd: Expression<F>,
        a: Expression<F>,
        spread_a: Expression<F>,
        b: Expression<F>,
        spread_b: Expression<F>,
        c: Expression<F>,
        spread_c: Expression<F>,
        d: Expression<F>,
        spread_d: Expression<F>,
        word_lo: Expression<F>,
        spread_word_lo: Expression<F>,
        word_mo: Expression<F>,
        spread_word_mo: Expression<F>,
        word_el: Expression<F>,
        spread_word_el: Expression<F>,
        word_hi: Expression<F>,
        spread_word_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > {
        let dense_check = a
            + b * F::from(1 << 16)
            + c * F::from(1 << 32)
            + d * F::from(1 << 48)
            // what is word_lo/word_hi?
            + word_lo * (-F::ONE)
            + word_mo * F::from(1 << 32) * (-F::ONE)
            + word_el * F::from(1 << 64) * (-F::ONE)
            + word_hi * F::from(1 << 96) * (-F::ONE);
        let spread_check = spread_a
            + spread_b * F::from(1 << 32)
            + spread_c * F::from(1 << 64)
            + spread_d * F::from(1 << 96)
            + spread_word_lo * (-F::ONE)
            + spread_word_hi * F::from(1 << 64) * (-F::ONE)
            + spread_word_hi * F::from(1 << 128) * (-F::ONE)
            + spread_word_hi * F::from(1 << 192) * (-F::ONE);

        Constraints::with_selector(
            s_decompose_abcd,
            dense_check
                .chain(Some(("spread_check", spread_check)))
        )

    }


// Decompose `A,B,C,D` words
    // (16, 16, 8, 8, 16)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_decompose_efgh(
        s_decompose_efgh: Expression<F>,
        e: Expression<F>,
        spread_e: Expression<F>,
        f_lo: Expression<F>,
        spread_f_lo: Expression<F>,
        f_hi: Expression<F>,
        spread_f_hi: Expression<F>,
        g: Expression<F>,
        spread_g: Expression<F>,
        h: Expression<F>,
        spread_h: Expression<F>,
        word_lo: Expression<F>,
        spread_word_lo: Expression<F>,
        word_hi: Expression<F>,
        spread_word_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > {
        // bits are range checked while looking up spread
        let dense_check = e
            + f_lo * F::from(1 << 8)
            + f_hi * F::from(1 << 16)
            + g * F::from(1 << 32)
            + h * F::from(1 << 48)
            // what is word_lo/word_hi?
            + word_lo * (-F::ONE)
            + word_hi * F::from(1 << 32) * (-F::ONE);
        let spread_check = spread_e
            + spread_f_lo * F::from(1 << 16)
            + spread_f_hi * F::from(1 << 32)
            + spread_g * F::from(1 << 64)
            + spread_h * F::from(1 << 96)
            + spread_word_lo * (-F::ONE)
            + spread_word_hi * F::from(1 << 64) * (-F::ONE);

        Constraints::with_selector(
            s_decompose_efgh,
            dense_check
                .chain(Some(("spread_check", spread_check))),
        )

    }



    // Decompose `A,B,C,D` words
    // (16, 16, 16, 15, 1)-bit chunks
    #[allow(clippy::too_many_arguments)]
    pub fn s_decompose_ijkl(
        s_decompose_efgh: Expression<F>,
        i_lo: Expression<F>,
        spread_i_lo: Expression<F>,
        i_hi: Expression<F>,
        spread_i_hi: Expression<F>,
        j: Expression<F>,
        spread_j: Expression<F>,
        k: Expression<F>,
        spread_k: Expression<F>,
        l: Expression<F>,
        spread_l: Expression<F>,
        word_lo: Expression<F>,
        spread_word_lo: Expression<F>,
        word_hi: Expression<F>,
        spread_word_hi: Expression<F>,
    ) -> Constraints<
        F,
        (&'static str, Expression<F>),
        impl Iterator<Item = (&'static str, Expression<F>)>,
    > { 
        let dense_check = i_lo
            + i_hi * F::from(1 << 1)
            + j * F::from(1 << 16)
            + k * F::from(1 << 32)
            + l * F::from(1 << 48)
            // what is word_lo/word_hi?
            + word_lo * (-F::ONE)
            + word_hi * F::from(1 << 32) * (-F::ONE);
        let spread_check = spread_i_lo
            + spread_i_hi * F::from(1 << 2)
            + spread_j * F::from(1 << 32)
            + spread_k * F::from(1 << 64)
            + spread_l * F::from(1 << 96)
            + spread_word_lo * (-F::ONE)
            + spread_word_hi * F::from(1 << 64) * (-F::ONE);

        Constraints::with_selector(
            s_decompose_efgh,
            dense_check
                .chain(Some(("spread_check", spread_check))),
        )

    }


// convert to take spread values
// First gate addition modulo, Va ← Va + Vb + x   with input
//todo change decomposition of words a,b,c,d after each rounds
#[allow(clippy::too_many_arguments)]
    pub fn s_spread_a1(
        s_spread_a1: Expression<F>,
        spread_m_a1: Expression<F>,
        spread_n_a1: Expression<F>,
        spread_o_a1: Expression<F>,
        spread_p_a1: Expression<F>,
        spread_m_a: Expression<F>,
        spread_n_a: Expression<F>,
        spread_o_a: Expression<F>,
        spread_p_a: Expression<F>,
        spread_m_b: Expression<F>,
        spread_n_b: Expression<F>,
        spread_o_b: Expression<F>,
        spread_p_b: Expression<F>,        
        spread_m_x: Expression<F>,
        spread_n_x: Expression<F>,
        spread_o_x: Expression<F>,
        spread_p_x: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let spread_a = spread_m_a + spread_n_a * F::from(1 << 32) + spread_o_a * F::from(1 << 64) + spread_p_a * F::from(1 << 96);
        let spread_b = spread_m_b + spread_n_b * F::from(1 << 32) + spread_o_b * F::from(1 << 64) + spread_p_b * F::from(1 << 96);
        let spread_x = spread_m_x + spread_n_x * F::from(1 << 32) + spread_o_x * F::from(1 << 64) + spread_p_x * F::from(1 << 96);
        let spread_sum = spread_a + spread_b + spread_x;

        let spread_a1 = spread_m_a1 + spread_n_a1 * F::from(1 << 16) + spread_o_a1 * F::from(1 << 32) + spread_p_a1 * F::from(1 << 48);

        let check = spread_sum - spread_a1;

        Some(("spread_a1", s_spread_a1 * (spread_sum - spread_a1)))
    }


// Second gate, xor and bit rotations: Vd ← (Vd xor Va) >>> 32
// vector_d1 on abcd words
    #[allow(clippy::too_many_arguments)]
    pub fn s_spread_d1(
        s_spread_d1: Expression<F>,
        spread_m_d1_even: Expression<F>,
        spread_m_d1_odd: Expression<F>,
        spread_n_d1_even: Expression<F>,
        spread_n_d1_odd: Expression<F>,
        spread_o_d1_even: Expression<F>,
        spread_o_d1_odd: Expression<F>,
        spread_p_d1_even: Expression<F>,
        spread_p_d1_odd: Expression<F>,
        spread_m_c: Expression<F>,
        spread_n_c: Expression<F>,
        spread_o_c: Expression<F>,
        spread_p_c: Expression<F>,
        spread_m_d: Expression<F>,
        spread_n_d: Expression<F>,
        spread_o_d: Expression<F>,
        spread_p_d: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {

        let spread_witness = 
               spread_m_d1_even + spread_m_d1_odd * F::from(2)
            + (spread_n_d1_even + spread_n_d1_odd * F::from(2)) * F::from(1 << 32)
            + (spread_o_d1_even + spread_o_d1_odd * F::from(2)) * F::from(1 << 64)
            + (spread_p_d1_even + spread_p_d1_odd * F::from(2)) * F::from(1 << 128);

        let xor_1 = spread_m_c.clone()
            + spread_n_c.clone() * F::from(1 << 32)
            + spread_o_c.clone() * F::from(1 << 64)
            + spread_p_c.clone() * F::from(1 << 96);

        let xor_2 = spread_m_d.clone()
            + spread_n_d.clone() * F::from(1 << 32)
            + spread_o_d.clone() * F::from(1 << 64)
            + spread_p_d.clone() * F::from(1 << 96);

        let xor = xor_1 + xor_2;

        let check = spread_witness + (xor * -F::ONE);

        // bit rotation
        let rot = spread_o_c.clone() + spread_p_d.clone()
            + (spread_p_c.clone() + spread_p_d.clone())* F::from(1 << 32)
            + (spread_m_c.clone() + spread_m_d.clone())* F::from(1 << 64)
            + (spread_n_c.clone() + spread_n_d.clone())* F::from(1 << 96);

        Some(("spread_d1", s_spread_d1 * check))

    }


// Third gate addition modulo:  Vc ← Vc + Vd   no input
// i.e Vc1 = Vc +Vd1
#[allow(clippy::too_many_arguments)]
pub fn s_spread_c1(
    s_spread_c1: Expression<F>,
    spread_m_c1: Expression<F>,
    spread_n_c1: Expression<F>,
    spread_o_c1: Expression<F>,
    spread_p_c1: Expression<F>,
    spread_m_c: Expression<F>,
    spread_n_c: Expression<F>,
    spread_o_c: Expression<F>,
    spread_p_c: Expression<F>,
    spread_m_d1: Expression<F>,
    spread_n_d1: Expression<F>,
    spread_o_d1: Expression<F>,
    spread_p_d1: Expression<F>,        
) -> Option<(&'static str, Expression<F>)> {
    let spread_c = spread_m_c + spread_n_c * F::from(1 << 32) + spread_o_c * F::from(1 << 64) + spread_p_c * F::from(1 << 96);
    let spread_d1 = spread_m_d1 + spread_n_d1 * F::from(1 << 32) + spread_o_d1 * F::from(1 << 64) + spread_p_d1 * F::from(1 << 96);
    let spread_sum = spread_c + spread_d1;

    let spread_c1 = spread_m_c1 + spread_n_c1 * F::from(1 << 32) + spread_o_c1 * F::from(1 << 64) + spread_p_c1 * F::from(1 << 96);

    let check = spread_sum - spread_c1;

    Some(("spread_c1", s_spread_c1 * (spread_sum - spread_c1)))
}

// check if put spread_m_b2_lo_even
// Fourth gate: Vb1 ← (Vb xor Vc1) >>> 24
// vector_b1 on abcd words
#[allow(clippy::too_many_arguments)]
    pub fn s_spread_b1(
        s_spread_b1: Expression<F>,
        spread_m_b1_even: Expression<F>,
        spread_m_b1_odd: Expression<F>,
        spread_n_b1_even: Expression<F>,
        spread_n_b1_odd: Expression<F>,
        spread_o_b1_even: Expression<F>,
        spread_o_b1_odd: Expression<F>,
        spread_p_b1_even: Expression<F>,
        spread_p_b1_odd: Expression<F>,
        spread_m_c1: Expression<F>,
        spread_n_lo_c1: Expression<F>,
        spread_n_hi_c1: Expression<F>,
        spread_o_c1: Expression<F>,
        spread_p_c1: Expression<F>,
        spread_m_b: Expression<F>,
        spread_n_lo_b: Expression<F>,
        spread_n_hi_b: Expression<F>,
        spread_o_b: Expression<F>,
        spread_p_b: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {

        let spread_witness = 
               spread_m_b1_even + spread_m_b1_odd * F::from(2)
            + (spread_n_b1_even + spread_n_b1_odd * F::from(2)) * F::from(1 << 64)
            + (spread_o_b1_even + spread_o_b1_odd * F::from(2)) * F::from(1 << 64)
            + (spread_p_b1_even + spread_p_b1_odd * F::from(2)) * F::from(1 << 64);

        let xor_1 = spread_m_c1.clone()
            + spread_n_lo_c1.clone() * F::from(1 << 32)
            + spread_n_hi_c1.clone() * F::from(1 << 48)
            + spread_o_c1.clone() * F::from(1 << 64)
            + spread_p_c1.clone() * F::from(1 << 96);

        let xor_2 = spread_m_b.clone()
            + spread_n_lo_b.clone() * F::from(1 << 32)
            + spread_n_hi_b.clone() * F::from(1 << 48)
            + spread_o_b.clone() * F::from(1 << 64)
            + spread_p_b.clone() * F::from(1 << 96);

        let xor = xor_1 + xor_2;

        let check = spread_witness + (xor * -F::ONE);

        // bit rotation
        let rot = spread_n_hi_c1.clone() + spread_n_hi_b.clone()
            + (spread_o_c1.clone() + spread_o_b.clone())* F::from(1 << 16)
            + (spread_p_c1.clone() + spread_p_b.clone())* F::from(1 << 48)
            + (spread_m_c1.clone() + spread_m_b.clone())* F::from(1 << 80)
            + (spread_n_lo_c1.clone() + spread_n_lo_b.clone())* F::from(1 << 112) ;

        Some(("spread_b1", s_spread_b1 * check))

    }

 
// Fifth gate addition modulo, Va2 ← Va1 + Vb1 + y   with input
#[allow(clippy::too_many_arguments)]
    pub fn s_spread_a2(
        s_spread_a2: Expression<F>,
        spread_m_a2: Expression<F>,
        spread_n_a2: Expression<F>,
        spread_o_a2: Expression<F>,
        spread_p_a2: Expression<F>,
        spread_m_a1: Expression<F>,
        spread_n_a1: Expression<F>,
        spread_o_a1: Expression<F>,
        spread_p_a1: Expression<F>,
        spread_m_b1: Expression<F>,
        spread_n_b1: Expression<F>,
        spread_o_b1: Expression<F>,
        spread_p_b1: Expression<F>,        
        spread_m_y: Expression<F>,
        spread_n_y: Expression<F>,
        spread_o_y: Expression<F>,
        spread_p_y: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {
        let spread_a1 = spread_m_a1 + spread_n_a1 * F::from(1 << 32) + spread_o_a1 * F::from(1 << 64) + spread_p_a1 * F::from(1 << 96);
        let spread_b1 = spread_m_b1 + spread_n_b1 * F::from(1 << 32) + spread_o_b1 * F::from(1 << 64) + spread_p_b1 * F::from(1 << 96);
        let spread_y = spread_m_y + spread_n_y * F::from(1 << 32) + spread_o_y * F::from(1 << 64) + spread_p_y * F::from(1 << 96);
        let spread_sum = spread_a1 + spread_b1 + spread_y;

        let spread_a2 = spread_m_a2 + spread_n_a2 * F::from(1 << 16) + spread_o_a2 * F::from(1 << 32) + spread_p_a2 * F::from(1 << 48);

        let check = spread_sum - spread_a2;

        Some(("spread_a2", s_spread_a2 * (spread_sum - spread_a2)))
    }


// Sixth gate, xor and bit rotations: Vd2 ← (Vd1 xor Va2) >>> 16
// vector_d1 on abcd words
#[allow(clippy::too_many_arguments)]
pub fn s_spread_d2(
    s_spread_d2: Expression<F>,
    spread_m_d2_even: Expression<F>,
    spread_m_d2_odd: Expression<F>,
    spread_n_d2_even: Expression<F>,
    spread_n_d2_odd: Expression<F>,
    spread_o_d2_even: Expression<F>,
    spread_o_d2_odd: Expression<F>,
    spread_p_d2_even: Expression<F>,
    spread_p_d2_odd: Expression<F>,
    spread_m_a2: Expression<F>,
    spread_n_a2: Expression<F>,
    spread_o_a2: Expression<F>,
    spread_p_a2: Expression<F>,
    spread_m_d1: Expression<F>,
    spread_n_d1: Expression<F>,
    spread_o_d1: Expression<F>,
    spread_p_d1: Expression<F>,
) -> Option<(&'static str, Expression<F>)> {

    let spread_witness = 
           spread_m_d2_even + spread_m_d2_odd * F::from(2)
        + (spread_n_d2_even + spread_n_d2_odd * F::from(2)) * F::from(1 << 32)
        + (spread_o_d2_even + spread_o_d2_odd * F::from(2)) * F::from(1 << 64)
        + (spread_p_d2_even + spread_p_d2_odd * F::from(2)) * F::from(1 << 128);

    let xor_1 = spread_m_a2.clone()
        + spread_n_a2.clone() * F::from(1 << 32)
        + spread_o_a2.clone() * F::from(1 << 64)
        + spread_p_a2.clone() * F::from(1 << 96);

    let xor_2 = spread_m_d1.clone()
        + spread_n_d1.clone() * F::from(1 << 32)
        + spread_o_d1.clone() * F::from(1 << 64)
        + spread_p_d1.clone() * F::from(1 << 96);

    let xor = xor_1 + xor_2;

    let check = spread_witness + (xor * -F::ONE);

    // bit rotation
    let rot = spread_n_a2.clone() + spread_n_d1.clone()
        + (spread_o_a2.clone() + spread_o_d1.clone())* F::from(1 << 32)
        + (spread_p_a2.clone() + spread_p_d1.clone())* F::from(1 << 64)
        + (spread_m_a2.clone() + spread_m_d1.clone())* F::from(1 << 96);

    Some(("spread_d2", s_spread_d2 * check))

}
    


// Seventh gate addition modulo:  Vc2 ← Vc1 + Vd2   no input
#[allow(clippy::too_many_arguments)]
pub fn s_spread_c2(
    s_spread_c2: Expression<F>,
    spread_m_c2: Expression<F>,
    spread_n_c2: Expression<F>,
    spread_o_c2: Expression<F>,
    spread_p_c2: Expression<F>,
    spread_m_c1: Expression<F>,
    spread_n_c1: Expression<F>,
    spread_o_c1: Expression<F>,
    spread_p_c1: Expression<F>,
    spread_m_d2: Expression<F>,
    spread_n_d2: Expression<F>,
    spread_o_d2: Expression<F>,
    spread_p_d2: Expression<F>,        
) -> Option<(&'static str, Expression<F>)> {
    let spread_c1 = spread_m_c1 + spread_n_c1 * F::from(1 << 32) + spread_o_c1 * F::from(1 << 64) + spread_p_c1 * F::from(1 << 96);
    let spread_d2 = spread_m_d2 + spread_n_d2 * F::from(1 << 32) + spread_o_d2 * F::from(1 << 64) + spread_p_d2 * F::from(1 << 96);
    let spread_sum = spread_c1 + spread_d2;

    let spread_c2 = spread_m_c2 + spread_n_c2 * F::from(1 << 32) + spread_o_c2 * F::from(1 << 64) + spread_p_c2 * F::from(1 << 96);

    let check = spread_sum - spread_c2;

    Some(("spread_c2", s_spread_c2 * (spread_sum - spread_c2)))
}

// check if put spread_m_b2_lo_even
// Eight gate: Vb2 ← (Vb1 xor Vc2) >>> 63
// vector_b1 on abcd words
#[allow(clippy::too_many_arguments)]
    pub fn s_spread_b2(
        s_spread_b2: Expression<F>,
        spread_m_b2_even: Expression<F>,
        spread_m_b2_odd: Expression<F>,
        spread_n_b2_even: Expression<F>,
        spread_n_b2_odd: Expression<F>,
        spread_o_b2_even: Expression<F>,
        spread_o_b2_odd: Expression<F>,
        spread_p_b2_even: Expression<F>,
        spread_p_b2_odd: Expression<F>,
        spread_n_c2: Expression<F>,
        spread_m_lo_c2: Expression<F>,
        spread_m_hi_c2: Expression<F>,
        spread_o_c2: Expression<F>,
        spread_p_c2: Expression<F>,
        spread_n_b1: Expression<F>,
        spread_m_lo_b1: Expression<F>,
        spread_m_hi_b1: Expression<F>,
        spread_o_b1: Expression<F>,
        spread_p_b1: Expression<F>,
    ) -> Option<(&'static str, Expression<F>)> {

        let spread_witness = 
               spread_m_b2_even + spread_m_b2_odd * F::from(2)
            + (spread_n_b2_even + spread_n_b2_odd * F::from(2)) * F::from(1 << 32)
            + (spread_o_b2_even + spread_o_b2_odd * F::from(2)) * F::from(1 << 64)
            + (spread_p_b2_even + spread_p_b2_odd * F::from(2)) * F::from(1 << 128);

        let xor_1 = spread_m_lo_c2.clone()
            + spread_m_hi_c2.clone() * F::from(1 << 2)
            + spread_n_c2.clone() * F::from(1 << 32)
            + spread_o_c2.clone() * F::from(1 << 64)
            + spread_p_c2.clone() * F::from(1 << 96);

        let xor_2 = spread_m_lo_b1.clone()
            + spread_m_hi_b1.clone() * F::from(1 << 2)
            + spread_n_b1.clone() * F::from(1 << 32)
            + spread_o_b1.clone() * F::from(1 << 64)
            + spread_p_b1.clone() * F::from(1 << 96);

        let xor = xor_1 + xor_2;

        let check = spread_witness + (xor * -F::ONE);

        // bit rotation
        let rot = spread_m_hi_c2.clone() + spread_m_hi_b1.clone()
            + (spread_n_c2.clone() + spread_n_b1.clone())* F::from(1 << 16)
            + (spread_o_c2.clone() + spread_o_b1.clone())* F::from(1 << 48)
            + (spread_p_c2.clone() + spread_p_b1.clone())* F::from(1 << 80)
            + (spread_m_lo_c2.clone() + spread_m_lo_b1.clone())* F::from(1 << 112) ;

        Some(("spread_b2", s_spread_b2 * check))

    }

// s_digest on final round
#[allow(clippy::too_many_arguments)]
pub fn s_digest(
    s_digest: Expression<F>,
    lo_0: Expression<F>,
    hi_0: Expression<F>,
    word_0: Expression<F>,
    lo_1: Expression<F>,
    hi_1: Expression<F>,
    word_1: Expression<F>,
    lo_2: Expression<F>,
    hi_2: Expression<F>,
    word_2: Expression<F>,
    lo_3: Expression<F>,
    hi_3: Expression<F>,
    word_3: Expression<F>,
) -> impl IntoIterator<Item = Constraint<F>> {
    let check_lo_hi = |lo: Expression<F>, hi: Expression<F>, word: Expression<F>| {
        lo + hi * F::from(1 << 16) - word
    };

    Constraints::with_selector(
        s_digest,
        [
            ("check_lo_hi_0", check_lo_hi(lo_0, hi_0, word_0)),
            ("check_lo_hi_1", check_lo_hi(lo_1, hi_1, word_1)),
            ("check_lo_hi_2", check_lo_hi(lo_2, hi_2, word_2)),
            ("check_lo_hi_3", check_lo_hi(lo_3, hi_3, word_3)),
        ],
    )
}



}

