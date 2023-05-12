// todo why word lo, hi uses without lookup? post on halo2 discord   

// will the spread form handle carry? i think so. in that case keep the calc in spread
// does the carry get added to the e_new value in the next round

// find enable equality copy advice - in table16 add all advice columns to permutation - solved
// The inputs we've been given could be located anywhere in the circuit,
// but we can only rely on relative offsets inside this region. So we
// assign new cells inside the region and constrain them to have the
// same values as the inputs.

// convert addition gates like anew, hprime - in enew how do we constrain dlo dhi
// the final output of gates should be in dense 
// while constraining dense forms by lookup, get spread of final outputs which will be used further 

use super::{
    AbcdVar, CompressionConfig, EfghVar, RoundWord, RoundWordA, RoundWordDense, RoundWordE,
    RoundWordSpread, State, UpperSigmaVar, StateWord, IjklVar,
};
use crate::blake2f::table16::{
    util::*, SpreadVar, SpreadWord, Table16Assignment, AssignedBits, // StateWord
};
use halo2_proofs::{
    circuit::{Region, Value},
    pasta::pallas,
    plonk::{Advice, Column, Error},
};
use std::convert::TryInto;

// Test vector 'abc'
#[cfg(test)]
pub const COMPRESSION_OUTPUT: [u32; 8] = [
    0b10111010011110000001011010111111,
    0b10001111000000011100111111101010,
    0b01000001010000010100000011011110,
    0b01011101101011100010001000100011,
    0b10110000000000110110000110100011,
    0b10010110000101110111101010011100,
    0b10110100000100001111111101100001,
    0b11110010000000000001010110101101,
];

// Rows needed for each gate
pub const SIGMA_0_ROWS: usize = 4;
pub const SIGMA_1_ROWS: usize = 4;
pub const CH_ROWS: usize = 8;
pub const MAJ_ROWS: usize = 4;
pub const DECOMPOSE_ABCD: usize = 2;
pub const DECOMPOSE_EFGH: usize = 2;

// Rows needed for main subregion
pub const SUBREGION_MAIN_LEN: usize = 64;
pub const SUBREGION_MAIN_WORD: usize =
    DECOMPOSE_ABCD + SIGMA_0_ROWS + DECOMPOSE_EFGH + SIGMA_1_ROWS + CH_ROWS + MAJ_ROWS;
pub const SUBREGION_MAIN_ROWS: usize = SUBREGION_MAIN_LEN * SUBREGION_MAIN_WORD;

/// The initial round.
pub struct InitialRound;

/// A main round index.
#[derive(Debug, Copy, Clone)]
pub struct MainRoundIdx(usize);

/// Round index.
#[derive(Debug, Copy, Clone)]
pub enum RoundIdx {
    Init,
    Main(MainRoundIdx),
}

impl From<InitialRound> for RoundIdx {
    fn from(_: InitialRound) -> Self {
        RoundIdx::Init
    }
}

impl From<MainRoundIdx> for RoundIdx {
    fn from(idx: MainRoundIdx) -> Self {
        RoundIdx::Main(idx)
    }
}

impl MainRoundIdx {
    pub(crate) fn as_usize(&self) -> usize {
        self.0
    }
}

impl From<usize> for MainRoundIdx {
    fn from(idx: usize) -> Self {
        MainRoundIdx(idx)
    }
}

impl std::ops::Add<usize> for MainRoundIdx {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        MainRoundIdx(self.0 + rhs)
    }
}

impl Ord for MainRoundIdx {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for MainRoundIdx {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for MainRoundIdx {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for MainRoundIdx {}

/// Returns starting row number of a compression round
pub fn get_round_row(round_idx: RoundIdx) -> usize {
    match round_idx {
        RoundIdx::Init => 0,
        RoundIdx::Main(MainRoundIdx(idx)) => {
            // number of rounds
            assert!(idx < 11);
            idx * SUBREGION_MAIN_WORD
        }
    }
}

// get stateword rows, E row decomposes word into Efgh chunks for initial round
pub fn get_decompose_e_row(round_idx: RoundIdx) -> usize {
    get_round_row(round_idx)
}

// initial round just decomposes into chunks
// assigns row for decomposing F in efgh chunks
pub fn get_decompose_f_row(round_idx: InitialRound) -> usize {
    get_decompose_e_row(round_idx.into()) + DECOMPOSE_EFGH
}

pub fn get_decompose_g_row(round_idx: InitialRound) -> usize {
    get_decompose_f_row(round_idx) + DECOMPOSE_EFGH
}

// get gates rows for main round
pub fn get_upper_sigma_1_row(round_idx: MainRoundIdx) -> usize {
    get_decompose_e_row(round_idx.into()) + DECOMPOSE_EFGH + 1
}

pub fn get_ch_row(round_idx: MainRoundIdx) -> usize {
    get_decompose_e_row(round_idx.into()) + DECOMPOSE_EFGH + SIGMA_1_ROWS + 1
}

pub fn get_ch_neg_row(round_idx: MainRoundIdx) -> usize {
    get_ch_row(round_idx) + CH_ROWS / 2
}

pub fn get_decompose_a_row(round_idx: RoundIdx) -> usize {
    match round_idx {
        RoundIdx::Init => get_h_row(round_idx) + DECOMPOSE_EFGH,
        RoundIdx::Main(mri) => get_ch_neg_row(mri) - 1 + CH_ROWS / 2,
    }
}

pub fn get_upper_sigma_0_row(round_idx: MainRoundIdx) -> usize {
    get_decompose_a_row(round_idx.into()) + DECOMPOSE_ABCD + 1
}

pub fn get_decompose_b_row(round_idx: InitialRound) -> usize {
    get_decompose_a_row(round_idx.into()) + DECOMPOSE_ABCD
}

pub fn get_decompose_c_row(round_idx: InitialRound) -> usize {
    get_decompose_b_row(round_idx) + DECOMPOSE_ABCD
}

pub fn get_maj_row(round_idx: MainRoundIdx) -> usize {
    get_upper_sigma_0_row(round_idx) + SIGMA_0_ROWS
}

// Get state word rows
pub fn get_h_row(round_idx: RoundIdx) -> usize {
    match round_idx {
        RoundIdx::Init => get_decompose_g_row(InitialRound) + DECOMPOSE_EFGH,
        RoundIdx::Main(mri) => get_ch_row(mri) - 1,
    }
}

pub fn get_h_prime_row(round_idx: MainRoundIdx) -> usize {
    get_ch_row(round_idx)
}

pub fn get_d_row(round_idx: RoundIdx) -> usize {
    match round_idx {
        RoundIdx::Init => get_decompose_c_row(InitialRound) + DECOMPOSE_ABCD,
        RoundIdx::Main(mri) => get_ch_row(mri) + 2,
    }
}

// e_new requires h_prime too but i think after h_prime is assigned just copy advice
pub fn get_e_new_row(round_idx: MainRoundIdx) -> usize {
    get_d_row(round_idx.into())
}

pub fn get_a_new_row(round_idx: MainRoundIdx) -> usize {
    get_maj_row(round_idx)
}

pub fn get_digest_abcd_row() -> usize {
    SUBREGION_MAIN_ROWS
}

pub fn get_digest_efgh_row() -> usize {
    get_digest_abcd_row() + 2
}

impl CompressionConfig {
    pub(super) fn decompose_abcd(
        &self,
        region: &mut Region<'_, pallas::Base>,
        row: usize,
        val: Value<u64>,
    ) -> Result<AbcdVar, Error> {
        self.s_decompose_abcd.enable(region, row)?;

        let spread_pieces = val.map(AbcdVar::pieces);
        // todo is length 4 related to # of constraints 
        let spread_pieces = spread_pieces.transpose_vec(1);

        let a = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row - 1,
            spread_pieces[0].clone().map(SpreadWord::try_new),
        )?;
        let b = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row,
            spread_pieces[1].clone().map(SpreadWord::try_new),
        )?;
        let c = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row + 1,
            spread_pieces[2].clone().map(SpreadWord::try_new),
        )?;
        let d = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row + 2,
            spread_pieces[3].clone().map(SpreadWord::try_new),
        )?;

        Ok(AbcdVar {
            a,
            b,
            c,
            d,
        })
    }

    pub(super) fn decompose_efgh(
        &self,
        region: &mut Region<'_, pallas::Base>,
        row: usize,
        val: Value<u64>,
    ) -> Result<EfghVar, Error> {

        // selector is just enforcing the conditional constraint for dense and spread check?
        self.s_decompose_efgh.enable(region, row)?;

        let spread_pieces = val.map(EfghVar::pieces);
        let spread_pieces = spread_pieces.transpose_vec(6);

        let a = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row - 1,
            spread_pieces[0].clone().map(SpreadWord::try_new),
        )?;
        let b_lo = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row,
            spread_pieces[1].clone().map(SpreadWord::try_new),
        )?;
        let b_hi = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row+1,
            spread_pieces[2].clone().map(SpreadWord::try_new),
        )?;
        let c = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row + 2,
            spread_pieces[3].clone().map(SpreadWord::try_new),
        )?;
        let d = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row+3,
            spread_pieces[4].clone().map(SpreadWord::try_new),
        )?;

        Ok(EfghVar {
            a,
            b_lo,
            b_hi,
            c,
            d,
        })
    }

    pub(super) fn decompose_ijkl(
        &self,
        region: &mut Region<'_, pallas::Base>,
        row: usize,
        val: Value<u64>,
    ) -> Result<IjklVar, Error> {
        self.s_decompose_ijkl.enable(region, row)?;

        let spread_pieces = val.map(IjklVar::pieces);
        let spread_pieces = spread_pieces.transpose_vec(6);

        let a = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row,
            spread_pieces[0].clone().map(SpreadWord::try_new),
        )?;
        let b = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row + 1,
            spread_pieces[1].clone().map(SpreadWord::try_new),
        )?;
        let c = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row + 1,
            spread_pieces[2].clone().map(SpreadWord::try_new),
        )?;
        let d_lo = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row,
            spread_pieces[3].clone().map(SpreadWord::try_new),
        )?;
        let d_hi = SpreadVar::with_lookup(
            region,
            &self.lookup,
            row,
            spread_pieces[4].clone().map(SpreadWord::try_new),
        )?;

        Ok(IjklVar {
            a,
            b,
            c,
            d_lo,
            d_hi,
        })
    }

    // result is passed to roundworda
    pub(super) fn decompose_a(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: RoundIdx,
        a_val: Value<u64>,
    ) -> Result<RoundWordA, Error> {
        let row = get_decompose_a_row(round_idx);

        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, a_val)?;
        let a_pieces = self.decompose_abcd(region, row, a_val)?;
        Ok(RoundWordA::new(a_pieces, dense_halves, spread_halves))
    }

    pub(super) fn decompose_e(
        &self,  
        region: &mut Region<'_, pallas::Base>,
        round_idx: RoundIdx,
        e_val: Value<u64>,
    ) -> Result<RoundWordE, Error> {
        let row = get_decompose_e_row(round_idx);

        let (dense_halves, spread_halves) = self.assign_word_halves(region, row, e_val)?;
        let e_pieces = self.decompose_efgh(region, row, e_val)?;
        Ok(RoundWordE::new(e_pieces, dense_halves, spread_halves))
    }


// gates only take spread values
    pub(super) fn assign_a1(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: MainRoundIdx,
        vector_a: &RoundWordDense,
        vector_b: &RoundWordDense,
        message_x: &RoundWordDense,
    ) -> Result<RoundWordDense, Error> {
        // Rename these here for ease of matching the gates to the specification.
        let a_1 = self.lookup.dense;
        let a_3 = self.extras[0];
        let a_4 = self.extras[1];
        let a_5 = self.extras[2];
        let a_6 = self.extras[3];

        let row = get_a1_row(round_idx);

        self.s_vector_a1.enable(region, row)?;

        // Assign and copy a
        vector_a.0.copy_advice(|| "vector_a_lo", region, a_3, row - 1 )?;
        vector_a.1.copy_advice(|| "vector_a_mo", region, a_3, row)?;
        vector_a.2.copy_advice(|| "vector_a_el", region, a_3, row + 1)?;
        vector_a.3.copy_advice(|| "vector_a_hi", region, a_3, row + 2)?;

        // Assign and copy d_lo, d_hi
        vector_b.0.copy_advice(|| "vector_b_lo", region, a_4, row - 1)?;
        vector_b.1.copy_advice(|| "vector_b_mo", region, a_4, row)?;
        vector_b.2.copy_advice(|| "vector_b_el", region, a_4, row + 1)?;
        vector_b.3.copy_advice(|| "vector_b_hi", region, a_4, row + 2)?;


        // Assign and copy d_lo, d_hi
        message_x.0.copy_advice(|| "message_x_lo", region, a_5, row - 1)?;
        message_x.1.copy_advice(|| "message_x_mo", region, a_5, row)?;
        message_x.2.copy_advice(|| "message_x_el", region, a_5, row + 1)?;
        message_x.3.copy_advice(|| "message_x_hi", region, a_5, row + 2)?;

        // Assign a1, a1_carry
        let (vector_a1, vector_a1_carry) = sum_with_carry(vec![
            (vector_a.0.value_u16(), vector_a.1.value_u16(),vector_a.2.value_u16(), vector_a.3.value_u16()),
            (vector_b.0.value_u16(), vector_b.1.value_u16(),vector_b.2.value_u16(), vector_b.3.value_u16()),
            (message_x.0.value_u16(), message_x.1.value_u16(),message_x.2.value_u16(), message_x.3.value_u16()),

        ]);
        
        let vector_a1_dense = self.assign_word_halves_dense(region, row-1, a_1, 
            row, a_1,row+1, a_1,row+2, a_1, vector_a1)?;

        region.assign_advice(
            || "vector_a1_carry",
            a_3,
            row - 1,
            || vector_a1_carry.map(pallas::Base::from),
        )?;

        Ok(vector_a1_dense)

    }


    pub(super) fn assign_d1(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: MainRoundIdx,
        vector_a1: AbcdVar,
    ) -> Result<(AssignedBits<16>, AssignedBits<16>), Error> {
        // Rename these here for ease of matching the gates to the specification.
        let a_3 = self.extras[0];
        let a_4 = self.extras[1];
        let a_5 = self.message_schedule;

        let row = get_vector_d1_row(round_idx);

        self.s_vector_d1.enable(region, row)?;

        // Assign `spread_a` and copy constraint
        vector_a1.m
            .spread
            .copy_advice(|| "spread_a", region, a_4, row - 1)?;

        // Assign `spread_b` and copy constraint
        vector_a1.n
            .spread
            .copy_advice(|| "spread_b", region, a_4, row)?;

        // Assign `spread_c` and copy constraint
        vector_a1.o
            .spread
            .copy_advice(|| "spread_c", region, a_5, row + 1)?;

        // Assign `spread_d` and copy constraint
        vector_a1.p
            .spread
            .copy_advice(|| "spread_d", region, a_4, row + 2)?;

        // Calculate R_0^{even}, R_0^{odd}, R_1^{even}, R_1^{odd}
        // Calculate R_0^{even}, R_0^{odd}, R_1^{even}, R_1^{odd}
        let r = vector_a1.xor_upper_sigma();
        let r_0: Value<[bool; 32]> = r.map(|r| r[..32].try_into().unwrap());
        let r_0_even = r_0.map(even_bits);
        let r_0_odd = r_0.map(odd_bits);

        let r_1: Value<[bool; 32]> = r.map(|r| r[32..].try_into().unwrap());
        let r_1_even = r_1.map(even_bits);
        let r_1_odd = r_1.map(odd_bits);

        self.assign_sigma_outputs(
            region,
            &self.lookup,
            a_3,
            row,
            r_0_even,
            r_0_odd,
            r_1_even,
            r_1_odd,
        )
    }

    fn assign_c1_outputs(
        &self,
        region: &mut Region<'_, pallas::Base>,
        row: usize,
        spread_m_c1: Value<[bool; 32]>,
        spread_n_c1: Value<[bool; 32]>,
        spread_o_c1: Value<[bool; 32]>,
        spread_p_c1: Value<[bool; 32]>,
    ) -> Result<(
            AssignedBits<32>, AssignedBits<32>,
            AssignedBits<32>, AssignedBits<32>,
    ), Error> {
        let a_3 = self.extras[0];
        let (even, odd) = self.assign_spread_outputs(
            region,
            &self.lookup,
            a_3,
            row,
            spread_m_c1,
            spread_n_c1,
            spread_o_c1,
            spread_p_c1,
        )?;

        // Mi_odd is the function output
        Ok(odd)
    }

// gates only take spread values
pub(super) fn assign_c1(
    &self,
    region: &mut Region<'_, pallas::Base>,
    round_idx: MainRoundIdx,
    vector_c: &RoundWordDense,
    vector_d1: &RoundWordDense,
) -> Result<RoundWordDense, Error> {
    // Rename these here for ease of matching the gates to the specification.
    let a_1 = self.lookup.dense;
    let a_3 = self.extras[0];
    let a_4 = self.extras[1];
    let a_5 = self.extras[2];
    let a_6 = self.extras[3];

    let row = get_upper_sigma_0_row(round_idx);

    self.s_vector_c1.enable(region, row)?;

    // Assign and copy a
    vector_c.0.copy_advice(|| "vector_c_lo", region, a_3, row - 1 )?;
    vector_c.1.copy_advice(|| "vector_c_mo", region, a_3, row)?;
    vector_c.2.copy_advice(|| "vector_c_el", region, a_3, row + 1)?;
    vector_c.3.copy_advice(|| "vector_c_hi", region, a_3, row + 2)?;

    // Assign and copy d_lo, d_hi
    vector_d1.0.copy_advice(|| "vector_d1_lo", region, a_4, row - 1)?;
    vector_d1.1.copy_advice(|| "vector_d1_mo", region, a_4, row)?;
    vector_d1.2.copy_advice(|| "vector_d1_el", region, a_4, row + 1)?;
    vector_d1.3.copy_advice(|| "vector_d1_hi", region, a_4, row + 2)?;


    // Assign c1, c1_carry
    let (vector_c1, vector_c1_carry) = sum_with_carry(vec![
        (vector_c.0.value_u16(), vector_c.1.value_u16(),vector_c.2.value_u16(), vector_c.3.value_u16()),
        (vector_d1.0.value_u16(), vector_d1.1.value_u16(),vector_d1.2.value_u16(), vector_d1.3.value_u16()),

    ]);
    
    let vector_c1_dense = self.assign_word_halves_dense(region, row-1, a_1, 
        row, a_1,row+1, a_1,row+2, a_1, vector_c1)?;

    region.assign_advice(
        || "vector_c1_carry",
        a_3,
        row - 1,
        || vector_c1_carry.map(pallas::Base::from),
    )?;

    Ok(vector_c1_dense)

}


    pub(super) fn assign_ch_neg(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: MainRoundIdx,
        spread_halves_e: RoundWordSpread,
        spread_halves_g: RoundWordSpread,
    ) -> Result<(AssignedBits<16>, AssignedBits<16>), Error> {
        let row = get_ch_neg_row(round_idx);

        self.s_ch_neg.enable(region, row)?;

        let a_3 = self.extras[0];
        let a_4 = self.extras[1];
        let a_5 = self.message_schedule;

        // Assign and copy spread_e_lo, spread_e_hi
        spread_halves_e
            .0
            .copy_advice(|| "spread_e_lo", region, a_5, row - 1)?;
        spread_halves_e
            .1
            .copy_advice(|| "spread_e_hi", region, a_5, row)?;

        // Assign and copy spread_g_lo, spread_g_hi
        spread_halves_g
            .0
            .copy_advice(|| "spread_g_lo", region, a_3, row + 1)?;
        spread_halves_g
            .1
            .copy_advice(|| "spread_g_hi", region, a_4, row + 1)?;

        // Calculate neg_e_lo
        let spread_neg_e_lo = spread_halves_e
            .0
            .value()
            .map(|spread_e_lo| negate_spread(spread_e_lo.0));
        // Assign spread_neg_e_lo
        AssignedBits::<32>::assign_bits(
            region,
            || "spread_neg_e_lo",
            a_3,
            row - 1,
            spread_neg_e_lo,
        )?;

        // Calculate neg_e_hi
        let spread_neg_e_hi = spread_halves_e
            .1
            .value()
            .map(|spread_e_hi| negate_spread(spread_e_hi.0));
        // Assign spread_neg_e_hi
        AssignedBits::<32>::assign_bits(
            region,
            || "spread_neg_e_hi",
            a_4,
            row - 1,
            spread_neg_e_hi,
        )?;

        let p: Value<[bool; 64]> = {
            let spread_neg_e = spread_neg_e_lo
                .zip(spread_neg_e_hi)
                .map(|(lo, hi)| lebs2ip(&lo) + (1 << 32) * lebs2ip(&hi));
            spread_neg_e
                .zip(spread_halves_g.value())
                .map(|(neg_e, g)| i2lebsp(neg_e + g))
        };

        let p_0: Value<[bool; 32]> = p.map(|p| p[..32].try_into().unwrap());
        let p_0_even = p_0.map(even_bits);
        let p_0_odd = p_0.map(odd_bits);

        let p_1: Value<[bool; 32]> = p.map(|p| p[32..].try_into().unwrap());
        let p_1_even = p_1.map(even_bits);
        let p_1_odd = p_1.map(odd_bits);

        self.assign_ch_outputs(region, row, p_0_even, p_0_odd, p_1_even, p_1_odd)
    }


    // s_h_prime to get H' = H + Ch(E, F, G) + s_upper_sigma_1(E) + K + W
    #[allow(clippy::too_many_arguments)]
    pub(super) fn assign_h_prime(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: MainRoundIdx,
        h: RoundWordDense,
        ch: (AssignedBits<16>, AssignedBits<16>),
        ch_neg: (AssignedBits<16>, AssignedBits<16>),
        sigma_1: (AssignedBits<16>, AssignedBits<16>),
        k: u32,
        w: &(AssignedBits<16>, AssignedBits<16>),
    ) -> Result<RoundWordDense, Error> {
        let row = get_h_prime_row(round_idx);
        self.s_h_prime.enable(region, row)?;

        let a_4 = self.extras[1];
        let a_5 = self.message_schedule;
        let a_6 = self.extras[2];
        let a_7 = self.extras[3];
        let a_8 = self.extras[4];
        let a_9 = self.extras[5];

        // Assign and copy h
        h.0.copy_advice(|| "h_lo", region, a_7, row - 1)?;
        h.1.copy_advice(|| "h_hi", region, a_7, row)?;

        // Assign and copy sigma_1
        sigma_1.0.copy_advice(|| "sigma_1_lo", region, a_4, row)?;
        sigma_1.1.copy_advice(|| "sigma_1_hi", region, a_5, row)?;

        // Assign k
        let k: [bool; 32] = i2lebsp(k.into());
        let k_lo: [bool; 16] = k[..16].try_into().unwrap();
        let k_hi: [bool; 16] = k[16..].try_into().unwrap();
        {
            AssignedBits::<16>::assign_bits(region, || "k_lo", a_6, row - 1, Value::known(k_lo))?;
            AssignedBits::<16>::assign_bits(region, || "k_hi", a_6, row, Value::known(k_hi))?;
        }

        // Assign and copy w
        w.0.copy_advice(|| "w_lo", region, a_8, row - 1)?;
        w.1.copy_advice(|| "w_hi", region, a_8, row)?;

        // Assign and copy ch
        ch.1.copy_advice(|| "ch_neg_hi", region, a_6, row + 1)?;

        // Assign and copy ch_neg
        ch_neg.0.copy_advice(|| "ch_neg_lo", region, a_5, row - 1)?;
        ch_neg.1.copy_advice(|| "ch_neg_hi", region, a_5, row + 1)?;

        // Assign h_prime_lo, h_prime_hi, h_prime_carry
        {
            let (h_prime, h_prime_carry) = sum_with_carry(vec![
                (h.0.value_u16(), h.1.value_u16()),
                (ch.0.value_u16(), ch.1.value_u16()),
                (ch_neg.0.value_u16(), ch_neg.1.value_u16()),
                (sigma_1.0.value_u16(), sigma_1.1.value_u16()),
                (
                    Value::known(lebs2ip(&k_lo) as u16),
                    Value::known(lebs2ip(&k_hi) as u16),
                ),
                (w.0.value_u16(), w.1.value_u16()),
            ]);

            region.assign_advice(
                || "h_prime_carry",
                a_9,
                row + 1,
                || h_prime_carry.map(pallas::Base::from),
            )?;

            let h_prime: Value<[bool; 32]> = h_prime.map(|w| i2lebsp(w.into()));
            let h_prime_lo: Value<[bool; 16]> = h_prime.map(|w| w[..16].try_into().unwrap());
            let h_prime_hi: Value<[bool; 16]> = h_prime.map(|w| w[16..].try_into().unwrap());

            let h_prime_lo =
                AssignedBits::<16>::assign_bits(region, || "h_prime_lo", a_7, row + 1, h_prime_lo)?;
            let h_prime_hi =
                AssignedBits::<16>::assign_bits(region, || "h_prime_hi", a_8, row + 1, h_prime_hi)?;

            Ok((h_prime_lo, h_prime_hi).into())
        }
    }

    pub(super) fn assign_c2(
        &self,
        region: &mut Region<'_, pallas::Base>,
        round_idx: MainRoundIdx,
        spread_halves_a: RoundWordSpread,
        spread_halves_b: RoundWordSpread,
    ) -> Result<(AssignedBits<32>, AssignedBits<32>), Error> {
        let a_4 = self.extras[1];
        let a_5 = self.message_schedule;
        let a_6 = self.extras[2];
        let a_7 = self.extras[3];

        let row = get_c2_row(round_idx);

        self.s_spread_c2.enable(region, row)?;

        // Assign and copy spread_a_lo, spread_a_hi
        spread_halves_a
            .0
            .copy_advice(|| "spread_m_a", region, a_4, row - 1)?;
        spread_halves_a
            .1
            .copy_advice(|| "spread_n_a", region, a_5, row - 1)?;
        spread_halves_a
            .2
            .copy_advice(|| "spread_o_a", region, a_6, row - 1)?;
        spread_halves_a
            .3
            .copy_advice(|| "spread_p_a", region, a_7, row - 1)?;


        // Assign and copy spread_b_lo, spread_b_hi
        spread_halves_b
            .0
            .copy_advice(|| "spread_m_b", region, a_4, row)?;
        spread_halves_b
            .1
            .copy_advice(|| "spread_n_b", region, a_5, row)?;
        spread_halves_b
            .2
            .copy_advice(|| "spread_o_b", region, a_6, row)?;
        spread_halves_b
            .3
            .copy_advice(|| "spread_p_b", region, a_7, row)?;

        // might have to change u64 to u128
        let m: Value<[bool; 128]> = spread_halves_a
            .value()
            .zip(spread_halves_b.value())
            .map(|(a, b)| i2lebsp(a + b));

        let m_0: Value<[bool; 64]> = m.map(|m| m[..64].try_into().unwrap());
        let m_0_even = m_0.map(even_bits);
        let m_0_odd = m_0.map(odd_bits);

        let m_1: Value<[bool; 64]> = m.map(|m| m[64..].try_into().unwrap());
        let m_1_even = m_1.map(even_bits);
        let m_1_odd = m_1.map(odd_bits);

        self.assign_c2_outputs(region, row, m_0_even, m_0_odd, m_1_even, m_1_odd)
    }




    pub fn assign_word_halves_dense(
        &self,
        region: &mut Region<'_, pallas::Base>,
        lo_row: usize,
        lo_col: Column<Advice>,
        mo_row: usize,
        mo_col: Column<Advice>,
        el_row: usize,
        el_col: Column<Advice>,
        hi_row: usize,
        hi_col: Column<Advice>,
        word: Value<u64>,
    ) -> Result<RoundWordDense, Error> {
        let word: Value<[bool; 64]> = word.map(|w| i2lebsp(w.into()));

        let lo = {
            let lo: Value<[bool; 16]> = word.map(|w| w[..16].try_into().unwrap());
            AssignedBits::<16>::assign_bits(region, || "lo", lo_col, lo_row, lo)?
        };

        let mo = {
            let mo: Value<[bool; 16]> = word.map(|w| w[16..32].try_into().unwrap());
            AssignedBits::<16>::assign_bits(region, || "mo", mo_col, mo_row, mo)?
        };

        let el = {
            let el: Value<[bool; 16]> = word.map(|w| w[32..48].try_into().unwrap());
            AssignedBits::<16>::assign_bits(region, || "el", el_col, el_row, el)?
        };

        let hi = {
            let hi: Value<[bool; 16]> = word.map(|w| w[48..].try_into().unwrap());
            AssignedBits::<16>::assign_bits(region, || "hi", hi_col, hi_row, hi)?
        };

        Ok((lo, mo, el, hi).into())
    }

    // Assign hi and lo halves for both dense and spread versions of a word
    #[allow(clippy::type_complexity)]
    pub fn assign_word_halves(
        &self,
        region: &mut Region<'_, pallas::Base>,
        row: usize,
        word: Value<u64>,
    ) -> Result<(RoundWordDense, RoundWordSpread), Error> {
        // Rename these here for ease of matching the gates to the specification.
        let a_7 = self.extras[3];
        let a_8 = self.extras[4];

        let word: Value<[bool; 32]> = word.map(|w| i2lebsp(w.into()));

        let lo: Value<[bool; 16]> = word.map(|w| w[..16].try_into().unwrap());
        let mo: Value<[bool; 16]> = word.map(|w| w[16..32].try_into().unwrap());
        let el: Value<[bool; 16]> = word.map(|w| w[32..48].try_into().unwrap());
        let hi: Value<[bool; 16]> = word.map(|w| w[48..].try_into().unwrap());
        

        let w_lo = SpreadVar::without_lookup(region, a_7, row, a_8, row, lo.map(SpreadWord::new))?;
        let w_mo = SpreadVar::without_lookup(region, a_7, row + 1, a_8, row + 1, mo.map(SpreadWord::new))?;
        let w_el = SpreadVar::without_lookup(region, a_7, row + 2, a_8, row + 1, el.map(SpreadWord::new))?;
        let w_hi = SpreadVar::without_lookup(region, a_7, row + 3, a_8, row + 1, hi.map(SpreadWord::new))?;

        Ok((
            (w_lo.dense, w_mo.dense, w_el.dense, w_hi.dense).into(),
            (w_lo.spread, w_mo.dense, w_el.dense, w_hi.spread).into(),
        ))
    }
}

#[allow(clippy::many_single_char_names)]
pub fn match_state(
    state: State,
) -> (
    RoundWordA,
    RoundWord,
    RoundWord,
    RoundWordDense,
    RoundWordE,
    RoundWord,
    RoundWord,
    RoundWordDense,
) {
    let a = match state.a {
        Some(StateWord::A(a)) => a,
        _ => unreachable!(),
    };
    let b = match state.b {
        Some(StateWord::B(b)) => b,
        _ => unreachable!(),
    };
    let c = match state.c {
        Some(StateWord::C(c)) => c,
        _ => unreachable!(),
    };
    let d = match state.d {
        Some(StateWord::D(d)) => d,
        _ => unreachable!(),
    };
    let e = match state.e {
        Some(StateWord::E(e)) => e,
        _ => unreachable!(),
    };
    let f = match state.f {
        Some(StateWord::F(f)) => f,
        _ => unreachable!(),
    };
    let g = match state.g {
        Some(StateWord::G(g)) => g,
        _ => unreachable!(),
    };
    let h = match state.h {
        Some(StateWord::H(h)) => h,
        _ => unreachable!(),
    };

    (a, b, c, d, e, f, g, h)
}
