//use crate::blake2f_circuit::blake2f::table16::util::{spread_bits, lebs2ip, i2lebsp};
//use super::util::{spread_bits, lebs2ip, i2lebsp};

//use crate::blake2f::table16::util::{spread_bits, lebs2ip, i2lebsp}; //table16::AssignedBits
use group::ff::{Field, PrimeField};

use halo2_proofs::{
    circuit::{Chip, Layouter, Region, Value, AssignedCell},
    pasta::pallas,
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn, Any, Assigned},
    poly::Rotation,
};
use std::convert::TryInto;
use std::marker::PhantomData;

use super::{util::{spread_bits, lebs2ip, i2lebsp}, compression::RoundWordSpread, AssignedBits};

use super::{util::*};

/// Little-endian bits (up to 64 bits)
/// 
/* 
pub struct Bits<const LEN: usize>([bool; LEN]);

impl<const LEN: usize> Bits<LEN> {
    fn spread<const SPREAD: usize>(&self) -> [bool; SPREAD] {
        spread_bits(self.0)
    }
}

impl<const LEN: usize> std::ops::Deref for Bits<LEN> {
    type Target = [bool; LEN];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const LEN: usize> From<[bool; LEN]> for Bits<LEN> {
    fn from(bits: [bool; LEN]) -> Self {
        Self(bits)
    }
}

impl<const LEN: usize> From<&Bits<LEN>> for [bool; LEN] {
    fn from(bits: &Bits<LEN>) -> Self {
        bits.0
    }
}

impl<const LEN: usize> From<&Bits<LEN>> for Assigned<pallas::Base> {
    fn from(bits: &Bits<LEN>) -> Assigned<pallas::Base> {
        assert!(LEN <= 64);
        pallas::Base::from(lebs2ip(&bits.0)).into()
    }
}

impl From<&Bits<16>> for u16 {
    fn from(bits: &Bits<16>) -> u16 {
        lebs2ip(&bits.0) as u16
    }
}

impl From<u16> for Bits<16> {
    fn from(int: u16) -> Bits<16> {
        Bits(i2lebsp::<16>(int.into()))
    }
}

impl From<&Bits<32>> for u32 {
    fn from(bits: &Bits<32>) -> u32 {
        lebs2ip(&bits.0) as u32
    }
}

impl From<u32> for Bits<32> {
    fn from(int: u32) -> Bits<32> {
        Bits(i2lebsp::<32>(int.into()))
    }
}

#[derive(Clone, Debug)]
pub struct AssignedBits<const LEN: usize>(AssignedCell<Bits<LEN>, pallas::Base>);

impl<const LEN: usize> std::ops::Deref for AssignedBits<LEN> {
    type Target = AssignedCell<Bits<LEN>, pallas::Base>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const LEN: usize> AssignedBits<LEN> {
    fn assign_bits<A, AR, T: TryInto<[bool; LEN]> + std::fmt::Debug + Clone>(
        region: &mut Region<'_, pallas::Base>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<T>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
        <T as TryInto<[bool; LEN]>>::Error: std::fmt::Debug,
    {
        let value: Value<[bool; LEN]> = value.map(|v| v.try_into().unwrap());
        let value: Value<Bits<LEN>> = value.map(|v| v.into());

        let column: Column<Any> = column.into();
        match column.column_type() {
            Any::Advice => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

impl AssignedBits<16> {
    fn value_u16(&self) -> Value<u16> {
        self.value().map(|v| v.into())
    }

    fn assign<A, AR>(
        region: &mut Region<'_, pallas::Base>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<u16>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        let column: Column<Any> = column.into();
        let value: Value<Bits<16>> = value.map(|v| v.into());
        match column.column_type() {
            Any::Advice => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

impl AssignedBits<32> {
    fn value_u32(&self) -> Value<u32> {
        self.value().map(|v| v.into())
    }

    fn assign<A, AR>(
        region: &mut Region<'_, pallas::Base>,
        annotation: A,
        column: impl Into<Column<Any>>,
        offset: usize,
        value: Value<u32>,
    ) -> Result<Self, Error>
    where
        A: Fn() -> AR,
        AR: Into<String>,
    {
        let column: Column<Any> = column.into();
        let value: Value<Bits<32>> = value.map(|v| v.into());
        match column.column_type() {
            Any::Advice => {
                region.assign_advice(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            Any::Fixed => {
                region.assign_fixed(annotation, column.try_into().unwrap(), offset, || {
                    value.clone()
                })
            }
            _ => panic!("Cannot assign to instance column"),
        }
        .map(AssignedBits)
    }
}

*/
//use pasta_curves::pallas;


const BITS_8: usize = 1 << 8;
const BITS_15: usize = 1 << 15;

/// An input word into a lookup, containing (tag, dense, spread)
#[derive(Copy, Clone, Debug)]
pub(crate) struct SpreadWord<const DENSE: usize, const SPREAD: usize> {
    pub tag: u8,
    pub dense: [bool; DENSE],
    pub spread: [bool; SPREAD],
}

/// Helper function that returns tag of 16-bit input
pub fn get_tag(input: u16) -> u8 {
    let input = input as usize;
    if input < BITS_8 {
        0
    } else if input<BITS_15{
        1
    } else {
        2
    }
}

impl<const DENSE: usize, const SPREAD: usize> SpreadWord<DENSE, SPREAD> {
    pub(super) fn new(dense: [bool; DENSE]) -> Self {
        assert!(DENSE <= 16);
        SpreadWord {
            tag: get_tag(lebs2ip(&dense) as u16),
            dense,
            spread: spread_bits(dense),
        }
    }

    pub(super) fn try_new<T: TryInto<[bool; DENSE]> + std::fmt::Debug>(dense: T) -> Self
    where
        <T as TryInto<[bool; DENSE]>>::Error: std::fmt::Debug,
    {
        assert!(DENSE <= 16);
        let dense: [bool; DENSE] = dense.try_into().unwrap();
        SpreadWord {
            tag: get_tag(lebs2ip(&dense) as u16),
            dense,
            spread: spread_bits(dense),
        }
    }
}

/// A variable stored in advice columns corresponding to a row of [`SpreadTableConfig`].
#[derive(Clone, Debug)]
pub(crate) struct SpreadVar<const DENSE: usize, const SPREAD: usize> {
    pub _tag: Value<u8>,
    pub dense: AssignedBits<DENSE>,
    pub spread: AssignedBits<SPREAD>,
}

impl<const DENSE: usize, const SPREAD: usize> SpreadVar<DENSE, SPREAD> {
    pub(super) fn with_lookup(
        region: &mut Region<'_, pallas::Base>,
        cols: &SpreadInputs,
        row: usize,
        word: Value<SpreadWord<DENSE, SPREAD>>,
    ) -> Result<Self, Error> {
        let tag = word.map(|word| word.tag);
        let dense_val = word.map(|word| word.dense);
        let spread_val = word.map(|word| word.spread);

        region.assign_advice(
            || "tag",
            cols.tag,
            row,
            || tag.map(|tag| pallas::Base::from(tag as u64)),
        )?;

        let dense =
            AssignedBits::<DENSE>::assign_bits(region, || "dense", cols.dense, row, dense_val)?;

        let spread =
            AssignedBits::<SPREAD>::assign_bits(region, || "spread", cols.spread, row, spread_val)?;

        Ok(SpreadVar {
            _tag: tag,
            dense,
            spread,
        })
    }

    pub(super) fn without_lookup(
        region: &mut Region<'_, pallas::Base>,
        dense_col: Column<Advice>,
        dense_row: usize,
        spread_col: Column<Advice>,
        spread_row: usize,
        word: Value<SpreadWord<DENSE, SPREAD>>,
    ) -> Result<Self, Error> {
        let tag = word.map(|word| word.tag);
        let dense_val = word.map(|word| word.dense);
        let spread_val = word.map(|word| word.spread);

        let dense = AssignedBits::<DENSE>::assign_bits(
            region,
            || "dense",
            dense_col,
            dense_row,
            dense_val,
        )?;

        let spread = AssignedBits::<SPREAD>::assign_bits(
            region,
            || "spread",
            spread_col,
            spread_row,
            spread_val,
        )?;

        Ok(SpreadVar {
            _tag: tag,
            dense,
            spread,
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SpreadInputs {
    pub(super) tag: Column<Advice>,
    pub(super) dense: Column<Advice>,
    pub(super) spread: Column<Advice>,
}

#[derive(Clone, Debug)]
pub(crate) struct SpreadTable {
    pub(super) tag: TableColumn,
    pub(super) dense: TableColumn,
    pub(super) spread: TableColumn,
}

 // Configuration for a [`Table16Chip`].
 #[derive(Clone, Debug)]
 pub struct XorConfig {
    lookup: SpreadTableConfig,
    
 }


#[derive(Clone, Debug)]
pub(crate) struct SpreadTableConfig {
    pub input: SpreadInputs,
    pub table: SpreadTable,
}

#[derive(Clone, Debug)]
pub(crate) struct SpreadTableChip<F: Field> {
    config: SpreadTableConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> Chip<F> for SpreadTableChip<F>{
    type Config = SpreadTableConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

trait SpreadTableAssignment {
    /// Assign cells for general spread computation used in sigma, ch, ch_neg, maj gates
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
fn assign_spread_outputs(
    &self,
    region: &mut Region<'_, pallas::Base>,
    lookup: &SpreadInputs,
    a_3: Column<Advice>,
    row: usize,
    r_0: Value<[bool; 16]>,
    r_1: Value<[bool; 16]>,
    r_2: Value<[bool; 16]>,
) -> Result<
    (
        (AssignedBits<16>, AssignedBits<16>, AssignedBits<16>),
    ),
    Error,
> {
    // Lookup R_0^{even}, R_0^{odd}, R_1^{even}, R_1^{odd}
    let r_0 = SpreadVar::with_lookup(
        region,
        lookup,
        row - 1,
        r_0.map(SpreadWord::<16, 32>::new),
    )?;
    let r_1 =
        SpreadVar::with_lookup(
            region,
            lookup,
            row,
            r_1.map(SpreadWord::<16, 32>::new))?;


    let r_2 = SpreadVar::with_lookup(
            region,
            lookup,
            row + 2,
            r_2.map(SpreadWord::<16, 32>::new))?;

    // Assign and copy R_1^{odd}
    r_2
        .spread
        .copy_advice(|| "Assign and copy R_1^{odd}", region, a_3, row)?;

    Ok((
        (r_0.dense, r_1.dense, r_2.dense),
    ))
}
}



impl <F: PrimeField> SpreadTableChip<F>  {
    /// Configures a circuit to include this chip.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        input_tag: Column<Advice>,
        input_dense: Column<Advice>,
        input_spread: Column<Advice>,
    ) -> <Self as Chip<F>>::Config {
        let table_tag = meta.lookup_table_column();
        let table_dense = meta.lookup_table_column();
        let table_spread = meta.lookup_table_column();

        let extras = [
            meta.advice_column(),
            meta.advice_column(),
        ];

        let a_4 = extras[0];
        let a_5 = extras[1];

        meta.lookup(|meta| {
            let tag_cur = meta.query_advice(input_tag, Rotation::cur());
            let dense_cur = meta.query_advice(input_dense, Rotation::cur());
            let spread_cur = meta.query_advice(input_spread, Rotation::cur());

            vec![
                (tag_cur, table_tag),
                (dense_cur, table_dense),
                (spread_cur, table_spread),
            ]
        });

        SpreadTableConfig {
            input: SpreadInputs {
                tag: input_tag,
                dense: input_dense,
                spread: input_spread,
            },
            table: SpreadTable {
                tag: table_tag,
                dense: table_dense,
                spread: table_spread,
            },
        }
    }
    

    pub fn load(
        config: SpreadTableConfig,
        layouter: &mut impl Layouter<F>,
    ) -> Result<<Self as Chip<F>>::Loaded, Error> {
        layouter.assign_table(
            || "spread table",
            |mut table| {
                // We generate the row values lazily (we only need them during keygen).
                let mut rows = SpreadTableConfig::generate::<F>();

                for index in 0..(1 << 16) {
                    let mut row = None;
                    table.assign_cell(
                        || "tag",
                        config.table.tag,
                        index,
                        || {
                            row = rows.next();
                            Value::known(row.map(|(tag, _, _)| tag).unwrap())
                        },
                    )?;
                    table.assign_cell(
                        || "dense",
                        config.table.dense,
                        index,
                        || Value::known(row.map(|(_, dense, _)| dense).unwrap()),
                    )?;
                    table.assign_cell(
                        || "spread",
                        config.table.spread,
                        index,
                        || Value::known(row.map(|(_, _, spread)| spread).unwrap()),
                    )?;
                }

                Ok(())
            },
        )
    }

}



impl SpreadTableConfig {

    /* 
    pub(super) fn assign_maj(
        &self,
        region: &mut Region<'_, pallas::Base>,
        spread_halves_a: RoundWordSpread,
        spread_halves_b: RoundWordSpread,
        spread_halves_c: RoundWordSpread,
    ) -> Result<(AssignedBits<16>, AssignedBits<16>), Error> {
        let a_4 = self.extras[1];
        let a_5 = self.message_schedule;
    
        let row = todo!();
    
        self.s_maj.enable(region, row)?;
    
        // Assign and copy spread_a_lo, spread_a_hi
        spread_halves_a
            .0
            .copy_advice(|| "spread_a_lo", region, a_4, row - 1)?;
        spread_halves_a
            .1
            .copy_advice(|| "spread_a_hi", region, a_5, row - 1)?;
    
        // Assign and copy spread_b_lo, spread_b_hi
        spread_halves_b
            .0
            .copy_advice(|| "spread_b_lo", region, a_4, row)?;
        spread_halves_b
            .1
            .copy_advice(|| "spread_b_hi", region, a_5, row)?;
    
        // Assign and copy spread_c_lo, spread_c_hi
        spread_halves_c
            .0
            .copy_advice(|| "spread_c_lo", region, a_4, row + 1)?;
        spread_halves_c
            .1
            .copy_advice(|| "spread_c_hi", region, a_5, row + 1)?;
    
        let m: Value<[bool; 64]> = spread_halves_a
            .value()
            .zip(spread_halves_b.value())
            .zip(spread_halves_c.value())
            .map(|((a, b), c)| i2lebsp(a + b + c));
    
        let m_0: Value<[bool; 32]> = m.map(|m| m[..32].try_into().unwrap());
        let m_0_even = m_0.map(even_bits);
        let m_0_odd = m_0.map(odd_bits);
    
        let m_1: Value<[bool; 32]> = m.map(|m| m[32..].try_into().unwrap());
        let m_1_even = m_1.map(even_bits);
        let m_1_odd = m_1.map(odd_bits);
    
        self.assign_spread_outputs(region, row, m_0_even, m_0_odd, m_1_even, m_1_odd)
    }

*/

    fn generate<F: PrimeField>() -> impl Iterator<Item = (F, F, F)> {
        (1..=(1 << 16)).scan((F::ZERO, F::ZERO, F::ZERO), |(tag, dense, spread), i| {
            // We computed this table row in the previous iteration.
            let res = (*tag, *dense, *spread);

            // i holds the zero-indexed row number for the next table row.
            match i {
                BITS_8 | BITS_15  => *tag += F::ONE,
                _ => (),
            }
            *dense += F::ONE;
            if i & 1 == 0 {
                // On even-numbered rows we recompute the spread.
                *spread = F::ZERO;
                for b in 0..16 {
                    if (i >> b) & 1 != 0 {
                        *spread += F::from(1 << (2 * b));
                    }
                }
            } else {
                // On odd-numbered rows we add one.
                *spread += F::ONE;
            }

            Some(res)
        })
    }
}

#[cfg(test)]
mod tests {
    //use crate::{ spread_table::{SpreadTableConfig, SpreadTableChip, SpreadInputs, SpreadWord, SpreadVar}};

    //use super::{get_tag, SpreadTableChip, SpreadTableConfig};
    //use ethers_core::rand::{self, rng};
    //use pasta_curves::Fp;
    use rand::Rng;

    use group::ff::PrimeField;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        pasta::Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };

    use crate::blake2f::table16::{spread_table::{SpreadTableConfig, SpreadTableChip}, util::even_bits};

    #[test]
    fn lookup_table() {
        /// This represents an advice column at a certain row in the ConstraintSystem
        #[derive(Copy, Clone, Debug)]
        pub struct Variable(Column<Advice>, usize);

        struct MyCircuit {}

        impl<F: PrimeField> Circuit<F> for MyCircuit {
            type Config = SpreadTableConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                MyCircuit {}
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let input_tag = meta.advice_column();
                let input_dense = meta.advice_column();
                let input_spread = meta.advice_column();

                SpreadTableChip::configure(meta, input_tag, input_dense, input_spread)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                SpreadTableChip::load(config.clone(), &mut layouter)?;

                layouter.assign_region(
                    || "spread_test",
                    |mut gate| {
                        let mut row = 0;
                        //let mut left_cell_advice = gate.assign_advice_from_constant()?;
                        //let mut right_cell_advice = gate.assign_advice_from_constant()?;

                        let mut add_row = |tag, dense, spread| -> Result<(), Error> {
                            gate.assign_advice(
                                || "tag",
                                config.input.tag,
                                row,
                                || Value::known(tag),
                            )?;
                            gate.assign_advice(
                                || "dense",
                                config.input.dense,
                                row,
                                || Value::known(dense),
                            )?;
                            gate.assign_advice(
                                || "spread",
                                config.input.spread,
                                row,
                                || Value::known(spread),
                            )?;
                            row += 1;
                            Ok(())
                        };

                        // Test the first few small values.
                        add_row(F::ZERO, F::from(0b000), F::from(0b000000));
                        add_row(F::ZERO, F::from(0b001), F::from(0b000001))?;
                        // add_row(F::ZERO, F::from(0b010), F::from(0b000100))?;
                        // add_row(F::ZERO, F::from(0b011), F::from(0b000101))?;
                        // add_row(F::ZERO, F::from(0b100), F::from(0b010000))?;
                        // add_row(F::ZERO, F::from(0b101), F::from(0b010001))?;

                        /* 
                        let left_cell = left_cell_advice.copy_advice(
                            || "copy left",
                            &mut gate,
                            config.input.spread,
                            1,
                        )?;

                        let right_cell = right_cell_advice.copy_advice(
                            || "copy left",
                            &mut gate,
                            config.input.spread,
                            2,
                        )?;
                        
                        let xor_result = left_cell
                        .value()
                        .zip(right_cell.value()).map(even_bits)
                        .map(|v| F::from_u128(v));

                        assert!(xor_result,001);

                        */

                        // //Test the tag boundaries:
                        // //8-bit
                        // add_row(F::ZERO, F::from(0b11111111), F::from(0b0101010101010101))?;
                        // add_row(F::ONE, F::from(0b100000000), F::from(0b010000000000000000))?;
                        // // - 15-bit
                        // add_row(
                        //     F::ONE,
                        //     F::from(0b111111111111111),
                        //     F::from(0b010101010101010101010101010101),
                        // )?;

                        // // Test random lookup values
                        // let mut rng = rand::thread_rng();

                        // fn interleave_u16_with_zeros(word: u16) -> u32 {
                        //     let mut word: u32 = word.into();
                        //     word = (word ^ (word << 8)) & 0x00ff00ff;
                        //     word = (word ^ (word << 4)) & 0x0f0f0f0f;
                        //     word = (word ^ (word << 2)) & 0x33333333;
                        //     word = (word ^ (word << 1)) & 0x55555555;
                        //     word
                        // }

                        // for _ in 0..10 {
                        //     let word: u16 = rng.gen();
                        //     add_row(
                        //         F::from(u64::from(get_tag(word))),
                        //         F::from(u64::from(word)),
                        //         F::from(u64::from(interleave_u16_with_zeros(word))),
                        //     )?;
                        // }

                        // let input1 = add_row(F::ZERO, F::from(0b000), F::from(0b000000))?;
                        // let input2 = add_row(F::ZERO, F::from(0b001), F::from(0b000001))?;
                        // //let xor = input1.spread.collect::<Vec<_>>(); + input2;                        

                        Ok(())
                    },
                )
            }
        }

        let circuit: MyCircuit = MyCircuit {};

        let prover = match MockProver::<Fp>::run(17, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
