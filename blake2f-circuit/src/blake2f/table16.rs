

 pub mod compression;
 pub mod util;
 pub mod spread_table;
 pub mod gate;


 use compression::*;
 //use gates::*;
 //use message_schedule::*;
 use spread_table::*;
 use util::*;

 use std::convert::TryInto;
 use std::marker::PhantomData;

 use super::Blake2fInstructions;
 use crate::blake2f::BLOCK_SIZE;

 use halo2_proofs::{
     circuit::{AssignedCell, Chip, Layouter, Region, Value},
     pasta::pallas,
     plonk::{Advice, Any, Assigned, Column, ConstraintSystem, Error},
 };


 const ROUNDS: usize = 10;
 const STATE: usize = 16;

 #[allow(clippy::unreadable_literal)]
 pub(crate) const ROUND_CONSTANTS: [[usize; 16]; ROUNDS] = [
    [  0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7,  0x8, 0x9, 0xa, 0xb, 0xc, 0xd, 0xe, 0xf,],
    [  0xe, 0xa, 0x4, 0x8, 0x9, 0xf, 0xd, 0x6,  0x1, 0xc, 0x0, 0x2, 0xb, 0x7, 0x5, 0x3,],
    [  0xb, 0x8, 0xc, 0x0, 0x5, 0x2, 0xf, 0xd,  0xa, 0xe, 0x3, 0x6, 0x7, 0x1, 0x9, 0x4,],
    [  0x7, 0x9, 0x3, 0x1, 0xd, 0xc, 0xb, 0xe,  0x2, 0x6, 0x5, 0xa, 0x4, 0x0, 0xf, 0x8,],
    [  0x9, 0x0, 0x5, 0x7, 0x2, 0x4, 0xa, 0xf,  0xe, 0x1, 0xb, 0xc, 0x6, 0x8, 0x3, 0xd,],
    [  0x2, 0xc, 0x6, 0xa, 0x0, 0xb, 0x8, 0x3,  0x4, 0xd, 0x7, 0x5, 0xf, 0xe, 0x1, 0x9,],
    [  0xc, 0x5, 0x1, 0xf, 0xe, 0xd, 0x4, 0xa,  0x0, 0x7, 0x6, 0x3, 0x9, 0x2, 0x8, 0xb,],
    [  0xd, 0xb, 0x7, 0xe, 0xc, 0x1, 0x3, 0x9,  0x5, 0x0, 0xf, 0x4, 0x8, 0x6, 0x2, 0xa,],
    [  0x6, 0xf, 0xe, 0x9, 0xb, 0x3, 0x0, 0x8,  0xc, 0x2, 0xd, 0x7, 0x1, 0x4, 0xa, 0x5,],
    [  0xa, 0x2, 0x8, 0x4, 0x7, 0x6, 0x1, 0x5,  0xf, 0xb, 0x9, 0xe, 0x3, 0xc, 0xd, 0x0,],

 ];


 const IV: [u64; 8] = [
    0x6a09e667f3bcc908,   // Frac(sqrt(2))
    0xbb67ae8584caa73b,   // Frac(sqrt(3))
    0x3c6ef372fe94f82b,   // Frac(sqrt(5))
    0xa54ff53a5f1d36f1,   // Frac(sqrt(7))
    0x510e527fade682d1,   // Frac(sqrt(11))
    0x9b05688c2b3e6c1f,   // Frac(sqrt(13))
    0x1f83d9abfb41bd6b,   // Frac(sqrt(17))
    0x5be0cd19137e2179,   // Frac(sqrt(19))
 ];

 #[derive(Clone, Copy, Debug, Default)]
 // A word in a `Table16` message block.
  //TODO: Make the internals of this struct private.
 pub struct BlockWord(pub Value<u32>);

 #[derive(Clone, Debug)]
 // Little-endian bits (up to 64 bits)
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
     pub fn assign_bits<A, AR, T: TryInto<[bool; LEN]> + std::fmt::Debug + Clone>(
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

 // Configuration for a [`Table16Chip`].
 #[derive(Clone, Debug)]
 pub struct Table16Config {
     lookup: SpreadTableConfig,
     //message_schedule: MessageScheduleConfig,
     compression: CompressionConfig,
 }

 // A chip that implements SHA-256 with a maximum lookup table size of $2^16$.
 #[derive(Clone, Debug)]
 pub struct Table16Chip {
     config: Table16Config,
     _marker: PhantomData<pallas::Base>,
 }

 impl Chip<pallas::Base> for Table16Chip {
     type Config = Table16Config;
     type Loaded = ();

     fn config(&self) -> &Self::Config {
         &self.config
     }

     fn loaded(&self) -> &Self::Loaded {
         &()
     }
 }

 impl Table16Chip {
     // Reconstructs this chip from the given config.
     pub fn construct(config: <Self as Chip<pallas::Base>>::Config) -> Self {
         Self {
             config,
             _marker: PhantomData,
         }
     }

     // Configures a circuit to include this chip.
     pub fn configure(
         meta: &mut ConstraintSystem<pallas::Base>,
     ) -> <Self as Chip<pallas::Base>>::Config {
          //Columns required by this chip:
         let message_schedule = meta.advice_column();
         let extras = [
             meta.advice_column(),
             meta.advice_column(),
             meta.advice_column(),
             meta.advice_column(),
             meta.advice_column(),
             meta.advice_column(),
         ];

          //- Three advice columns to interact with the lookup table.
         let input_tag = meta.advice_column();
         let input_dense = meta.advice_column();
         let input_spread = meta.advice_column();

         let lookup = SpreadTableChip::configure(meta, input_tag, input_dense, input_spread);
         let lookup_inputs = lookup.input.clone();

         // Rename these here for ease of matching the gates to the specification.
         let _a_0 = lookup_inputs.tag;
         let a_1 = lookup_inputs.dense;
         let a_2 = lookup_inputs.spread;
         let a_3 = extras[0];
         let a_4 = extras[1];
         let a_5 = message_schedule;
         let a_6 = extras[2];
         let a_7 = extras[3];
         let a_8 = extras[4];
         let _a_9 = extras[5];

          //Add all advice columns to permutation
         for column in [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8].iter() {
             meta.enable_equality(*column);
         }

         let compression =
             CompressionConfig::configure(meta, lookup_inputs.clone(), message_schedule, extras);

        //  let message_schedule =
        //      MessageScheduleConfig::configure(meta, lookup_inputs, message_schedule, extras);

         Table16Config {
             lookup,
             //message_schedule,
             compression,
         }
     }

     // Loads the lookup table required by this chip into the circuit.
     pub fn load(
         config: Table16Config,
         layouter: &mut impl Layouter<pallas::Base>,
     ) -> Result<(), Error> {
         SpreadTableChip::load(config.lookup, layouter)
     }
 }

 impl Blake2fInstructions<pallas::Base> for Table16Chip {
     type State = State;
     type BlockWord = BlockWord;

     fn initialization_vector(
         &self,
         layouter: &mut impl Layouter<pallas::Base>,
     ) -> Result<State, Error> {
         self.config().compression.initialize_with_iv(layouter, IV)
     }

     fn initialization(
         &self,
         layouter: &mut impl Layouter<pallas::Base>,
         init_state: &Self::State,
     ) -> Result<Self::State, Error> {
         self.config()
             .compression
             .initialize_with_state(layouter, init_state.clone())
     }

      //Given an initialized state and an input message block, compress the
      //message block and return the final state.
     fn compress(
         &self,
         layouter: &mut impl Layouter<pallas::Base>,
         initialized_state: &Self::State,
         input: [Self::BlockWord; super::BLOCK_SIZE],
     ) -> Result<Self::State, Error> {
         let config = self.config();
         //let (_, w_halves) = config.message_schedule.process(layouter, input)?;
         // config
           //  .compression
             //.compress(layouter, initialized_state.clone())
             todo!();
     }

     fn digest(
         &self,
         layouter: &mut impl Layouter<pallas::Base>,
         state: &Self::State,
     ) -> Result<[Self::BlockWord; super::DIGEST_SIZE], Error> {
          //Copy the dense forms of the state variable chunks down to this gate.
          //Reconstruct the 32-bit dense words.
         self.config().compression.digest(layouter, state.clone())
     }
 }

 // Common assignment patterns used by Table16 regions.
 pub trait Table16Assignment {
     // Assign cells for general spread computation used in sigma, ch, ch_neg, maj gates
     #[allow(clippy::too_many_arguments)]
     #[allow(clippy::type_complexity)]
     fn assign_spread_outputs(
         &self,
         region: &mut Region<'_, pallas::Base>,
         lookup: &SpreadInputs,
         a_3: Column<Advice>,
         row: usize,
         r_0_even: Value<[bool; 32]>,
         r_0_odd: Value<[bool; 32]>,
         r_1_even: Value<[bool; 32]>,
         r_1_odd: Value<[bool; 32]>,
     ) -> Result<
         (
             (AssignedBits<32>, AssignedBits<32>),
             (AssignedBits<32>, AssignedBits<32>),
         ),
         Error,
     > {
          //Lookup R_0^{even}, R_0^{odd}, R_1^{even}, R_1^{odd}
         let r_0_even = SpreadVar::with_lookup(
             region,
             lookup,
             row - 1,
             r_0_even.map(SpreadWord::<32, 64>::new),
         )?;
         let r_0_odd =
             SpreadVar::with_lookup(region, lookup, row, r_0_odd.map(SpreadWord::<16, 32>::new))?;
         let r_1_even = SpreadVar::with_lookup(
             region,
             lookup,
             row + 1,
             r_1_even.map(SpreadWord::<32, 64>::new),
         )?;
         let r_1_odd = SpreadVar::with_lookup(
             region,
             lookup,
             row + 2,
             r_1_odd.map(SpreadWord::<32, 64>::new),
         )?;

          //Assign and copy R_1^{odd}
         r_1_odd
             .spread
             .copy_advice(|| "Assign and copy R_1^{odd}", region, a_3, row)?;

         Ok((
             (r_0_even.dense, r_1_even.dense),
             (r_0_odd.dense, r_1_odd.dense),
         ))
     }

     // Assign outputs of sigma gates
     #[allow(clippy::too_many_arguments)]
     fn assign_sigma_outputs(
         &self,
         region: &mut Region<'_, pallas::Base>,
         lookup: &SpreadInputs,
         a_3: Column<Advice>,
         row: usize,
         r_0_even: Value<[bool; 32]>,
         r_0_odd: Value<[bool; 32]>,
         r_1_even: Value<[bool; 32]>,
         r_1_odd: Value<[bool; 32]>,
     ) -> Result<(AssignedBits<32>, AssignedBits<32>), Error> {
         let (even, _odd) = self.assign_spread_outputs(
             region, lookup, a_3, row, r_0_even, r_0_odd, r_1_even, r_1_odd,
         )?;

         Ok(even)
     }
 }

/* 
 #[cfg(test)]
 #[cfg(feature = "test-dev-graph")]
 mod tests {
     use super::super::{Blake2f, DIGEST_SIZE};
     use plotters::prelude::*;
     use super::{Table16Chip, Table16Config};
     use halo2_proofs::{
         circuit::{Layouter, SimpleFloorPlanner},
         pasta::pallas,
         plonk::{Circuit, ConstraintSystem, Error},
     };

     #[test]
     fn print_blake2f_circuit() {
         
         struct MyCircuit {}

         impl Circuit<pallas::Base> for MyCircuit {
             type Config = Table16Config;
             type FloorPlanner = SimpleFloorPlanner;

             fn without_witnesses(&self) -> Self {
                 MyCircuit {}
             }

             fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
                 Table16Chip::configure(meta)
             }

             fn synthesize(
                 &self,
                 config: Self::Config,
                 mut layouter: impl Layouter<pallas::Base>,
             ) -> Result<(), Error> {
                 let table16_chip = Table16Chip::construct(config.clone());
                 Table16Chip::load(config, &mut layouter)?;

                 // Test vector: "abc"
                 let test_input = todo; //msg_schedule_test_input();

                  //Create a message of length 31 blocks
                 let mut input = Vec::with_capacity(31 * BLOCK_SIZE);
                 for _ in 0..31 {
                     input.extend_from_slice(&test_input);
                 }

                 Blake2f::digest(table16_chip, layouter.namespace(|| "'abc' * 31"), &input)?;

                 Ok(())
             }
         }
         use plotters::prelude::*;
         let root =
             BitMapBackend::new("Blake2f-table16-chip-layout.png", (1024, 3480)).into_drawing_area();
         root.fill(&WHITE).unwrap();
         let root = root
             .titled("16-bit Table Blake2f Chip", ("sans-serif", 60))
             .unwrap();

         let circuit = MyCircuit {};
         halo2_proofs::dev::CircuitLayout::default()
             .render::<pallas::Base, _, _>(17, &circuit, &root)
             .unwrap();
     }
 }
*/