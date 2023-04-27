  //implementation of blake2 hashing algorithm with halo2
  //this is a basic implementation with no optional features such as salting, personalized hashes, or tree hashing
 #![allow(dead_code)]
 #![allow(unused_variables)]
 #![allow(unreachable_code)]

 pub mod table16;
 //pub mod xor;

 use group::ff::{Field, PrimeField};
 use std::{cmp::min, marker::PhantomData};
 use std::convert::TryInto;
 use std::fmt;

 use halo2_proofs::{
    circuit::{Chip, Layouter, Region, Value, AssignedCell},
    pasta::pallas,
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn, Any, Assigned},
    poly::Rotation,
};


 //pub struct BlockWord(pub Option<u32>);

 pub use table16::{BlockWord, Table16Chip, Table16Config};

use self::table16::compression::{State, CompressionConfig};


//The [SHA-256] hash function.
//
// [SHA-256]: https://tools.ietf.org/html/rfc6234

/// The size of a SHA-256 block, in 32-bit words.
pub const BLOCK_SIZE: usize = 16;
/// The size of a SHA-256 digest, in 32-bit words.
const DIGEST_SIZE: usize = 8;

/// The set of circuit instructions required to use the [`Blake2f`] gadget.
pub trait Blake2fInstructions<F: Field>: Chip<F> {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + fmt::Debug;
    /// Variable representing a 32-bit word of the input block to the SHA-256 compression
    /// function.
    type BlockWord: Copy + fmt::Debug + Default;

    /// Places the SHA-256 IV in the circuit, returning the initial state variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input and returns the
    /// final state.
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [Self::BlockWord; BLOCK_SIZE],
    ) -> Result<Self::State, Error>;

    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;
}

/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Blake2fDigest<BlockWord>([BlockWord; DIGEST_SIZE]);

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug)]
pub struct Blake2f<F: Field, CS: Blake2fInstructions<F>> {
    chip: CS,
    state: CS::State,
    cur_block: Vec<CS::BlockWord>,
    length: usize,
}

impl<F: Field, Blake2fChip: Blake2fInstructions<F>> Blake2f<F, Blake2fChip> {
    /// Create a new hasher instance.
    pub fn new(chip: Blake2fChip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
        let state = chip.initialization_vector(&mut layouter)?;
        Ok(Blake2f {
            chip,
            state,
            cur_block: Vec::with_capacity(BLOCK_SIZE),
            length: 0,
        })
    }

    /// Digest data, updating the internal state.
    pub fn update(
        &mut self,
        mut layouter: impl Layouter<F>,
        mut data: &[Blake2fChip::BlockWord],
    ) -> Result<(), Error> {
        self.length += data.len() * 32;

        // Fill the current block, if possible.
        let remaining = BLOCK_SIZE - self.cur_block.len();
        let (l, r) = data.split_at(min(remaining, data.len()));
        self.cur_block.extend_from_slice(l);
        data = r;

        // If we still don't have a full block, we are done.
        if self.cur_block.len() < BLOCK_SIZE {
            return Ok(());
        }

        // Process the now-full current block.
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;
        self.cur_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_SIZE);
        for chunk in &mut chunks_iter {
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
            )?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        self.cur_block.extend_from_slice(rem);

        Ok(())
    }

    /// Retrieve result and consume hasher instance.
    pub fn finalize(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<Blake2fDigest<Blake2fChip::BlockWord>, Error> {
        // Pad the remaining block
        if !self.cur_block.is_empty() {
            let padding = vec![Blake2fChip::BlockWord::default(); BLOCK_SIZE - self.cur_block.len()];
            self.cur_block.extend_from_slice(&padding);
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        }
        self.chip
            .digest(&mut layouter, &self.state)
            .map(Blake2fDigest)
    }

    /// Convenience function to compute hash of the data. It will handle hasher creation,
    /// data feeding and finalization.
    pub fn digest(
        chip: Blake2fChip,
        mut layouter: impl Layouter<F>,
        data: &[Blake2fChip::BlockWord],
    ) -> Result<Blake2fDigest<Blake2fChip::BlockWord>, Error> {
        let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
        hasher.update(layouter.namespace(|| "update"), data)?;
        hasher.finalize(layouter.namespace(|| "finalize"))
    }
}


//  #[cfg(any(feature = "test", test))]
//  pub mod dev {
//      use super::*;

//      use ethers_core::{types::H512, utils::hex::FromHex};
//      use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
//      //use pasta_curves::arithmetic::Field;
//      use std::{marker::PhantomData, str::FromStr};

//      lazy_static::lazy_static! {
//           //https:eips.ethereum.org/EIPS/eip-152#example-usage-in-solidity
//          pub static ref INPUTS_OUTPUTS: (Vec<Blake2fWitness>, Vec<H512>) = {
//              let (h1, h2) = (
//                  <[u8; 32]>::from_hex("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5").expect(""),
//                  <[u8; 32]>::from_hex("d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b").expect(""),
//              );
//              let (m1, m2, m3, m4) = (
//                  <[u8; 32]>::from_hex("6162630000000000000000000000000000000000000000000000000000000000").expect(""),
//                  <[u8; 32]>::from_hex("0000000000000000000000000000000000000000000000000000000000000000").expect(""),
//                  <[u8; 32]>::from_hex("0000000000000000000000000000000000000000000000000000000000000000").expect(""),
//                  <[u8; 32]>::from_hex("0000000000000000000000000000000000000000000000000000000000000000").expect(""),
//              );
//              (
//                  vec![
//                      Blake2fWitness {
//                          rounds: 12,
//                          h: [
//                              u64::from_le_bytes(h1[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(h1[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(h1[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(h1[0x18..0x20].try_into().expect("")),
//                              u64::from_le_bytes(h2[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(h2[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(h2[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(h2[0x18..0x20].try_into().expect("")),
//                          ],
//                          m: [
//                              u64::from_le_bytes(m1[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(m1[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(m1[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(m1[0x18..0x20].try_into().expect("")),
//                              u64::from_le_bytes(m2[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(m2[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(m2[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(m2[0x18..0x20].try_into().expect("")),
//                              u64::from_le_bytes(m3[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(m3[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(m3[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(m3[0x18..0x20].try_into().expect("")),
//                              u64::from_le_bytes(m4[0x00..0x08].try_into().expect("")),
//                              u64::from_le_bytes(m4[0x08..0x10].try_into().expect("")),
//                              u64::from_le_bytes(m4[0x10..0x18].try_into().expect("")),
//                              u64::from_le_bytes(m4[0x18..0x20].try_into().expect("")),
//                          ],
//                          t: [3, 0],
//                          f: true,
//                      }
//                  ],
//                  vec![
//                      H512::from_str("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")
//                      .expect("BLAKE2F compression function output is 64-bytes")
//                  ],
//              )
//          };
//      }

//      #[derive(Default)]
//      pub struct Blake2fTestCircuit<F> {
//          pub inputs: Vec<Blake2fWitness>,
//          pub outputs: Vec<usize>,// H512
//          pub _marker: PhantomData<F>,
//      }

//      impl<F: Field> Circuit<F> for Blake2fTestCircuit<F> {
//          type Config = Blake2fConfig<F>;
//          type FloorPlanner = SimpleFloorPlanner;

//          fn without_witnesses(&self) -> Self {
//              Self::default()
//          }

//          fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
//              let blake2f_table = Blake2fTable::construct(&mut meta);
//              Blake2fConfig::configure(meta, blake2f_table)
//          }

//          fn synthesize(
//              &self,
//              config: Self::Config,
//              mut layouter: impl Layouter<F>,
//          ) -> Result<(), Error> {
//              let chip = Blake2fChip::construct(config, self.inputs.clone());
//              chip.load(&mut layouter)
//          }
//      }
//  }

//  #[cfg(test)]
//  mod tests {
//      use halo2curves::bn256::Fr;
//      use halo2_proofs::{dev::MockProver};
//      use std::marker::PhantomData;

//      use super::dev::{Blake2fTestCircuit, INPUTS_OUTPUTS};

//      #[test]
//      fn test_blake2f_circuit() {
//          let (inputs, outputs) = INPUTS_OUTPUTS.clone();

//          let circuit: Blake2fTestCircuit<Fr> = Blake2fTestCircuit {
//              inputs,
//              outputs,
//              _marker: PhantomData,
//             H512: todo!(),
//          };

//          let k = 8;
//          let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//          assert_eq!(prover.verify(), Ok(()));
//      }
//  }
