use std::marker::PhantomData;

use crate::{
    ecc::chip::NonIdentityEccPoint,
    utilities::{
        decompose_running_sum::{RunningSum, RunningSumConfig},
        i2lebsp, range_check,
    },
};

use super::{util::compute_endoscalar_with_acc, EndoscaleInstructions};
use ff::PrimeFieldBits;
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Instance, TableColumn},
};

mod alg_1;
mod alg_2;

use alg_1::Alg1Config;
use alg_2::Alg2Config;

/// Bitstring used in endoscaling.
#[derive(Clone, Debug)]
#[allow(clippy::type_complexity)]
pub enum Bitstring<F: FieldExt + PrimeFieldBits, const K: usize> {
    Pair(RunningSum<F, 2>),
    KBit(RunningSum<F, K>),
}

/// Configuration for endoscalar table.
#[derive(Copy, Clone, Debug)]
pub(crate) struct TableConfig<F: FieldExt, const K: usize> {
    pub(crate) bits: TableColumn,
    pub(crate) endoscalar: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const K: usize> TableConfig<F, K> {
    #[allow(dead_code)]
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        TableConfig {
            bits: meta.lookup_table_column(),
            endoscalar: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "endoscalar_map",
            |mut table| {
                for index in 0..(1 << K) {
                    table.assign_cell(
                        || "bits",
                        self.bits,
                        index,
                        || Value::known(F::from(index as u64)),
                    )?;
                    table.assign_cell(
                        || "endoscalar",
                        self.endoscalar,
                        index,
                        || {
                            Value::known(compute_endoscalar_with_acc(
                                Some(F::zero()),
                                &i2lebsp::<K>(index as u64),
                            ))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// Config used in processing endoscalars.
#[derive(Clone, Debug)]
pub struct EndoscaleConfig<C: CurveAffine, const K: usize, const MAX_BITSTRING_LENGTH: usize>
where
    C::Base: PrimeFieldBits,
{
    alg_1: Alg1Config<C>,
    alg_2: Alg2Config<C, K, MAX_BITSTRING_LENGTH>,
    // Configuration for running sum decomposition into pairs of bits.
    running_sum_pairs: RunningSumConfig<C::Base, 2>,
    // Configuration for running sum decomposition into K-bit chunks.
    running_sum_chunks: RunningSumConfig<C::Base, K>,
}

impl<C: CurveAffine, const K: usize, const MAX_BITSTRING_LENGTH: usize>
    EndoscaleConfig<C, K, MAX_BITSTRING_LENGTH>
where
    C::Base: PrimeFieldBits,
{
    #[allow(dead_code)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        // Advice columns not shared across alg_1 and alg_2
        advices: [Column<Advice>; 8],
        // Running sum column shared across alg_1 and alg_2
        running_sum: Column<Advice>,
        endoscalars: Column<Instance>,
    ) -> Self {
        let running_sum_pairs = {
            let q_pairs = meta.selector();
            RunningSumConfig::configure(meta, q_pairs, running_sum)
        };

        // Each window in running_sum_pairs must be two bits.
        meta.create_gate("pair range check", |meta| {
            let q_range_check = meta.query_selector(running_sum_pairs.q_range_check());
            let word = running_sum_pairs.window_expr(meta);

            Constraints::with_selector(q_range_check, Some(range_check(word, 1 << 2)))
        });

        let alg_1 = Alg1Config::configure(
            meta,
            (advices[0], advices[1]),
            (advices[2], advices[3]),
            (advices[4], advices[5], advices[6], advices[7]),
            running_sum_pairs,
        );

        let running_sum_chunks = {
            let q_chunks = meta.complex_selector();
            RunningSumConfig::configure(meta, q_chunks, running_sum)
        };

        let table = TableConfig::configure(meta);

        let alg_2 = Alg2Config::configure(
            meta,
            endoscalars,
            advices[0],
            advices[1],
            running_sum_chunks,
            table,
        );

        Self {
            alg_1,
            alg_2,
            running_sum_pairs,
            running_sum_chunks,
        }
    }
}

impl<C: CurveAffine, const K: usize, const N: usize> EndoscaleInstructions<C>
    for EndoscaleConfig<C, K, N>
where
    C::Base: PrimeFieldBits,
{
    type NonIdentityPoint = NonIdentityEccPoint<C>;
    type Bitstring = Bitstring<C::Base, K>;
    type FixedBases = C;
    const MAX_BITSTRING_LENGTH: usize = 248;
    const NUM_FIXED_BASES: usize = N;

    fn witness_bitstring(
        &self,
        _layouter: &mut impl Layouter<C::Base>,
        _bits: &[Value<bool>],
        _for_base: bool,
    ) -> Result<Vec<Self::Bitstring>, Error> {
        todo!()
    }

    #[allow(clippy::type_complexity)]
    fn endoscale_fixed_base(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: Vec<Self::Bitstring>,
        bases: Vec<Self::FixedBases>,
    ) -> Result<Vec<Self::NonIdentityPoint>, Error> {
        let mut points = Vec::new();
        for (bitstring, base) in bitstring.iter().zip(bases.iter()) {
            match bitstring {
                Bitstring::Pair(bitstring) => {
                    points.push(self.alg_1.endoscale_fixed_base(layouter, bitstring, base)?)
                }
                _ => unreachable!(),
            }
        }
        Ok(points)
    }

    fn endoscale_var_base(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: Vec<Self::Bitstring>,
        bases: Vec<Self::NonIdentityPoint>,
    ) -> Result<Vec<Self::NonIdentityPoint>, Error> {
        let mut points = Vec::new();
        for (bitstring, base) in bitstring.iter().zip(bases.iter()) {
            match bitstring {
                Bitstring::Pair(bitstring) => {
                    points.push(self.alg_1.endoscale_var_base(layouter, bitstring, base)?)
                }
                _ => unreachable!(),
            }
        }
        Ok(points)
    }

    fn compute_endoscalar(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: &Self::Bitstring,
    ) -> Result<AssignedCell<C::Base, C::Base>, Error> {
        match bitstring {
            Bitstring::KBit(bitstring) => self.alg_2.compute_endoscalar(layouter, bitstring),
            _ => unreachable!(),
        }
    }

    fn recover_bitstring(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: &Self::Bitstring,
        pub_input_rows: Vec<usize>,
    ) -> Result<Self::Bitstring, Error> {
        match bitstring {
            Bitstring::KBit(bitstring) => self
                .alg_2
                .recover_bitstring(layouter, bitstring, pub_input_rows)
                .map(Bitstring::KBit),
            _ => unreachable!(),
        }
    }
}
