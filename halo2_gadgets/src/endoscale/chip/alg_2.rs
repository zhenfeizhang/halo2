use ff::{Field, PrimeFieldBits};
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector},
    poly::Rotation,
};

use crate::{
    endoscale::util::compute_endoscalar_with_acc,
    utilities::decompose_running_sum::{RunningSum, RunningSumConfig},
};

use super::TableConfig;

/// Config used in Algorithm 2 (endoscaling in the field).
#[derive(Clone, Debug)]
pub(super) struct Alg2Config<C: CurveAffine, const K: usize, const MAX_BITSTRING_LENGTH: usize>
where
    C::Base: PrimeFieldBits,
{
    // Selector enabling a lookup in the (bitstring, endoscalar) table.
    q_lookup: Selector,
    // Selector for Alg 2 endoscaling.
    q_endoscale_scalar: Selector,
    // Public inputs are provided as endoscalars. Each endoscalar corresponds
    // to a K-bit chunk.
    endoscalars: Column<Instance>,
    // An additional advice column where endoscalar values are copied and used
    // in the lookup argument.
    endoscalars_copy: Column<Advice>,
    // Advice column where accumulator is witnessed.
    acc: Column<Advice>,
    // Configuration for running sum decomposition into K-bit chunks.
    pub(super) running_sum_chunks: RunningSumConfig<C::Base, K>,
    // Table mapping words to their corresponding endoscalars.
    table: TableConfig<C::Base, K>,
}

impl<C: CurveAffine, const K: usize, const MAX_BITSTRING_LENGTH: usize>
    Alg2Config<C, K, MAX_BITSTRING_LENGTH>
where
    C::Base: PrimeFieldBits,
{
    pub(super) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        endoscalars: Column<Instance>,
        endoscalars_copy: Column<Advice>,
        acc: Column<Advice>,
        running_sum_chunks: RunningSumConfig<C::Base, K>,
        table: TableConfig<C::Base, K>,
    ) -> Self {
        meta.enable_equality(endoscalars);
        meta.enable_equality(endoscalars_copy);
        meta.enable_equality(acc);

        let config = Self {
            q_lookup: meta.complex_selector(),
            q_endoscale_scalar: meta.selector(),
            endoscalars,
            endoscalars_copy,
            acc,
            running_sum_chunks,
            table,
        };

        meta.create_gate("Endoscale scalar with lookup", |meta| {
            let q_endoscale_scalar = meta.query_selector(config.q_endoscale_scalar);
            let endo = meta.query_advice(config.endoscalars_copy, Rotation::cur());
            let acc = meta.query_advice(config.acc, Rotation::cur());
            let next_acc = meta.query_advice(config.acc, Rotation::next());

            // Check that next_acc = acc + endo * 2^{K/2}
            let expected_next_acc = acc + (endo * C::Base::from(1 << (K / 2)));

            Constraints::with_selector(q_endoscale_scalar, [next_acc - expected_next_acc])
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let neg_q_lookup = Expression::Constant(C::Base::one()) - q_lookup.clone();
            let word = config.running_sum_chunks.window_expr(meta);
            let endo = meta.query_advice(config.endoscalars_copy, Rotation::cur());
            let default_endo = {
                let val = compute_endoscalar_with_acc(Some(C::Base::zero()), &[false; K]);
                Expression::Constant(val)
            };

            vec![
                (q_lookup.clone() * word, table.bits),
                (
                    q_lookup * endo + neg_q_lookup * default_endo,
                    table.endoscalar,
                ),
            ]
        });

        config
    }

    pub(super) fn compute_endoscalar(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: &RunningSum<C::Base, K>,
    ) -> Result<AssignedCell<C::Base, C::Base>, Error> {
        let num_bits = bitstring.num_bits();
        // num_bits must be an even number not greater than MAX_BITSTRING_LENGTH.
        assert!(num_bits <= MAX_BITSTRING_LENGTH);

        layouter.assign_region(
            || "Endoscale scalar using bitstring (lookup optimisation)",
            |mut region| {
                let offset = 0;
                // The endoscalar is initialised to 2 * (ζ + 1).
                let mut acc = {
                    let init = (C::Base::ZETA + C::Base::one()).double();
                    region.assign_advice_from_constant(
                        || "initialise acc",
                        self.acc,
                        offset,
                        init,
                    )?
                };

                // Copy the running sum
                for (idx, z) in bitstring.zs().iter().enumerate() {
                    z.copy_advice(
                        || format!("z[{:?}]", idx),
                        &mut region,
                        self.running_sum_chunks.z(),
                        offset + idx,
                    )?;
                }

                // For each chunk, lookup the (chunk, endoscalar) pair and add
                // it to the accumulator.
                for (idx, chunk) in bitstring.windows().iter().enumerate() {
                    self.q_lookup.enable(&mut region, offset + idx)?;
                    self.q_endoscale_scalar.enable(&mut region, offset + idx)?;

                    let endoscalar = chunk.map(|c| {
                        compute_endoscalar_with_acc(
                            Some(C::Base::zero()),
                            &c.to_le_bits().iter().by_vals().take(K).collect::<Vec<_>>(),
                        )
                    });
                    // Witness endoscalar.
                    region.assign_advice(
                        || format!("Endoscalar for chunk {}", idx),
                        self.endoscalars_copy,
                        offset + idx,
                        || endoscalar,
                    )?;

                    // Bitshift the endoscalar by {K / 2} and add to accumulator.
                    let acc_val = acc
                        .value()
                        .zip(endoscalar)
                        .map(|(&acc, endo)| acc + endo * C::Base::from(1 << (K / 2)));
                    acc = region.assign_advice(
                        || format!("Endoscalar for chunk {}", idx),
                        self.acc,
                        offset + idx + 1,
                        || acc_val,
                    )?;
                }

                Ok(acc)
            },
        )
    }

    pub(super) fn recover_bitstring(
        &self,
        mut _layouter: &mut impl Layouter<C::Base>,
        _bitstring: &RunningSum<C::Base, K>,
        _pub_input_rows: Vec<usize>,
    ) -> Result<RunningSum<C::Base, K>, Error> {
        todo!()
    }
}
