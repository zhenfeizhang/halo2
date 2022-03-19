use ff::{Field, PrimeFieldBits};
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector},
    poly::Rotation,
};

use crate::{
    endoscale::util::compute_endoscalar_with_acc,
    utilities::{
        decompose_running_sum::{RunningSum, RunningSumConfig},
        lookup_range_check::LookupRangeCheckConfig,
    },
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
    // Selector enabling a lookup on a partial chunk in the (bitstring, endoscalar) table.
    q_lookup_partial: Selector,
    // Selector checking that partial chunks are correctly shifted.
    q_partial_chunk: Selector,
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
    // Configuration for lookup range check of partial chunks.
    lookup_range_check: LookupRangeCheckConfig<C::Base, K>,
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
        let lookup_range_check =
            LookupRangeCheckConfig::configure(meta, running_sum_chunks.z(), table.bits);

        meta.enable_equality(endoscalars);
        meta.enable_equality(endoscalars_copy);
        meta.enable_equality(acc);

        let config = Self {
            q_lookup: meta.complex_selector(),
            q_endoscale_scalar: meta.selector(),
            q_lookup_partial: meta.complex_selector(),
            q_partial_chunk: meta.selector(),
            endoscalars,
            endoscalars_copy,
            acc,
            running_sum_chunks,
            table,
            lookup_range_check,
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

        meta.create_gate("Endoscale scalar of partial chunk", |meta| {
            let q_partial_chunk = meta.query_selector(config.q_partial_chunk);
            let padded_endoscalar = meta.query_advice(config.endoscalars_copy, Rotation::prev());
            let shift = meta.query_advice(config.endoscalars_copy, Rotation::cur());
            let shifted_endoscalar = meta.query_advice(config.endoscalars_copy, Rotation::next());
            let prev_acc = meta.query_advice(config.acc, Rotation::prev());
            let cur_acc = meta.query_advice(config.acc, Rotation::cur());

            let acc_check =
                cur_acc - (prev_acc + shifted_endoscalar.clone() * C::Base::from(1 << (K / 2)));

            let shift_check = shifted_endoscalar - (padded_endoscalar - shift);

            Constraints::with_selector(
                q_partial_chunk,
                std::array::IntoIter::new([("acc_check", acc_check), ("shift_check", shift_check)]),
            )
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup_partial);
            let neg_q_lookup = Expression::Constant(C::Base::one()) - q_lookup.clone();
            let word = meta.query_advice(config.acc, Rotation::cur());
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

        // The bitstring will be broken into K-bit chunks with a k_prime-bit
        // partial chunk.
        let k_prime = num_bits % K;

        let (acc, bitstring) = layouter.assign_region(
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

                Ok((acc, bitstring))
            },
        )?;

        // Handle the partial chunk.
        let acc = if k_prime == 0 {
            acc
        } else {
            let padded_endoscalar = self.partial_chunk_lookup(
                layouter.namespace(|| "partial chunk lookup"),
                bitstring.zs().last().unwrap(),
                k_prime,
            )?;

            layouter.assign_region(
                || "Add partial endo to acc",
                |mut region| {
                    let offset = 0;
                    self.q_partial_chunk.enable(&mut region, offset + 1)?;

                    // Copy padded_endoscalar to the correct offset.
                    padded_endoscalar.copy_advice(
                        || "padded endoscalar",
                        &mut region,
                        self.endoscalars_copy,
                        offset,
                    )?;

                    // Assign 2^{K'/2} - 2^{K/2} from a fixed column.
                    let two_pow_k_prime_div2 = C::Base::from(1 << (k_prime / 2));
                    let two_pow_k_div2 = C::Base::from(1 << (K / 2));
                    let shift = two_pow_k_prime_div2 - two_pow_k_div2;
                    region.assign_advice_from_constant(
                        || "k_prime",
                        self.endoscalars_copy,
                        offset + 1,
                        shift,
                    )?;

                    // Subtract 2^{K'/2} - 2^{K/2} from the padded_endoscalar to
                    // recover the endoscalar corresponding to the unpadded
                    // partial chunk.
                    let shifted_endoscalar =
                        padded_endoscalar.value().map(|&padded| padded - shift);
                    region.assign_advice(
                        || "shifted endoscalar",
                        self.endoscalars_copy,
                        offset + 2,
                        || shifted_endoscalar,
                    )?;

                    // Copy the current accumulator to the correct offset.
                    acc.copy_advice(|| "current acc", &mut region, self.acc, offset)?;

                    // Bitshift the endoscalar by {K / 2} and add to accumulator.
                    let acc_val = acc
                        .value()
                        .zip(shifted_endoscalar)
                        .map(|(&acc, endo)| acc + endo * two_pow_k_div2);

                    region.assign_advice(
                        || "Endoscalar for partial chunk",
                        self.acc,
                        offset + 1,
                        || acc_val,
                    )
                },
            )?
        };

        Ok(acc)
    }

    pub(super) fn recover_bitstring(
        &self,
        layouter: &mut impl Layouter<C::Base>,
        bitstring: &RunningSum<C::Base, K>,
        pub_input_rows: Vec<usize>,
    ) -> Result<RunningSum<C::Base, K>, Error> {
        let num_bits = bitstring.num_bits();

        // num_bits must be an even number not greater than MAX_BITSTRING_LENGTH.
        assert!(num_bits <= MAX_BITSTRING_LENGTH);
        assert_eq!(num_bits % 2, 0);

        // The bitstring will be broken into K-bit chunks with a k_prime-bit
        // partial chunk.
        let k_prime = num_bits % K;

        let bitstring = layouter.assign_region(
            || "Recover bitstring from endoscalars",
            |mut region| {
                let offset = 0;

                // Copy the running sum.
                for (idx, z) in bitstring.zs().iter().enumerate() {
                    z.copy_advice(
                        || format!("z[{:?}]", idx),
                        &mut region,
                        self.running_sum_chunks.z(),
                        offset + idx,
                    )?;
                }

                // For each chunk, lookup the (chunk, endoscalar) pair.
                for (idx, (chunk, pub_input_row)) in bitstring
                    .windows()
                    .iter()
                    .zip(pub_input_rows.iter())
                    .enumerate()
                {
                    self.q_lookup.enable(&mut region, offset + idx)?;

                    let _computed_endoscalar = chunk.map(|c| {
                        compute_endoscalar_with_acc(
                            Some(C::Base::zero()),
                            &c.to_le_bits().iter().by_vals().take(K).collect::<Vec<_>>(),
                        )
                    });
                    // Copy endoscalar from given row on instance column
                    let _copied_endoscalar = region.assign_advice_from_instance(
                        || format!("Endoscalar at row {:?}", pub_input_row),
                        self.endoscalars,
                        *pub_input_row,
                        self.endoscalars_copy,
                        offset + idx,
                    )?;

                    #[cfg(test)]
                    {
                        _copied_endoscalar
                            .value()
                            .zip(_computed_endoscalar)
                            .assert_if_known(|(copied, computed)| *copied == computed);
                    }
                }

                Ok(bitstring.clone())
            },
        )?;

        // Handle the partial chunk.
        if k_prime > 0 {
            self.partial_chunk_lookup(
                layouter.namespace(|| "partial chunk lookup"),
                bitstring.zs().last().unwrap(),
                k_prime,
            )?;
        }

        Ok(bitstring)
    }

    fn partial_chunk_lookup(
        &self,
        mut layouter: impl Layouter<C::Base>,
        partial_chunk: &AssignedCell<C::Base, C::Base>,
        partial_chunk_num_bits: usize,
    ) -> Result<AssignedCell<C::Base, C::Base>, Error> {
        // `z_w` of the running sum is the value of the partial chunk.
        // Range-constrain the partial chunk to `k_prime` bits.
        self.lookup_range_check.copy_short_check(
            layouter.namespace(|| {
                format!(
                    "Check that partial_chunk is {} bits",
                    partial_chunk_num_bits
                )
            }),
            partial_chunk,
            partial_chunk_num_bits,
        )?;

        layouter.assign_region(
            || "Endoscale partial chunk",
            |mut region| {
                let offset = 0;

                self.q_lookup_partial.enable(&mut region, offset)?;

                let partial_chunk =
                    partial_chunk.copy_advice(|| "partial chunk", &mut region, self.acc, offset)?;
                // Pad the partial chunk to `K` bits and lookup the corresponding
                // padded_endoscalar.
                let padded_endoscalar = {
                    let padded_bits = partial_chunk.value().map(|v| {
                        std::iter::repeat(false)
                            .take(K)
                            .chain(v.to_le_bits().iter().by_vals())
                            .collect::<Vec<_>>()
                    });
                    let padded_endoscalar =
                        padded_bits.map(|b| compute_endoscalar_with_acc(Some(C::Base::zero()), &b));
                    region.assign_advice(
                        || "padded endoscalar",
                        self.endoscalars_copy,
                        offset,
                        || padded_endoscalar,
                    )?
                };

                Ok(padded_endoscalar)
            },
        )
    }
}
