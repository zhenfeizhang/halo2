//! Primitives used in endoscaling.

use group::{Curve, Group};
use pasta_curves::arithmetic::{CurveAffine, FieldExt};

use subtle::CtOption;

/// Maps a pair of bits to a multiple of a scalar using endoscaling.
pub(crate) fn compute_endoscalar_pair<F: FieldExt>(bits: [bool; 2]) -> F {
    // [2 * bits.0 - 1]
    let mut scalar = F::from(bits[0]).double() - F::one();

    if bits[1] {
        scalar *= F::ZETA;
    }

    scalar
}

/// Maps a K-bit bitstring to a scalar.
///
/// This corresponds to Algorithm 1 from [BGH2019], where `F` corresponds to $F_q$, the
/// scalar field of $P$. Where Algorithm 1 computes $Acc = [scalar] P$, this function
/// computes `scalar`.
///
/// [BGH2019]: https://eprint.iacr.org/2019/1021.pdf
#[allow(dead_code)]
pub(crate) fn compute_endoscalar<F: FieldExt>(bits: &[bool]) -> F {
    compute_endoscalar_with_acc(None, bits)
}

/// Maps a K-bit bitstring to a scalar.
///
/// This function takes an optional accumulator which can be initialised to some value.
/// This is convenient when chunking the bitstring being endoscaled is a partial chunk
/// in some larger bitstring.
///
/// # Panics
/// Panics if there is an odd number of bits.
pub(crate) fn compute_endoscalar_with_acc<F: FieldExt>(acc: Option<F>, bits: &[bool]) -> F {
    assert_eq!(bits.len() % 2, 0);

    let mut acc = if let Some(acc) = acc {
        acc
    } else {
        (F::ZETA + F::one()).double()
    };
    for j in 0..(bits.len() / 2) {
        let pair = [bits[2 * j], bits[2 * j + 1]];
        let endo = compute_endoscalar_pair::<F>(pair);
        acc = acc.double();
        acc += endo;
    }
    acc
}

/// Maps a pair of bits to a multiple of a base using endoscaling.
///
/// # Panics
/// Panics if the base is the identity.
pub(crate) fn endoscale_point_pair<C: CurveAffine>(bits: [bool; 2], base: C) -> CtOption<C> {
    assert!(!bool::from(base.to_curve().is_identity()));

    let mut base = {
        let base = base.coordinates();
        (*base.unwrap().x(), *base.unwrap().y())
    };

    if !bits[0] {
        base.1 = -base.1;
    }

    if bits[1] {
        base.0 *= C::Base::ZETA;
    }

    C::from_xy(base.0, base.1)
}

/// Maps a K-bit bitstring to a multiple of a given base.
///
/// This is Algorithm 1 from [BGH2019](https://eprint.iacr.org/2019/1021.pdf).
///
/// # Panics
/// Panics if the base is the identity.
/// Panics if there is an odd number of bits.
#[allow(dead_code)]
pub(crate) fn endoscale_point<C: CurveAffine>(bits: &[bool], base: C) -> C {
    assert_eq!(bits.len() % 2, 0);
    assert!(!bool::from(base.to_curve().is_identity()));

    // Initialise accumulator to [2](φ(P) + P)
    let mut acc = (base.to_curve() + base * C::Scalar::ZETA).double();

    for j in 0..(bits.len() / 2) {
        let pair = [bits[2 * j], bits[2 * j + 1]];
        let endo = endoscale_point_pair::<C>(pair, base);
        acc = acc.double();
        acc += endo.unwrap();
    }

    acc.to_affine()
}

#[test]

fn test_endoscale_primitives() {
    use group::prime::PrimeCurveAffine;
    use pasta_curves::pallas;
    use rand::rngs::OsRng;

    let base = pallas::Point::random(OsRng);
    let bits = [true, false, true, false, false, false, true, true];

    let endoscalar: pallas::Scalar = compute_endoscalar(&bits);
    let endoscaled_base = endoscale_point(&bits, base.to_affine());

    assert_eq!(base * endoscalar, endoscaled_base.to_curve());

    fn endoscale_scalar_by_chunk<F: FieldExt, const K: usize>(bits: &[bool]) -> F {
        assert_eq!(bits.len() % K, 0);

        let mut acc = (F::ZETA + F::one()).double();
        for chunk_idx in 0..(bits.len() / K) {
            let idx = chunk_idx * K;
            acc = compute_endoscalar_with_acc(Some(acc), &bits[idx..(idx + K)]);
        }
        acc
    }
    let endoscalar_by_chunk: pallas::Scalar = endoscale_scalar_by_chunk::<_, 4>(&bits);
    let endoscalar_by_pair: pallas::Scalar = compute_endoscalar_with_acc(None, &bits);
    assert_eq!(endoscalar_by_chunk, endoscalar_by_pair);

    fn endo_partial_chunk_lookup<F: FieldExt, const K: usize, const N: usize>(bits: &[bool]) -> F {
        let k_prime = bits.len();
        assert!(K % 2 == 0);
        assert!(k_prime % 2 == 0);
        assert!(k_prime <= K);

        let padding = std::iter::repeat(false).take(K - k_prime);
        let padded_bits: Vec<_> = padding.chain(bits.iter().copied()).collect();
        let padded_endo = compute_endoscalar_with_acc(Some(F::zero()), &padded_bits);

        let endo = {
            //   (1 - 2^{(K - K')/2}) * 2^{K'/2}
            // = 2^{K'/2} - 2^{K/2}
            let shift = F::from(1 << (k_prime / 2)) - F::from(1 << (K / 2));
            padded_endo - shift
        };

        assert_eq!(endo, compute_endoscalar_with_acc(Some(F::zero()), bits));

        endo
    }

    endo_partial_chunk_lookup::<pallas::Base, 10, 1024>(&bits);
}
