// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ark_ec::{ModelParameters, SWModelParameters};
use ark_ff::{BigInteger, FftField, Field, FpParameters, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

/// Returns an iterator over increasing powers of the given `scalar` starting
/// at `0`.
#[inline]
pub fn powers_of<F>(scalar: F) -> impl Iterator<Item = F>
where
    F: Field,
{
    core::iter::successors(Some(F::one()), move |p| Some(*p * scalar))
}

/// Evaluation Domain Extension Trait
pub trait EvaluationDomainExt<F>: EvaluationDomain<F>
where
    F: FftField,
{
    /// Returns the value of `log_2(self.size)`.
    fn log_size_of_group(&self) -> u32;

    /// Returns the inverse of the size in the field.
    fn size_inv(&self) -> F;

    /// Returns a fixed generator of the subgroup.
    fn group_gen(&self) -> F;

    /// Returns the inverse of the fixed generator of the subgroup.
    fn group_gen_inv(&self) -> F;

    /// Returns a fixed multiplicative generator of the finite field.
    fn generator_inv(&self) -> F;
}

impl<F> EvaluationDomainExt<F> for GeneralEvaluationDomain<F>
where
    F: FftField,
{
    #[inline]
    fn log_size_of_group(&self) -> u32 {
        match self {
            GeneralEvaluationDomain::Radix2(domain) => domain.log_size_of_group,
            GeneralEvaluationDomain::MixedRadix(domain) => {
                domain.log_size_of_group
            }
        }
    }

    #[inline]
    fn size_inv(&self) -> F {
        match self {
            GeneralEvaluationDomain::Radix2(domain) => domain.size_inv,
            GeneralEvaluationDomain::MixedRadix(domain) => domain.size_inv,
        }
    }

    #[inline]
    fn group_gen(&self) -> F {
        match self {
            GeneralEvaluationDomain::Radix2(domain) => domain.group_gen,
            GeneralEvaluationDomain::MixedRadix(domain) => domain.group_gen,
        }
    }

    #[inline]
    fn group_gen_inv(&self) -> F {
        match self {
            GeneralEvaluationDomain::Radix2(domain) => domain.group_gen_inv,
            GeneralEvaluationDomain::MixedRadix(domain) => domain.group_gen_inv,
        }
    }

    #[inline]
    fn generator_inv(&self) -> F {
        match self {
            GeneralEvaluationDomain::Radix2(domain) => domain.generator_inv,
            GeneralEvaluationDomain::MixedRadix(domain) => domain.generator_inv,
        }
    }
}

/// Get a pairing friendly curve scalar `E::Fr` from a scalar of the embedded
/// curve. Panics if the embedded scalar is greater than the modulus of the
/// pairing firendly curve scalar field
#[allow(dead_code)]
pub fn from_embedded_curve_scalar<F, P>(
    embedded_scalar: <P as ModelParameters>::ScalarField,
) -> F
where
    F: PrimeField,
    P: SWModelParameters<BaseField = F>,
{
    let scalar_repr = embedded_scalar.into_repr();
    let modulus = <<F as PrimeField>::Params as FpParameters>::MODULUS;
    if modulus.num_bits() >= scalar_repr.num_bits() {
        let s = <<F as PrimeField>::BigInt as BigInteger>::from_bits_le(
            &scalar_repr.to_bits_le(),
        );
        assert!(s < modulus,
            "The embedded scalar exceeds the capacity representation of the outter curve scalar");
    } else {
        let m = <<P::ScalarField as PrimeField>::BigInt as BigInteger>::from_bits_le(
            &modulus.to_bits_le(),
        );
        assert!(scalar_repr < m,
            "The embedded scalar exceeds the capacity representation of the outter curve scalar");
    }
    F::from_le_bytes_mod_order(&scalar_repr.to_bytes_le())
}

/// Get a embedded curve scalar `P::ScalarField` from a scalar of the pariring
/// friendly curve. Panics if the pairing frindly curve scalar is greater than
/// the modulus of the embedded curve scalar field
#[allow(dead_code)]
pub(crate) fn to_embedded_curve_scalar<F, P>(pfc_scalar: F) -> P::ScalarField
where
    F: PrimeField,
    P: SWModelParameters<BaseField = F>,
{
    let scalar_repr = pfc_scalar.into_repr();
    let modulus =
        <<P::ScalarField as PrimeField>::Params as FpParameters>::MODULUS;
    if modulus.num_bits() >= scalar_repr.num_bits() {
        let s = <<P::ScalarField as PrimeField>::BigInt as BigInteger>::from_bits_le(
            &scalar_repr.to_bits_le(),
        );
        assert!(s < modulus,
            "The embedded scalar exceeds the capacity representation of the outter curve scalar");
    } else {
        let m = <<F as PrimeField>::BigInt as BigInteger>::from_bits_le(
            &modulus.to_bits_le(),
        );
        assert!(scalar_repr < m,
            "The embedded scalar exceeds the capacity representation of the outter curve scalar");
    }
    P::ScalarField::from_le_bytes_mod_order(&scalar_repr.to_bytes_le())
}

/// Macro to quickly label polynomials
#[macro_export]
macro_rules! label_polynomial {
    ($poly:expr) => {
        ark_poly_commit::LabeledPolynomial::new(
            stringify!($poly).to_owned(),
            $poly.clone(),
            None,
            None,
        )
    };
}

/// Macro to quickly label polynomial commitments
#[macro_export]
macro_rules! label_commitment {
    ($comm:expr) => {
        ark_poly_commit::LabeledCommitment::new(
            stringify!($comm).to_owned(),
            $comm.clone(),
            None,
        )
    };
}
