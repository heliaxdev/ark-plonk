// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Methods to preprocess the constraint system for use in a proof.

use crate::{
    commitment::HomomorphicCommitment,
    constraint_system::StandardComposer,
    error::{to_pc_error, Error},
    label_polynomial,
    lookup::PreprocessedLookupTable,
    proof_system::{widget, ProverKey},
};
use ark_ec::TEModelParameters;
use ark_ff::{FftField, PrimeField};
use ark_poly::{
    polynomial::univariate::DensePolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, UVPolynomial,
};
use core::marker::PhantomData;
use merlin::Transcript;

/// Struct that contains all of the selector and permutation [`Polynomial`]s in
/// PLONK.
///
/// [`Polynomial`]: DensePolynomial
pub struct SelectorPolynomials<F>
where
    F: FftField,
{
    q_m: DensePolynomial<F>,
    q_l: DensePolynomial<F>,
    q_r: DensePolynomial<F>,
    q_o: DensePolynomial<F>,
    q_c: DensePolynomial<F>,
    q_4: DensePolynomial<F>,
    q_arith: DensePolynomial<F>,
    q_range: DensePolynomial<F>,
    q_logic: DensePolynomial<F>,
    q_lookup: DensePolynomial<F>,
    q_fixed_group_add: DensePolynomial<F>,
    q_variable_group_add: DensePolynomial<F>,
    left_sigma: DensePolynomial<F>,
    right_sigma: DensePolynomial<F>,
    out_sigma: DensePolynomial<F>,
    fourth_sigma: DensePolynomial<F>,
}
/// Struct that contains all of the blinding values for a preprocessed [`ProverKey`]
///
/// [`ProverKey`]: ProverKey
#[derive(Default, Copy, Clone, Debug)]
pub struct Blinding<F>
where
    F: FftField,
{
    /// blinder
    pub q_m: F,
    /// blinder
    pub q_l: F,
    /// blinder
    pub q_r: F,
    /// blinder
    pub q_o: F,
    /// blinder
    pub q_c: F,
    /// blinder
    pub q_4: F,
    /// blinder
    pub q_arith: F,
    /// blinder
    pub q_range: F,
    /// blinder
    pub q_logic: F,
    /// blinder
    pub q_lookup: F,
    /// blinder
    pub q_fixed_group_add: F,
    /// blinder
    pub q_variable_group_add: F,
    /// blinder
    pub left_sigma: F,
    /// blinder
    pub right_sigma: F,
    /// blinder
    pub out_sigma: F,
    /// blinder
    pub fourth_sigma: F,
}

impl<F> ark_std::UniformRand for Blinding<F>
where
    F: FftField,
{
    fn rand<R: ark_std::rand::Rng + ?Sized>(rng: &mut R) -> Self {
        Blinding::<F> {
            q_m: F::rand(rng),
            q_l: F::rand(rng),
            q_r: F::rand(rng),
            q_o: F::rand(rng),
            q_c: F::rand(rng),
            q_4: F::rand(rng),
            q_arith: F::rand(rng),
            q_range: F::rand(rng),
            q_logic: F::rand(rng),
            q_lookup: F::rand(rng),
            q_fixed_group_add: F::rand(rng),
            q_variable_group_add: F::rand(rng),
            left_sigma: F::rand(rng),
            right_sigma: F::rand(rng),
            out_sigma: F::rand(rng),
            fourth_sigma: F::rand(rng),
        }
    }
}

impl<F, P> StandardComposer<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    /// Pads the circuit to the next power of two.
    ///
    /// # Note
    /// `diff` is the difference between circuit size and next power of two.
    fn pad(&mut self, diff: usize) {
        // Add a zero variable to circuit
        let zero_scalar = F::zero();
        let zero_var = self.zero_var();

        let zeroes_scalar = vec![zero_scalar; diff];
        let zeroes_var = vec![zero_var; diff];

        self.q_m.extend(zeroes_scalar.iter());
        self.q_l.extend(zeroes_scalar.iter());
        self.q_r.extend(zeroes_scalar.iter());
        self.q_o.extend(zeroes_scalar.iter());
        self.q_c.extend(zeroes_scalar.iter());
        self.q_4.extend(zeroes_scalar.iter());
        self.q_arith.extend(zeroes_scalar.iter());
        self.q_range.extend(zeroes_scalar.iter());
        self.q_logic.extend(zeroes_scalar.iter());
        self.q_lookup.extend(zeroes_scalar.iter());
        self.q_fixed_group_add.extend(zeroes_scalar.iter());
        self.q_variable_group_add.extend(zeroes_scalar.iter());

        self.w_l.extend(zeroes_var.iter());
        self.w_r.extend(zeroes_var.iter());
        self.w_o.extend(zeroes_var.iter());
        self.w_4.extend(zeroes_var.iter());

        self.n += diff;
    }

    /// Checks that all of the wires of the composer have the same
    /// length.
    fn check_poly_same_len(&self) -> Result<(), Error> {
        let k = self.q_m.len();

        if self.q_o.len() == k
            && self.q_l.len() == k
            && self.q_r.len() == k
            && self.q_c.len() == k
            && self.q_4.len() == k
            && self.q_arith.len() == k
            && self.q_range.len() == k
            && self.q_logic.len() == k
            && self.q_lookup.len() == k
            && self.q_fixed_group_add.len() == k
            && self.q_variable_group_add.len() == k
            && self.w_l.len() == k
            && self.w_r.len() == k
            && self.w_o.len() == k
            && self.w_4.len() == k
        {
            Ok(())
        } else {
            Err(Error::MismatchedPolyLen)
        }
    }
}
impl<F, P> StandardComposer<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    /// These are the parts of preprocessing that the prover must compute
    /// Although the prover does not need the verification key, he must compute
    /// the commitments in order to seed the transcript, allowing both the
    /// prover and verifier to have the same view
    pub fn preprocess_prover<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
    ) -> Result<ProverKey<F>, Error>
    where
        PC: HomomorphicCommitment<F>,
    {
        let (_, selectors, domain, preprocessed_table) =
            self.preprocess_shared(commit_key, transcript, _pc)?;

        let domain_4n =
            GeneralEvaluationDomain::new(4 * domain.size()).ok_or(Error::InvalidEvalDomainSize {
                log_size_of_group: (4 * domain.size()).trailing_zeros(),
                adicity:
                    <<F as FftField>::FftParams as ark_ff::FftParameters>::TWO_ADICITY,
            })?;
        let q_m_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_m),
            domain_4n,
        );
        let q_l_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_l),
            domain_4n,
        );
        let q_r_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_r),
            domain_4n,
        );
        let q_o_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_o),
            domain_4n,
        );
        let q_c_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_c),
            domain_4n,
        );
        let q_4_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_4),
            domain_4n,
        );
        let q_arith_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_arith),
            domain_4n,
        );
        let q_range_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_range),
            domain_4n,
        );
        let q_logic_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_logic),
            domain_4n,
        );
        let q_lookup_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_lookup),
            domain_4n,
        );
        let q_fixed_group_add_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_fixed_group_add),
            domain_4n,
        );
        let q_variable_group_add_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_variable_group_add),
            domain_4n,
        );
        let left_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.left_sigma),
            domain_4n,
        );
        let right_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.right_sigma),
            domain_4n,
        );
        let out_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.out_sigma),
            domain_4n,
        );
        let fourth_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.fourth_sigma),
            domain_4n,
        );
        // XXX: Remove this and compute it on the fly
        let linear_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&[F::zero(), F::one()]),
            domain_4n,
        );

        // Compute 4n evaluations for X^n -1
        let v_h_coset_4n =
            compute_vanishing_poly_over_coset(domain_4n, domain.size() as u64);

        Ok(ProverKey::from_polynomials_and_evals(
            domain.size(),
            (selectors.q_m, q_m_eval_4n),
            (selectors.q_l, q_l_eval_4n),
            (selectors.q_r, q_r_eval_4n),
            (selectors.q_o, q_o_eval_4n),
            (selectors.q_4, q_4_eval_4n),
            (selectors.q_c, q_c_eval_4n),
            (selectors.q_arith, q_arith_eval_4n),
            (selectors.q_range, q_range_eval_4n),
            (selectors.q_logic, q_logic_eval_4n),
            (selectors.q_lookup, q_lookup_eval_4n),
            (selectors.q_fixed_group_add, q_fixed_group_add_eval_4n),
            (selectors.q_variable_group_add, q_variable_group_add_eval_4n),
            (selectors.left_sigma, left_sigma_eval_4n),
            (selectors.right_sigma, right_sigma_eval_4n),
            (selectors.out_sigma, out_sigma_eval_4n),
            (selectors.fourth_sigma, fourth_sigma_eval_4n),
            linear_eval_4n,
            v_h_coset_4n,
            preprocessed_table.t[0].0.clone(),
            preprocessed_table.t[1].0.clone(),
            preprocessed_table.t[2].0.clone(),
            preprocessed_table.t[3].0.clone(),
        ))
    }

    /// These are the parts of preprocessing that the prover must compute
    /// Although the prover does not need the verification key, he must compute
    /// the commitments in order to seed the transcript, allowing both the
    /// prover and verifier to have the same view
    pub fn preprocess_prover_with_blinding<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
        blinding: &Blinding<F>,
    ) -> Result<ProverKey<F>, Error>
    where
        PC: HomomorphicCommitment<F>,
    {
        let (_, selectors, domain, preprocessed_table) = self
            .preprocess_shared_with_blinding(
                commit_key, transcript, _pc, blinding,
            )?;

        let domain_4n =
            GeneralEvaluationDomain::new(4 * domain.size()).ok_or(Error::InvalidEvalDomainSize {
                log_size_of_group: (4 * domain.size()).trailing_zeros(),
                adicity:
                    <<F as FftField>::FftParams as ark_ff::FftParameters>::TWO_ADICITY,
            })?;
        let q_m_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_m),
            domain_4n,
        );
        let q_l_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_l),
            domain_4n,
        );
        let q_r_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_r),
            domain_4n,
        );
        let q_o_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_o),
            domain_4n,
        );
        let q_c_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_c),
            domain_4n,
        );
        let q_4_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_4),
            domain_4n,
        );
        let q_arith_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_arith),
            domain_4n,
        );
        let q_range_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_range),
            domain_4n,
        );
        let q_logic_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_logic),
            domain_4n,
        );
        let q_lookup_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_lookup),
            domain_4n,
        );
        let q_fixed_group_add_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_fixed_group_add),
            domain_4n,
        );
        let q_variable_group_add_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.q_variable_group_add),
            domain_4n,
        );
        let left_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.left_sigma),
            domain_4n,
        );
        let right_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.right_sigma),
            domain_4n,
        );
        let out_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.out_sigma),
            domain_4n,
        );
        let fourth_sigma_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&selectors.fourth_sigma),
            domain_4n,
        );
        // XXX: Remove this and compute it on the fly
        let linear_eval_4n = Evaluations::from_vec_and_domain(
            domain_4n.coset_fft(&[F::zero(), F::one()]),
            domain_4n,
        );

        // Compute 4n evaluations for X^n -1
        let v_h_coset_4n =
            compute_vanishing_poly_over_coset(domain_4n, domain.size() as u64);

        Ok(ProverKey::from_polynomials_and_evals(
            domain.size(),
            (selectors.q_m, q_m_eval_4n),
            (selectors.q_l, q_l_eval_4n),
            (selectors.q_r, q_r_eval_4n),
            (selectors.q_o, q_o_eval_4n),
            (selectors.q_4, q_4_eval_4n),
            (selectors.q_c, q_c_eval_4n),
            (selectors.q_arith, q_arith_eval_4n),
            (selectors.q_range, q_range_eval_4n),
            (selectors.q_logic, q_logic_eval_4n),
            (selectors.q_lookup, q_lookup_eval_4n),
            (selectors.q_fixed_group_add, q_fixed_group_add_eval_4n),
            (selectors.q_variable_group_add, q_variable_group_add_eval_4n),
            (selectors.left_sigma, left_sigma_eval_4n),
            (selectors.right_sigma, right_sigma_eval_4n),
            (selectors.out_sigma, out_sigma_eval_4n),
            (selectors.fourth_sigma, fourth_sigma_eval_4n),
            linear_eval_4n,
            v_h_coset_4n,
            preprocessed_table.t[0].0.clone(),
            preprocessed_table.t[1].0.clone(),
            preprocessed_table.t[2].0.clone(),
            preprocessed_table.t[3].0.clone(),
        ))
    }

    /// The verifier only requires the commitments in order to verify a
    /// [`Proof`](super::Proof) We can therefore speed up preprocessing for the
    /// verifier by skipping the FFTs needed to compute the 4n evaluations.
    pub fn preprocess_verifier<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
    ) -> Result<widget::VerifierKey<F, PC>, Error>
    where
        PC: HomomorphicCommitment<F>,
    {
        let (verifier_key, _, _, _) =
            self.preprocess_shared(commit_key, transcript, _pc)?;
        Ok(verifier_key)
    }

    /// The verifier only requires the commitments in order to verify a
    /// [`Proof`](super::Proof) We can therefore speed up preprocessing for the
    /// verifier by skipping the FFTs needed to compute the 4n evaluations.
    pub fn preprocess_verifier_with_blinding<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
        blinding: &Blinding<F>,
    ) -> Result<widget::VerifierKey<F, PC>, Error>
    where
        PC: HomomorphicCommitment<F>,
    {
        let (verifier_key, _, _, _) = self.preprocess_shared_with_blinding(
            commit_key, transcript, _pc, blinding,
        )?;
        Ok(verifier_key)
    }

    /// Both the [`Prover`](super::Prover) and [`Verifier`](super::Verifier)
    /// must perform IFFTs on the selector polynomials and permutation
    /// polynomials in order to commit to them and have the same transcript
    /// view.
    #[allow(clippy::type_complexity)] // FIXME: Add struct for prover side (last two tuple items).
    fn preprocess_shared<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
    ) -> Result<
        (
            widget::VerifierKey<F, PC>,
            SelectorPolynomials<F>,
            GeneralEvaluationDomain<F>,
            PreprocessedLookupTable<F, PC>,
        ),
        Error,
    >
    where
        PC: HomomorphicCommitment<F>,
    {
        let domain = GeneralEvaluationDomain::new(self.circuit_bound()).ok_or(Error::InvalidEvalDomainSize {
            log_size_of_group: (self.circuit_bound()).trailing_zeros(),
            adicity:
                <<F as FftField>::FftParams as ark_ff::FftParameters>::TWO_ADICITY,
        })?;

        let preprocessed_table = PreprocessedLookupTable::<F, PC>::preprocess(
            &self.lookup_table,
            commit_key,
            domain.size() as u32,
        )
        .unwrap();

        // Check that the length of the wires is consistent.
        self.check_poly_same_len()?;

        // 1. Pad circuit to a power of two
        self.pad(domain.size() as usize - self.n);

        let q_m_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_m));

        let q_r_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_r));

        let q_l_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_l));

        let q_o_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_o));

        let q_c_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_c));

        let q_4_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_4));

        let q_arith_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_arith));

        let q_range_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_range));

        let q_logic_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_logic));

        let q_lookup_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(domain.ifft(&self.q_lookup));

        let q_fixed_group_add_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(
                domain.ifft(&self.q_fixed_group_add),
            );

        let q_variable_group_add_poly: DensePolynomial<F> =
            DensePolynomial::from_coefficients_vec(
                domain.ifft(&self.q_variable_group_add),
            );

        // 2. Compute the sigma polynomials
        let (
            left_sigma_poly,
            right_sigma_poly,
            out_sigma_poly,
            fourth_sigma_poly,
        ) = self.perm.compute_sigma_polynomials(self.n, &domain);

        let (commitments, _) = PC::commit(
            commit_key,
            [
                label_polynomial!(q_m_poly),
                label_polynomial!(q_l_poly),
                label_polynomial!(q_r_poly),
                label_polynomial!(q_o_poly),
                label_polynomial!(q_4_poly),
                label_polynomial!(q_c_poly),
                label_polynomial!(q_arith_poly),
                label_polynomial!(q_range_poly),
                label_polynomial!(q_logic_poly),
                label_polynomial!(q_lookup_poly),
                label_polynomial!(q_fixed_group_add_poly),
                label_polynomial!(q_variable_group_add_poly),
                label_polynomial!(left_sigma_poly),
                label_polynomial!(right_sigma_poly),
                label_polynomial!(out_sigma_poly),
                label_polynomial!(fourth_sigma_poly),
            ]
            .iter(),
            None,
        )
        .map_err(to_pc_error::<F, PC>)?;

        let verifier_key = widget::VerifierKey::from_polynomial_commitments(
            self.n,
            commitments[0].commitment().clone(), // q_m
            commitments[1].commitment().clone(), // q_l
            commitments[2].commitment().clone(), // q_r
            commitments[3].commitment().clone(), // q_o
            commitments[4].commitment().clone(), // q_4
            commitments[5].commitment().clone(), // q_c
            commitments[6].commitment().clone(), // q_arith
            commitments[7].commitment().clone(), // q_range
            commitments[8].commitment().clone(), // q_logic
            commitments[9].commitment().clone(), // q_lookup
            commitments[10].commitment().clone(), // q_fixed_group_add
            commitments[11].commitment().clone(), // q_variable_group_add
            commitments[12].commitment().clone(), // left_sigma
            commitments[13].commitment().clone(), // right_sigma
            commitments[14].commitment().clone(), // out_sigma
            commitments[15].commitment().clone(), // fourth_sigma
            preprocessed_table.t[0].1.clone(),
            preprocessed_table.t[1].1.clone(),
            preprocessed_table.t[2].1.clone(),
            preprocessed_table.t[3].1.clone(),
        );

        let selectors = SelectorPolynomials {
            q_m: q_m_poly,
            q_l: q_l_poly,
            q_r: q_r_poly,
            q_o: q_o_poly,
            q_c: q_c_poly,
            q_4: q_4_poly,
            q_arith: q_arith_poly,
            q_range: q_range_poly,
            q_logic: q_logic_poly,
            q_lookup: q_lookup_poly,
            q_fixed_group_add: q_fixed_group_add_poly,
            q_variable_group_add: q_variable_group_add_poly,
            left_sigma: left_sigma_poly,
            right_sigma: right_sigma_poly,
            out_sigma: out_sigma_poly,
            fourth_sigma: fourth_sigma_poly,
        };

        // Add the circuit description to the transcript
        verifier_key.seed_transcript(transcript);

        Ok((verifier_key, selectors, domain, preprocessed_table))
    }

    /// Both the [`Prover`](super::Prover) and [`Verifier`](super::Verifier)
    /// must perform IFFTs on the selector polynomials and permutation
    /// polynomials in order to commit to them and have the same transcript
    /// view.
    #[allow(clippy::type_complexity)] // FIXME: Add struct for prover side (last two tuple items).
    fn preprocess_shared_with_blinding<PC>(
        &mut self,
        commit_key: &PC::CommitterKey,
        transcript: &mut Transcript,
        _pc: PhantomData<PC>,
        blinding: &Blinding<F>,
    ) -> Result<
        (
            widget::VerifierKey<F, PC>,
            SelectorPolynomials<F>,
            GeneralEvaluationDomain<F>,
            PreprocessedLookupTable<F, PC>,
        ),
        Error,
    >
    where
        PC: HomomorphicCommitment<F>,
    {
        let domain = GeneralEvaluationDomain::new(self.circuit_bound()).ok_or(Error::InvalidEvalDomainSize {
            log_size_of_group: (self.circuit_bound()).trailing_zeros(),
            adicity:
                <<F as FftField>::FftParams as ark_ff::FftParameters>::TWO_ADICITY,
        })?;

        let preprocessed_table = PreprocessedLookupTable::<F, PC>::preprocess(
            &self.lookup_table,
            commit_key,
            domain.size() as u32,
        )
        .unwrap();

        // Check that the length of the wires is consistent.
        self.check_poly_same_len()?;

        // 1. Pad circuit to a power of two
        self.pad(domain.size() as usize - self.n);

        let poly =
            |evals| DensePolynomial::from_coefficients_vec(domain.ifft(evals));
        let mut q_m_poly: DensePolynomial<F> = poly(&self.q_m);
        let mut q_r_poly: DensePolynomial<F> = poly(&self.q_r);
        let mut q_l_poly: DensePolynomial<F> = poly(&self.q_l);
        let mut q_o_poly: DensePolynomial<F> = poly(&self.q_o);
        let mut q_c_poly: DensePolynomial<F> = poly(&self.q_c);
        let mut q_4_poly: DensePolynomial<F> = poly(&self.q_4);
        let mut q_arith_poly: DensePolynomial<F> = poly(&self.q_arith);
        let mut q_range_poly: DensePolynomial<F> = poly(&self.q_range);
        let mut q_logic_poly: DensePolynomial<F> = poly(&self.q_logic);
        let mut q_lookup_poly: DensePolynomial<F> = poly(&self.q_lookup);
        let mut q_fixed_group_add_poly: DensePolynomial<F> =
            poly(&self.q_fixed_group_add);
        let mut q_variable_group_add_poly: DensePolynomial<F> =
            poly(&self.q_variable_group_add);

        // blinding
        let z_h: DensePolynomial<F> = domain.vanishing_polynomial().into();

        // /!\ WARNING: we blind with `b0 * Z_H(X)` only /!\
        q_m_poly = q_m_poly + &z_h * blinding.q_m;
        q_r_poly = q_r_poly + &z_h * blinding.q_r;
        q_l_poly = q_l_poly + &z_h * blinding.q_l;
        q_o_poly = q_o_poly + &z_h * blinding.q_o;
        q_c_poly = q_c_poly + &z_h * blinding.q_c;
        q_4_poly = q_4_poly + &z_h * blinding.q_4;
        q_arith_poly = q_arith_poly + &z_h * blinding.q_arith;
        q_range_poly = q_range_poly + &z_h * blinding.q_range;
        q_logic_poly = q_logic_poly + &z_h * blinding.q_logic;
        q_lookup_poly = q_lookup_poly + &z_h * blinding.q_lookup;
        q_fixed_group_add_poly =
            q_fixed_group_add_poly + &z_h * blinding.q_fixed_group_add;
        q_variable_group_add_poly =
            q_variable_group_add_poly + &z_h * blinding.q_variable_group_add;

        // 2. Compute the sigma polynomials
        let (
            left_sigma_poly,
            right_sigma_poly,
            out_sigma_poly,
            fourth_sigma_poly,
        ) = self.perm.compute_sigma_polynomials(self.n, &domain);

        //left_sigma_poly = left_sigma_poly + z_h; //  * blinding.left_sigma;
        //right_sigma_poly = right_sigma_poly + &z_h * blinding.right_sigma;
        //out_sigma_poly = out_sigma_poly + &z_h * blinding.out_sigma;
        //fourth_sigma_poly = fourth_sigma_poly + &z_h * blinding.fourth_sigma;

        let (commitments, _) = PC::commit(
            commit_key,
            [
                label_polynomial!(q_m_poly),
                label_polynomial!(q_l_poly),
                label_polynomial!(q_r_poly),
                label_polynomial!(q_o_poly),
                label_polynomial!(q_4_poly),
                label_polynomial!(q_c_poly),
                label_polynomial!(q_arith_poly),
                label_polynomial!(q_range_poly),
                label_polynomial!(q_logic_poly),
                label_polynomial!(q_lookup_poly),
                label_polynomial!(q_fixed_group_add_poly),
                label_polynomial!(q_variable_group_add_poly),
                label_polynomial!(left_sigma_poly),
                label_polynomial!(right_sigma_poly),
                label_polynomial!(out_sigma_poly),
                label_polynomial!(fourth_sigma_poly),
            ]
            .iter(),
            None,
        )
        .map_err(to_pc_error::<F, PC>)?;

        let verifier_key = widget::VerifierKey::from_polynomial_commitments(
            self.n,
            commitments[0].commitment().clone(), // q_m
            commitments[1].commitment().clone(), // q_l
            commitments[2].commitment().clone(), // q_r
            commitments[3].commitment().clone(), // q_o
            commitments[4].commitment().clone(), // q_4
            commitments[5].commitment().clone(), // q_c
            commitments[6].commitment().clone(), // q_arith
            commitments[7].commitment().clone(), // q_range
            commitments[8].commitment().clone(), // q_logic
            commitments[9].commitment().clone(), // q_lookup
            commitments[10].commitment().clone(), // q_fixed_group_add
            commitments[11].commitment().clone(), // q_variable_group_add
            commitments[12].commitment().clone(), // left_sigma
            commitments[13].commitment().clone(), // right_sigma
            commitments[14].commitment().clone(), // out_sigma
            commitments[15].commitment().clone(), // fourth_sigma
            preprocessed_table.t[0].1.clone(),
            preprocessed_table.t[1].1.clone(),
            preprocessed_table.t[2].1.clone(),
            preprocessed_table.t[3].1.clone(),
        );

        let selectors = SelectorPolynomials {
            q_m: q_m_poly,
            q_l: q_l_poly,
            q_r: q_r_poly,
            q_o: q_o_poly,
            q_c: q_c_poly,
            q_4: q_4_poly,
            q_arith: q_arith_poly,
            q_range: q_range_poly,
            q_logic: q_logic_poly,
            q_lookup: q_lookup_poly,
            q_fixed_group_add: q_fixed_group_add_poly,
            q_variable_group_add: q_variable_group_add_poly,
            left_sigma: left_sigma_poly,
            right_sigma: right_sigma_poly,
            out_sigma: out_sigma_poly,
            fourth_sigma: fourth_sigma_poly,
        };

        // Add the circuit description to the transcript
        verifier_key.seed_transcript(transcript);

        Ok((verifier_key, selectors, domain, preprocessed_table))
    }
}

/// Given that the domain size is `D`
/// This function computes the `D` evaluation points for
/// the vanishing polynomial of degree `n` over a coset
pub fn compute_vanishing_poly_over_coset<F, D>(
    domain: D,        // domain to evaluate over
    poly_degree: u64, // degree of the vanishing polynomial
) -> Evaluations<F, D>
where
    F: FftField,
    D: EvaluationDomain<F>,
{
    assert!(
        (domain.size() as u64) > poly_degree,
        "domain_size = {}, poly_degree = {}",
        domain.size() as u64,
        poly_degree
    );
    let group_gen = domain.element(1);
    let coset_gen = F::multiplicative_generator().pow(&[poly_degree, 0, 0, 0]);
    let v_h: Vec<_> = (0..domain.size())
        .map(|i| {
            (coset_gen * group_gen.pow(&[poly_degree * i as u64, 0, 0, 0]))
                - F::one()
        })
        .collect();
    Evaluations::from_vec_and_domain(v_h, domain)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{batch_test_field_params, constraint_system::helper::*};
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;

    /// Tests that the circuit gets padded to the correct length.
    // FIXME: We can do this test without dummy_gadget method.
    fn test_pad<F, P>()
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        let mut composer: StandardComposer<F, P> = StandardComposer::new();
        dummy_gadget(100, &mut composer);

        // Pad the circuit to next power of two
        let next_pow_2 = composer.n.next_power_of_two() as u64;
        composer.pad(next_pow_2 as usize - composer.n);

        let size = composer.n;
        assert!(size.is_power_of_two());
        assert_eq!(composer.q_m.len(), size);
        assert_eq!(composer.q_l.len(), size);
        assert_eq!(composer.q_o.len(), size);
        assert_eq!(composer.q_r.len(), size);
        assert_eq!(composer.q_c.len(), size);
        assert_eq!(composer.q_arith.len(), size);
        assert_eq!(composer.q_range.len(), size);
        assert_eq!(composer.q_logic.len(), size);
        assert_eq!(composer.q_lookup.len(), size);
        assert_eq!(composer.q_fixed_group_add.len(), size);
        assert_eq!(composer.q_variable_group_add.len(), size);
        assert_eq!(composer.w_l.len(), size);
        assert_eq!(composer.w_r.len(), size);
        assert_eq!(composer.w_o.len(), size);
    }

    // Bls12-381 tests
    batch_test_field_params!(
        [test_pad],
        [] => (
            Bls12_381,
            ark_ed_on_bls12_381::EdwardsParameters
        )
    );

    // Bls12-377 tests
    batch_test_field_params!(
        [test_pad],
        [] => (
            Bls12_377,
            ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
