// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// Copyright (c) ZK-GARAGE. All rights reserved.

//! PLONK Example

use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ec::TEModelParameters;
use ark_ed_on_bls12_381::{
    EdwardsParameters as JubJubParameters,
};
use ark_ff::PrimeField;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use plonk::error::to_pc_error;
use plonk_core::circuit::{verify_proof, Circuit};
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use plonk_core::prelude::*;
use rand_core::{OsRng, SeedableRng};
use std::marker::PhantomData;
use std::time::Instant;
use ark_std::rand;
use rand::Rng;

fn main() -> Result<(), Error> {
    // Implements a circuit that checks:
    // 1) a + b = c where C is a PI
    // 2) a <= 2^6
    // 3) b <= 2^4
    // 4) a * b = d where D is a PI
    // 5) JubJub::GENERATOR * e(JubJubScalar) = f where F is a PI
    #[derive(derivative::Derivative)]
    #[derivative(Debug(bound = ""), Default(bound = ""))]
    pub struct Range_circuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        f: PhantomData<P>, // PhantomData for the JubJub curve
    }

    impl<F, P> Circuit<F, P> for Range_circuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        const CIRCUIT_ID: [u8; 32] = [0xff; 32];

        fn gadget(
            &mut self,
            composer: &mut StandardComposer<F, P>,
        ) -> Result<(), Error> {

            let range_in2 = |composer : &mut StandardComposer<F,P>, a_var : Variable, range : usize| {
                let mut _temp_var = a_var;

                for i in 0..range  {
                    if i < range - 1 {
                        let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var).into_repr())[0];

                        let a_reminder = a % 2;
                        let a_quotient = a / 2;
                        let quotient_var = composer.add_input(F::from(a_quotient));
                        let reminder_var = composer.add_input(F::from(a_reminder));
                        composer.boolean_gate(reminder_var);

                        //Checking that the operations made by the prover are sound
                        composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var, quotient_var, Some(_temp_var))
                                .add(F::one(), F::from(2u64))
                        });
                        _temp_var = quotient_var;
                    } else {
                        let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var).into_repr())[0];
                        let a_reminder = a % 2;
                        let a_quotient = a / 2;
                        let reminder_var = composer.add_input(F::from(a_reminder));
                        let quotient_var = composer.add_input(F::from(a_quotient));
                        composer.boolean_gate(reminder_var);
                        composer.boolean_gate(quotient_var);
                    }
                }
            };

            let a = composer.add_input(F::from(16u64));
            range_in2(composer, a, 8);
            Ok(())
        }
        fn padded_circuit_size(&self) -> usize {
            1 << 9
        }
    }

    // Generate CRS
    // Time to generate CRS
    let start_crs = Instant::now();
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 9, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)?;
    let end_crs = start_crs.elapsed();
    println!("Time to generate CRS: {:?}", end_crs);
    let mut circuit: Range_circuit<BlsScalar, JubJubParameters> =
        Range_circuit {
            f: PhantomData, // PhantomData for the JubJub curve
        };

    // Compile the circuit
    // Time to compile the circuit
    let start_comp = Instant::now();
    let (pk_p, (vk, _pi_pos)) = circuit.compile::<PC>(&pp)?;
    let end_comp = start_comp.elapsed();
    println!("Time to compile the circuit: {:?}", end_comp);

    // Prover POV
    // Time to generate proof
    let start_proof = Instant::now();
    let (proof, pi) = {
        circuit.gen_proof::<PC>(&pp, pk_p, b"Test")
    }?;
    let end_proof = start_proof.elapsed();
    println!("Time to generate proof: {:?}", end_proof);

    // Verifier POV
    // Time to verify proof
    let start_verify = Instant::now();
    let verifier_data = VerifierData::new(vk, pi);
    verify_proof::<BlsScalar, JubJubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    )?;
    let end_verify = start_verify.elapsed();
    println!("Time to verify proof: {:?}", end_verify);
    Ok(())
}
