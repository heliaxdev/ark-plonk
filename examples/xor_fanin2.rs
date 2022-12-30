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
use rand_core::OsRng;
use std::marker::PhantomData;
use std::time::Instant;

fn main() -> Result<(), Error> {
    // Implements a circuit that checks:
    // 1) a + b = c where C is a PI
    // 2) a <= 2^6
    // 3) b <= 2^4
    // 4) a * b = d where D is a PI
    // 5) JubJub::GENERATOR * e(JubJubScalar) = f where F is a PI
    #[derive(derivative::Derivative)]
    #[derivative(Debug(bound = ""), Default(bound = ""))]
    pub struct XORcircuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        f: PhantomData<P>, // PhantomData for the JubJub curve
    }

    impl<F, P> Circuit<F, P> for XORcircuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        const CIRCUIT_ID: [u8; 32] = [0xff; 32];

        fn gadget(
            &mut self,
            composer: &mut StandardComposer<F, P>,
        ) -> Result<(), Error> {

            // compute a xor between 2 Variables
            let xor = |composer : &mut StandardComposer<F,P>, a_var : Variable, b_var : Variable, range :usize| -> Variable {
                let mut _temp_var_a = a_var;
                let mut _temp_var_b = b_var;

                // Create a vector of variables that are going to be combined together to create the xor
                let mut xor_accumulator = Vec::new();

                for i in 0..range  {
                    if i < range - 1 {
                        let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var_a).into_repr())[0];
                        let b = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var_b).into_repr())[0];
                        let a_reminder = a % 2;
                        let b_reminder = b % 2;
                        let a_quotient = a / 2;
                        let b_quotient = b / 2;

                        let quotient_var_a = composer.add_input(F::from(a_quotient));
                        let quotient_var_b = composer.add_input(F::from(b_quotient));
                        let reminder_var_a = composer.add_input(F::from(a_reminder));
                        let reminder_var_b = composer.add_input(F::from(b_reminder));

                        // Check that the reminder is boolean
                        composer.boolean_gate(reminder_var_a);
                        composer.boolean_gate(reminder_var_b);

                        //Checking that the operations made by the prover are sound
                        composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_a, quotient_var_a, Some(_temp_var_a))
                                .add(F::one(), F::from(2u64))
                        });
                        composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_b, quotient_var_b, Some(_temp_var_b))
                                .add(F::one(), F::from(2u64))
                        });

                        // Compute the xor between the 2 reminders
                        // a + b - 2ab
                        let xor = a_reminder + b_reminder - 2 * a_reminder * b_reminder;
                        let xor_var = composer.add_input(F::from(xor as u64));
                        // Check that xor var was correctly computed
                        let a_plus_b = composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_a, reminder_var_b, None)
                                .add(F::one(), F::one())
                        });
                        let two_ab = composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_a, reminder_var_b, None)
                                .mul(F::from(2 as u64))
                        });

                        // Check that xor was correctly computed
                        composer.arithmetic_gate(|gate| {
                            gate.witness(xor_var, two_ab, Some(a_plus_b))
                                .add(F::one(), F::one())
                        });
                        _temp_var_a = quotient_var_a;
                        _temp_var_b = quotient_var_b;
                        xor_accumulator.push(xor_var);
                    } else {
                        let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var_a).into_repr())[0];
                        let b = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(_temp_var_b).into_repr())[0];
                        let a_reminder = a % 2;
                        let b_reminder = b % 2;
                        let a_quotient = a / 2;
                        let b_quotient = b / 2;

                        let reminder_var_a = composer.add_input(F::from(a_reminder));
                        let reminder_var_b = composer.add_input(F::from(b_reminder));
                        let quotient_var_a = composer.add_input(F::from(a_quotient));
                        let quotient_var_b = composer.add_input(F::from(b_quotient));

                        composer.boolean_gate(reminder_var_a);
                        composer.boolean_gate(reminder_var_b);
                        composer.boolean_gate(quotient_var_a);
                        composer.boolean_gate(quotient_var_b);

                        // Compute the xor between the 2 reminders
                        // a + b - 2ab
                        let xor = a_reminder + b_reminder - 2 * a_reminder * b_reminder;
                        let xor_var = composer.add_input(F::from(xor as u64));

                        // Check that xor var was correctly computed
                        let a_plus_b = composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_a, reminder_var_b, None)
                                .add(F::one(), F::one())
                        });
                        let two_ab = composer.arithmetic_gate(|gate| {
                            gate.witness(reminder_var_a, reminder_var_b, None)
                                .mul(F::from(2 as u64))
                        });

                        // Check that xor was correctly computed
                        composer.arithmetic_gate(|gate| {
                            gate.witness(xor_var, two_ab, Some(a_plus_b))
                                .add(F::one(), F::one())
                        });

                        xor_accumulator.push(xor_var);
                    }
                }


                // Combine all the xor variables together
                let mut xor_result = xor_accumulator[0];
                // print all the values in xor_result, <F

                for i in 1..xor_accumulator.len() {
                    xor_result = composer.arithmetic_gate(|gate| {
                        gate.witness(xor_result, xor_accumulator[i], None)
                            .add(F::one(), F::from(u64::pow(2, (i) as u32)))
                    });
                }
                return xor_result;
            };

            // Quick test that the xor function works
            let a = composer.add_input(F::from(4287643u64));
            let b = composer.add_input(F::from(198123u64));
            let result = composer.add_input(F::from(4352368u64));
            let xor_result = xor(composer,a, b, 23);
            composer.assert_equal(xor_result, result);


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
    let mut circuit: XORcircuit<BlsScalar, JubJubParameters> =
        XORcircuit {
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