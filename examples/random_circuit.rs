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
    pub struct RandomCircuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        seed: u64, // Seed for the random number generator
        num_gates: usize, // Number of gates in each layer
        num_layers: usize, // Number of layers in the circuit
        input_values: Vec<u64>, // Input values for the circuit
        f: PhantomData<P>, // PhantomData for the JubJub curve
    }

    impl<F, P> Circuit<F, P> for RandomCircuit<F, P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        const CIRCUIT_ID: [u8; 32] = [0xff; 32];

        fn gadget(
            &mut self,
            composer: &mut StandardComposer<F, P>,
        ) -> Result<(), Error> {
            // Convert the input values to Fr
            let input_values_f = self.input_values
                .iter()
                .map(|v| F::from(*v))
                .collect::<Vec<F>>();

            // Random number from seed
            let mut rng = rand::rngs::StdRng::seed_from_u64(self.seed);

            // Create vector of input variables from input_values
            let input_vars: Vec<Variable> = input_values_f
                .iter()
                .map(|&v| composer.add_input(v))
                .collect();


            // Initialize the output variable vector to the input variables
            let mut output_vars = input_vars.clone();

            // At this point we have a layer of gates with random coefficients applied to the input variables
            // We now repeat this process until we have a circuit with a number of layers equal to num_layers
            for _ in 0..self.num_layers {
                // Print number of output variables so far:
                let mut new_output_vars:Vec<Variable> = Vec::new();
                // Pick a random with of each layer. The width range is n_gates/2
                let layer_width = rng.gen_range((self.num_gates-self.num_gates/2)..(self.num_gates+self.num_gates/2));

                // pick how many multiplication, addition, xor and range gates for the layer
                // constraing te total number of gate of being less than the layer width
                let num_mul_gates = rng.gen_range(0..layer_width);
                let num_add_gates = rng.gen_range(0..layer_width - num_mul_gates);
                let num_xor_gates = rng.gen_range(0..layer_width - num_mul_gates - num_add_gates);
                let num_range_gates = layer_width - num_mul_gates - num_add_gates - num_xor_gates;

                // create a vector of q_m, q_l, q_r for the circuit with random coefficients
                let mut q_m = vec![F::zero(); num_mul_gates];
                let mut q_l = vec![F::zero(); num_add_gates];
                let mut q_r = vec![F::zero(); num_add_gates];
                for i in 0..num_mul_gates {
                    q_m[i] = F::rand(&mut rng);
                }
                for i in 0..num_add_gates {
                    q_l[i] = F::rand(&mut rng);
                    q_r[i] = F::rand(&mut rng);
                }

                for i in 0..num_add_gates {
                    let a = output_vars[rng.gen_range(0..output_vars.len())];
                    let b = output_vars[rng.gen_range(0..output_vars.len())];
                    new_output_vars.push(
                        composer.arithmetic_gate(|gate| {
                        gate.witness(a, b, None)
                            .add(q_l[i], q_r[i])
                        })
                    );
                };
                for i in 0..num_mul_gates {
                    let a = output_vars[rng.gen_range(0..output_vars.len())];
                    let b = output_vars[rng.gen_range(0..output_vars.len())];
                    new_output_vars.push(
                        composer.arithmetic_gate(|gate| {
                        gate.witness(a, b, None)
                            .mul(q_m[i])
                        })
                    );
                };
                for _ in 0..num_xor_gates {
                    let a = output_vars[rng.gen_range(0..output_vars.len())];
                    let b = output_vars[rng.gen_range(0..output_vars.len())];
                    new_output_vars.push(
                        composer.xor_gate(a, b, 32)
                    );
                };
                for _ in 0..num_range_gates {
                    let a = output_vars[rng.gen_range(0..output_vars.len())];
                    composer.range_gate(a, 32);
                };
                output_vars = new_output_vars;
            }

            // We now want to reduce the number of outputs to 1
            // We do this by picking a random subset of the output variables and randomly adding or multiplying them together
            // We repeat this process until we have 1 output variable
            while output_vars.len() > 1 {
                let mut new_output_vars:Vec<Variable> = Vec::new();
                for _ in 0..output_vars.len()/2 {
                    let a = output_vars[rng.gen_range(0..output_vars.len())];
                    let b = output_vars[rng.gen_range(0..output_vars.len())];
                    // Randomly pick between addition and multiplication
                    if rng.gen() {
                        new_output_vars.push(
                            composer.arithmetic_gate(|gate| {
                            gate.witness(a, b, None)
                                .add(F::rand(&mut rng), F::rand(&mut rng))
                            })
                        );
                    } else {
                        new_output_vars.push(
                            composer.arithmetic_gate(|gate| {
                            gate.witness(a, b, None)
                                .mul(F::rand(&mut rng))
                            })
                        );
                    }
                };
                if output_vars.len() % 2 == 1 {
                    new_output_vars.push(output_vars[output_vars.len()-1]);
                }
                output_vars = new_output_vars;
            }

            Ok(())
        }

        fn padded_circuit_size(&self) -> usize {
            1 << 9
        }
    }

    // optimize random circuit


    // Generate CRS
    // Time to generate CRS
    let start_crs = Instant::now();
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 9, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)?;
    let end_crs = start_crs.elapsed();
    println!("Time to generate CRS: {:?}", end_crs);
    let mut circuit: RandomCircuit<BlsScalar, JubJubParameters> =
        RandomCircuit {
            seed: 701973957,
            num_gates: 50,
            num_layers: 5,
            input_values: vec![1, 2, 3, 5, 6], // Input values for the circuit
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