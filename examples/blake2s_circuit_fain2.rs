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
    pub struct Blake2Circuit<F, P>
        where
            F: PrimeField,
            P: TEModelParameters<BaseField = F>,
    {
        s: Box<str>,
        f: PhantomData<P>,
    }

    impl<F, P> Circuit<F, P> for Blake2Circuit<F, P>
        where
            F: PrimeField,
            P: TEModelParameters<BaseField = F>,
    {
        const CIRCUIT_ID: [u8; 32] = [0xff; 32];

        fn gadget(
            &mut self,
            composer: &mut StandardComposer<F, P>,
        ) -> Result<(), Error> {
            // Define helper clousres
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


            let subs: Vec<[u8; 4]> = self.s.as_bytes()
                .chunks(4)
                .map(|buf| {
                    let mut arr = [0; 4];
                    arr[..buf.len()].copy_from_slice(buf);
                    arr
                })
                .collect();

            let mut message:Vec<u64> = Vec::new();
            for i in subs{
                message.push((i[0] as u64) + (i[1] as u64)*u64::pow(16, 2 as u32) + (i[2] as u64)*u64::pow(16, 4 as u32) + (i[3] as u64)*u64::pow(16, 6 as u32));
            }
            while message.len() < 16 {
                message.push(0 as u64);
            }
            // ll is the number of bytes of the input message
            let ll:usize = self.s.len();
            assert!(ll < 65);

            // SIGMA ROTATIONS
            let sigma:Vec<Vec<usize>> = vec![vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
                                             vec![14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
                                             vec![11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
                                             vec![7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
                                             vec![9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
                                             vec![2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
                                             vec![12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
                                             vec![13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
                                             vec![6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
                                             vec![10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]];

            // Initialization vector
            let iv : Vec<u64> = vec![1779033703,3144134277,1013904242,2773480762,1359893119,2600822924,528734635,1541459225];

            let const_1 = composer.add_input(F::from(0x1010000 as u64));
            let const_2 = composer.add_input(F::from(32 as u64));
            composer.constrain_to_constant(const_1,F::from(0x1010000 as u64), None);
            composer.constrain_to_constant(const_2, F::from(32 as u64), None);

            // vector h
            let h = iv.clone();
            let mut h_witness :Vec<Variable> = Vec::new();

            for (i, h_i) in h.iter().enumerate(){
                h_witness.push(composer.add_input(F::from(*h_i)));
                composer.constrain_to_constant(h_witness[i],F::from(*h_i), None);
            };

            h_witness[0] = xor(composer, h_witness[0], const_1, 32);
            h_witness[0] = xor(composer, h_witness[0], const_2, 32);
            let mut v = h_witness.clone();
            for i in &iv{
                v.push(composer.add_input(F::from(*i)));
            }


            // mudlo 2^32 operation
            let mod_32 = |composer : &mut StandardComposer<F,P>, a_var : Variable| {
                //composer.range_gate(a_var, 32);
                let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(a_var).into_repr())[0];
                let a_reminder = a % u64::pow(2, 32 as u32);
                let a_quotient = a / u64::pow(2, 32 as u32);

                let quotient_var = composer.add_input(F::from(a_quotient));
                let reminder_var = composer.add_input(F::from(a_reminder));

                //Checking that the operations made by the prover are sound
                composer.arithmetic_gate(|gate| {
                    gate.witness(reminder_var, quotient_var, Some(a_var))
                        .add( F::one(), F::from(u64::pow(2, 32 as u32)))
                });
                range_in2(composer, quotient_var, 32);
                return reminder_var;
            };

            let ll_var = composer.add_input(F::from(ll as u64));
            v[12] = xor(composer,v[12], ll_var, 32);

            let f_f = composer.add_input(F::from(0xFFFFFFFF as u64));
            composer.constrain_to_constant(f_f,F::from(0xFFFFFFFF as u64), None);
            v[14] = xor(composer,v[14], f_f, 32);

            // computes the n-bits cyclic right rotation y of a variable
            let rotation =  |
                composer : &mut StandardComposer<F,P>,
                x_var: Variable,
                n :usize ,
                k :usize
            | {
                range_in2(composer, x_var, 32);
                let x = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(x_var).into_repr())[0];
                // Check that x is in range 32
                // composer.range_gate(x_var, k);

                // compute the quotient and reminder, render them as variables
                let h = x % (u64::pow(2, n as u32));
                let h_var = composer.add_input(F::from(h));
                let l = x / u64::pow(2, n as u32);
                let l_var = composer.add_input(F::from(l));

                // check the reminder is in range n bits
                range_in2(composer, h_var, n);

                // check that x = 2^n * l + h
                composer.arithmetic_gate(|gate| {
                    gate.witness(l_var, h_var, Some(x_var))
                        .add(F::from(u64::pow(2, n as u32)), F::one())
                });

                // output y = 2**(k-n) * h + l, the rotation of x
                let y_var = composer.arithmetic_gate(|gate| {
                    gate.witness(h_var, l_var, None)
                        .add(F::from(u64::pow(2, (k - n) as u32)), F::one())
                });

                return y_var;
            };

            // G mixing function, build using rotation closure above
            let g_mix = |
                composer: &mut StandardComposer<F, P>,
                va: Variable,
                vb: Variable,
                vc: Variable,
                vd: Variable,
                x_var : Variable,
                y_var : Variable            // Build a test for the rotation function

            | {
                // Check that the input variables are in range_
                range_in2(composer, x_var, 32);
                range_in2(composer, y_var, 32);

                let temp1 = composer.arithmetic_gate(|gate| {
                    gate.witness(va, vb, None)
                        .add(F::one(), F::one())
                });

                let _va1 = composer.arithmetic_gate(|gate| {
                    gate.witness(temp1, x_var, None)
                        .add(F::one(), F::one())
                });

                let va1 = mod_32(composer, _va1);

                let temp2 = xor(composer,vd, va1, 32);
                let vd1 = rotation(composer, temp2, 16, 32);

                let _vc1 = composer.arithmetic_gate(|gate| {
                    gate.witness(vc, vd1, None)
                        .add(F::one(), F::one())
                });
                let vc1 = mod_32(composer, _vc1);

                let temp3 = xor(composer,vb, vc1, 32);
                let vb1 = rotation(composer, temp3, 12, 32);

                let temp4 = composer.arithmetic_gate(|gate| {
                    gate.witness(va1, vb1, None)
                        .add(F::one(), F::one())
                });
                let _va2 = composer.arithmetic_gate(|gate| {
                    gate.witness(temp4, y_var, None)
                        .add(F::one(), F::one())
                });
                let va2 = mod_32(composer, _va2);

                let temp5 = xor(composer,vd1, va2, 32);
                let vd2 = rotation(composer, temp5, 8, 32);

                let _vc2 = composer.arithmetic_gate(|gate| {
                    gate.witness(vc1, vd2, None)
                        .add(F::one(), F::one())
                });
                let vc2 = mod_32(composer, _vc2);

                let temp6 = xor(composer,vb1, vc2, 32);
                let vb2 = rotation(composer, temp6, 7, 32);

                return (va2, vb2, vc2, vd2);
            };

            // Complete G function operation
            let g_total = |
                composer: &mut StandardComposer<F, P>,
                v : &mut Vec<Variable> ,
                m : Vec<Variable> ,
                sigma : Vec<usize>,
            | {
                // Columns
                (v[0], v[4], v[8], v[12]) = g_mix(composer, v[0], v[4], v[8], v[12],m[sigma[0]], m[sigma[1]]);
                (v[1], v[5], v[9], v[13]) = g_mix(composer,v[1], v[5], v[9], v[13], m[sigma[2]], m[sigma[3]]);
                (v[2], v[6], v[10], v[14]) = g_mix(composer,v[2], v[6], v[10], v[14], m[sigma[4]], m[sigma[5]]);
                (v[3], v[7], v[11], v[15]) = g_mix(composer,v[3], v[7], v[11], v[15], m[sigma[6]], m[sigma[7]]);

                // Diagonals
                (v[0], v[5], v[10], v[15]) = g_mix(composer, v[0], v[5], v[10], v[15], m[sigma[8]], m[sigma[9]]);
                (v[1], v[6], v[11], v[12]) = g_mix(composer, v[1], v[6], v[11], v[12], m[sigma[10]], m[sigma[11]]);
                (v[2], v[7], v[8], v[13]) = g_mix(composer, v[2], v[7], v[8], v[13], m[sigma[12]], m[sigma[13]]);
                (v[3], v[4], v[9], v[14]) = g_mix(composer, v[3], v[4], v[9], v[14], m[sigma[14]], m[sigma[15]]);
            };


            let mut m = Vec::new();
            for i in &message{
                m.push(composer.add_input(F::from(*i)));
            };

            // (352957251, 3810779495, 2237070752, 544337075)
            for i in 0..10{
                g_total(composer, &mut v, m.clone(), sigma[i].clone());
            }

            // XOR HALVES
            for i in 0..8{
                let temp = xor(composer,h_witness[i], v[i], 32);
                h_witness[i] = xor(composer,temp, v[i + 8], 32);
            };

            // Test vector form reference implementation
            let h_test:Vec<usize> = vec![0x8C5E8C50, 0xE2147C32, 0xA32BA7E1, 0x2F45EB4E, 0x208B4537,
                                         0x293AD69E, 0x4C9B994D, 0x82596786];
            // Check validity of the hash:
            for (i, h_i) in h_test.iter().enumerate(){
                composer.constrain_to_constant(h_witness[i],F::from(*h_i as u64), None);
            };
            Ok(())
        }

        fn padded_circuit_size(&self) -> usize {
            1 << 18
        }
    }

    // Generate CRS
    // Time to generate CRS
    let start_crs = Instant::now();
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 18, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)?;
    let end_crs = start_crs.elapsed();
    println!("Time to generate CRS: {:?}", end_crs);
    let mut circuit = Blake2Circuit::<BlsScalar, JubJubParameters>::default();
    // Compile the circuit
    // Time to compile the circuit
    let start_comp = Instant::now();
    let (pk_p, (vk, _pi_pos)) = circuit.compile::<PC>(&pp)?;
    let end_comp = start_comp.elapsed();
    println!("Time to compile the circuit: {:?}", end_comp);

    //INPUT MESSAGE
    const MESS: &str = "abc";

    // Prover POV
    // Time to generate proof
    let start_proof = Instant::now();
    let (proof, pi) = {
        let mut circuit: Blake2Circuit<BlsScalar, JubJubParameters> =
            Blake2Circuit {
                s: Box::from(MESS),
                f: PhantomData
            };
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