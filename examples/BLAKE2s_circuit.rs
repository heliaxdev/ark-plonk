// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// Copyright (c) ZK-GARAGE. All rights reserved.

//! PLONK Example

use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ec::models::twisted_edwards_extended::GroupAffine;
use ark_ec::{AffineCurve, ProjectiveCurve, TEModelParameters};
use ark_ed_on_bls12_381::{
    EdwardsParameters as JubJubParameters, Fr as JubJubScalar,
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
        // message: Vec<F>,
        // iv: Vec<F>,
        a: F,
        f: GroupAffine<P>,
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
            // input message into the circuit (here is "abc")
            let s: &str = "abc";
            let subs: Vec<[u8; 4]> = s.as_bytes()
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
            let ll = s.len();
            assert!(ll < 65);


            // SIGMA ROTATIONS
            let sigma =  vec![vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
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

            // vector h
            let h = iv.clone();
            let mut h_witness = Vec::new();
            for i in &h{
                h_witness.push(composer.add_input(F::from(*i)));
            }

            let const_1 = composer.add_input(F::from(0x1010000 as u64));
            let const_2 = composer.add_input(F::from(32 as u64));

            h_witness[0] = composer.xor_gate(h_witness[0], const_1, 32);
            h_witness[0] = composer.xor_gate(h_witness[0], const_2, 32);
            let mut v = h_witness.clone();
            for i in &iv{
                v.push(composer.add_input(F::from(*i)));
            }

            let mod_32 = |composer : &mut StandardComposer<F,P>, a_var : Variable| {
                let a = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(a_var).into_repr())[0];
                let a_mod_32 = a % u64::pow(2, 32 as u32);
                return composer.add_input(F::from(a_mod_32));
            };

            let ll_var = composer.add_input(F::from(ll as u64));
            v[12] = composer.xor_gate(v[12], ll_var, 32);

            //ADDING A COSTANT AS A VARIABLE!!!
            let f_f = composer.add_input(F::from(0xFFFFFFFF as u64));
            v[14] = composer.xor_gate(v[14], f_f, 32);

            // computes the n-bits cyclic right rotation y of a variable 32-bits x as:
            // h = x % 2**n , reminder of x and 2
            // l = x / 2**n , quotient of x and 2
            // y = 2**(32 - n) * h + l
            // x : variable to be rotated
            // n : number of bits of the rotaiton
            // k : lenght in bits of x
            let rotation =  |
                composer : &mut StandardComposer<F,P>,
                x_var: Variable,
                n :usize ,
                k :usize
            | {

                let x = <F as PrimeField>::BigInt::as_ref(&composer.value_of_var(x_var).into_repr())[0];
                // Check that x is in range 32
                composer.range_gate(x_var, k);

                // compute the quotient and reminder, render them as variables
                let h = x % (u64::pow(2, n as u32));
                let h_var = composer.add_input(F::from(h));
                let l = x / u64::pow(2, n as u32);
                let l_var = composer.add_input(F::from(l));

                // check the reminder is in range n bits. The range check in this plonk implementation
                // is valid only for even bits. Hence, to check the range of odd bits the variable
                // has to be multiplied by 2
                if n % 2 == 0 {
                    composer.range_gate(h_var, n);
                } else {
                    let two = composer.add_input(F::from(2 as u64));
                    let h_even = composer.arithmetic_gate(|gate| {
                        gate.witness(two, h_var, None)
                            .mul(F::one())
                    });
                    composer.range_gate(h_even, n + 1);
                    composer.range_gate(two, 2);
                }

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
                y_var : Variable
            | {
                // va1 = fresh((va + vb + x) % 4294967296);
                let temp1 = composer.arithmetic_gate(|gate| {
                    gate.witness(va, vb, None)
                        .add(F::one(), F::one())
                });

                let _va1 = composer.arithmetic_gate(|gate| {
                    gate.witness(temp1, x_var, None)
                        .add(F::one(), F::one())
                });
                let va1 = mod_32(composer, _va1);
                composer.range_gate(va1, 32);

                // vd1 = r1 (xor32 vd va1);
                let temp2 = composer.xor_gate(vd, va1, 32);
                let vd1 = rotation(composer, temp2, 16, 32);

                // _vc1 = fresh((vc + vd1) % 4294967296);
                let _vc1 = composer.arithmetic_gate(|gate| {
                    gate.witness(vc, vd1, None)
                        .add(F::one(), F::one())
                });
                let vc1 = mod_32(composer, _vc1);
                composer.range_gate(vc1, 32);

                // vb1 = r2 (xor32 vb vc1);
                let temp3 = composer.xor_gate(vb, vc1, 32);
                let vb1 = rotation(composer, temp3, 12, 32);

                // va2 = fresh((va1 + vb1 + y) % 4294967296);
                let temp4 = composer.arithmetic_gate(|gate| {
                    gate.witness(va1, vb1, None)
                        .add(F::one(), F::one())
                });
                let _va2 = composer.arithmetic_gate(|gate| {
                    gate.witness(temp4, y_var, None)
                        .add(F::one(), F::one())
                });
                let va2 = mod_32(composer, _va2);
                composer.range_gate(va2, 32);

                // vd2 = r3 (xor32 vd1 va2);
                let temp5 = composer.xor_gate(vd1, va2, 32);
                let vd2 = rotation(composer, temp5, 8, 32);

                // vc2 = fresh((vc1 + vd2) % 4294967296);
                let _vc2 = composer.arithmetic_gate(|gate| {
                    gate.witness(vc1, vd2, None)
                        .add(F::one(), F::one())
                });
                let vc2 = mod_32(composer, _vc2);
                composer.range_gate(vc2, 32);

                // vb2 = r4 (xor32 vb1 vc2);
                let temp6 = composer.xor_gate(vb1, vc2, 32);
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
                let temp = composer.xor_gate(h_witness[i], v[i], 32);
                h_witness[i] = composer.xor_gate(temp, v[i + 8], 32);
            };

            Ok(())
        }

        fn padded_circuit_size(&self) -> usize {
            1 << 18
        }
    }

    // Generate CRS
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 18, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)?;

    let mut circuit = Blake2Circuit::<BlsScalar, JubJubParameters>::default();
    // Compile the circuit
    let (pk_p, (vk, _pi_pos)) = circuit.compile::<PC>(&pp)?;

    let (x, y) = JubJubParameters::AFFINE_GENERATOR_COEFFS;
    let generator: GroupAffine<JubJubParameters> = GroupAffine::new(x, y);
    let point_f_pi: GroupAffine<JubJubParameters> =
        AffineCurve::mul(&generator, JubJubScalar::from(2u64).into_repr())
            .into_affine();
    // Prover POV
    let (proof, pi) = {
        let mut circuit: Blake2Circuit<BlsScalar, JubJubParameters> =
            Blake2Circuit {
                a: BlsScalar::from(20u64),
                f: point_f_pi,
            };
        circuit.gen_proof::<PC>(&pp, pk_p, b"Test")
    }?;

    // Verifier POV
    let verifier_data = VerifierData::new(vk, pi);
    verify_proof::<BlsScalar, JubJubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    )
}
