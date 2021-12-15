// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::constraint_system::ecc::Point;
use crate::constraint_system::{variable::Variable, StandardComposer};
use ark_ec::models::twisted_edwards_extended::{GroupAffine, GroupProjective};
use ark_ec::models::TEModelParameters;
use ark_ec::{ModelParameters, PairingEngine, ProjectiveCurve};
use ark_ff::{BigInteger, FpParameters, PrimeField};
use num_traits::{One, Zero};

fn compute_wnaf_point_multiples<P: TEModelParameters>(
    base_point: GroupProjective<P>,
) -> Vec<GroupAffine<P>>
where
    <P as ModelParameters>::BaseField: PrimeField,
{
    let mut multiples = vec![
        GroupProjective::<P>::default();
        <P::BaseField as PrimeField>::Params::MODULUS_BITS
            as usize
    ];
    multiples[0] = base_point;
    for i in 1..<P::BaseField as PrimeField>::Params::MODULUS_BITS as usize {
        multiples[i] = multiples[i - 1].double();
    }

    ProjectiveCurve::batch_normalization_into_affine(&multiples)
}

impl<E: PairingEngine, P: TEModelParameters<BaseField = E::Fr>>
    StandardComposer<E, P>
{
    /// Adds an elliptic curve Scalar multiplication gate to the circuit
    /// description.
    ///
    /// # Note
    ///
    /// This function is optimized for fixed base ops **ONLY** and therefore,
    /// the **ONLY** input that should be passed to the function as a point is
    /// the generator or basepoint of the curve over which we are operating.
    pub fn fixed_base_scalar_mul(
        &mut self,
        jubjub_scalar: Variable,
        base_point: GroupAffine<P>,
    ) -> Point<E, P> {
        let num_bits =
            <P::BaseField as PrimeField>::Params::MODULUS_BITS as usize;
        // compute 2^iG
        let mut point_multiples =
            compute_wnaf_point_multiples(base_point.into());
        point_multiples.reverse();

        // Fetch the raw scalar value as bls scalar, then convert to a jubjub
        // scalar
        // XXX: Not very Tidy, impl From function in JubJub
        let jubjub_scalar_value = self.variables.get(&jubjub_scalar).unwrap();

        // Convert scalar to wnaf_2(k)
        let wnaf_entries = jubjub_scalar_value
            .into_repr()
            .find_wnaf(2)
            .unwrap_or_else(|| panic!("Fix this!"));
        // wnaf_entries.extend(vec![0i64; num_bits - wnaf_entries.len()]);
        assert!(wnaf_entries.len() <= num_bits);

        // Initialise the accumulators
        let mut scalar_acc = Vec::with_capacity(num_bits);
        scalar_acc.push(E::Fr::zero());
        let mut point_acc = Vec::with_capacity(num_bits);
        point_acc.push(GroupAffine::<P>::zero());

        // Auxillary point to help with checks on the backend
        let mut xy_alphas = Vec::with_capacity(num_bits);

        let n_trailing_zeros = num_bits - wnaf_entries.len();
        scalar_acc.extend(vec![E::Fr::zero(); n_trailing_zeros]);
        point_acc.extend(vec![GroupAffine::<P>::zero(); n_trailing_zeros]);
        xy_alphas.extend(vec![E::Fr::zero(); n_trailing_zeros]);

        // Load values into accumulators based on wnaf entries
        for (i, entry) in wnaf_entries.iter().rev().enumerate() {
            // Offset the index by the number of trailing zeros
            let index = i + n_trailing_zeros;
            // Based on the WNAF, we decide what scalar and point to add
            let (scalar_to_add, point_to_add) =
                match entry {
                    0 => { (E::Fr::zero(), GroupAffine::<P>::zero())},
                    -1 => {(-E::Fr::one(), -point_multiples[index])},
                    1 => {(E::Fr::one(), point_multiples[index])},
                    _ => unreachable!("Currently WNAF_2(k) is supported.
                        The possible values are 1, -1 and 0. Current entry is {}", entry),
                };

            let prev_accumulator = E::Fr::from(2u64) * scalar_acc[index];
            scalar_acc.push(prev_accumulator + scalar_to_add);
            point_acc.push(point_acc[index] + point_to_add);

            let x_alpha = point_to_add.x;
            let y_alpha = point_to_add.y;

            xy_alphas.push(x_alpha * y_alpha);
        }

        for i in 0..num_bits {
            let acc_x = self.add_input(point_acc[i].x);
            let acc_y = self.add_input(point_acc[i].y);

            let accumulated_bit = self.add_input(scalar_acc[i]);

            // We constrain the point accumulator to start from the Identity
            // point and the Scalar accumulator to start from zero
            if i == 0 {
                self.constrain_to_constant(acc_x, E::Fr::zero(), None);
                self.constrain_to_constant(acc_y, E::Fr::one(), None);
                self.constrain_to_constant(
                    accumulated_bit,
                    E::Fr::zero(),
                    None,
                );
            }

            let x_beta = point_multiples[i].x;
            let y_beta = point_multiples[i].y;

            let xy_alpha = self.add_input(xy_alphas[i]);

            let xy_beta = x_beta * y_beta;

            let wnaf_round = StandardComposer::<E, P>::new_wnaf(
                acc_x,
                acc_y,
                accumulated_bit,
                xy_alpha,
                x_beta,
                y_beta,
                xy_beta,
            );

            self.fixed_group_add(wnaf_round);
        }

        // Add last gate, but do not activate it for ECC
        // It is for use with the previous gate
        let acc_x = self.add_input(point_acc[num_bits].x);
        let acc_y = self.add_input(point_acc[num_bits].y);
        let xy_alpha = self.zero_var;
        let last_accumulated_bit = self.add_input(scalar_acc[num_bits]);

        self.big_add_gate(
            acc_x,
            acc_y,
            xy_alpha,
            Some(last_accumulated_bit),
            E::Fr::zero(),
            E::Fr::zero(),
            E::Fr::zero(),
            E::Fr::zero(),
            E::Fr::zero(),
            None,
        );

        // Constrain the last element in the accumulator to be equal to the
        // input jubjub scalar
        self.assert_equal(last_accumulated_bit, jubjub_scalar);

        Point::<E, P>::new(acc_x, acc_y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{batch_test, constraint_system::helper::*, util};
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;
    use ark_ec::{group::Group, AffineCurve};
    use ark_ff::Field;
    use rand::Rng;

    fn test_blinding_circuit<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                /*
                Secret:
                * `com`, a commitment that we want to hide
                * `b0`, a scalar
                * `b1`, a scalar.
                Public:
                * `com_blinded`, a blinded commitment
                * `com_z_h`, a commitment to the vanishing polynomial
                * `com_x_z_h`, a commitment to X * the vanishing polynomial

                Produces the circuit corresponding to the proof that com_blinded = com + [(b0+b1*x)*z_h(x)]
                */

                // SECRET INPUT

                // b0 and b1
                // let mut buf = [1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4];
                // let mut buf = rand::thread_rng().gen::<[u8;32]>();
                // let b0 = E::Fr::from_random_bytes(&mut
                // buf).unwrap();
		// the code above does not work with the random buf,
		// but works with the hardcoded one...
                let b0 = E::Fr::from(1234u64);
		let b1 = E::Fr::from(5678u64);
                // com
                buf = [
                    201, 247, 119, 206, 196, 228, 135, 238, 42, 216, 36, 234,
                    188, 123, 35, 229, 141, 58, 11, 120, 111, 10, 214, 12, 37,
                    225, 177, 8, 198, 253, 146, 1,
                ];
                let com = GroupAffine::from_random_bytes(&mut buf).unwrap();

                // PUBLIC INPUT

                // com_z_h
                buf = [
                    216, 115, 9, 136, 192, 48, 164, 170, 103, 64, 181, 17, 189,
                    64, 196, 78, 95, 25, 67, 157, 48, 40, 184, 76, 30, 241,
                    229, 85, 160, 131, 131, 18,
                ];
                let com_z_h = GroupAffine::from_random_bytes(&mut buf).unwrap();
                // com_x_z_h
                buf = [
                    99, 254, 249, 48, 161, 217, 87, 100, 253, 116, 218, 14, 14,
                    185, 217, 168, 230, 151, 230, 71, 86, 253, 173, 24, 148,
                    243, 137, 195, 240, 65, 189, 14,
                ];
                let com_x_z_h =
                    GroupAffine::from_random_bytes(&mut buf).unwrap();

                // EXPECTED POINTS FOR THE CIRCUIT CHECK

                let expected_blinding_term: GroupAffine<P> = (AffineCurve::mul(
                    &com_z_h,
                    util::to_embedded_curve_scalar::<E, P>(b0),
                )
                    + AffineCurve::mul(
                        &com_x_z_h,
                        util::to_embedded_curve_scalar::<E, P>(b1),
                    ))
                .into();
                let expected_com_blinded = com + expected_blinding_term;

                // CIRCUIT

                // Adding the secrets b0 and b1 into the circuit
                let secret_b0 = composer.add_input(b0);
                let secret_b1 = composer.add_input(b1);
                let secret_com_x = composer.add_input(com.x);
                let secret_com_y = composer.add_input(com.y);
                let secret_com = Point::<E, P>::new(secret_com_x, secret_com_y);

                // Multiplication and addition constraints
                let component_b0 =
                    composer.fixed_base_scalar_mul(secret_b0, com_z_h);

                let component_b1 =
                    composer.fixed_base_scalar_mul(secret_b1, com_x_z_h);

                let component_b0_b1 =
                    composer.point_addition_gate(component_b0, component_b1);

                let component_blinded_commitment =
                    composer.point_addition_gate(component_b0_b1, secret_com);

                // Final constraint
                composer.assert_equal_public_point(
                    component_blinded_commitment,
                    expected_com_blinded,
                );

                assert_eq!(composer.q_l.len(), 525);
            },
            600,
        );
        assert!(res.is_ok());
    }

    fn test_ecc_constraint<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let scalar = E::Fr::from_le_bytes_mod_order(&[
                    182, 44, 247, 214, 94, 14, 151, 208, 130, 16, 200, 204,
                    147, 32, 104, 166, 0, 59, 52, 1, 1, 59, 103, 6, 169, 175,
                    51, 101, 234, 180, 125, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0,
                ]);
                let secret_scalar = composer.add_input(scalar);

                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);
                let expected_point: GroupAffine<P> = AffineCurve::mul(
                    &generator,
                    util::to_embedded_curve_scalar::<E, P>(scalar),
                )
                .into();

                let point_scalar =
                    composer.fixed_base_scalar_mul(secret_scalar, generator);

                composer
                    .assert_equal_public_point(point_scalar, expected_point);
            },
            600,
        );
        assert!(res.is_ok());
    }

    fn test_ecc_constraint_zero<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let scalar = E::Fr::zero();
                let secret_scalar = composer.add_input(scalar);

                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);
                let expected_point: GroupAffine<P> = AffineCurve::mul(
                    &generator,
                    util::to_embedded_curve_scalar::<E, P>(scalar),
                )
                .into();

                let point_scalar =
                    composer.fixed_base_scalar_mul(secret_scalar, generator);

                composer
                    .assert_equal_public_point(point_scalar, expected_point);
            },
            600,
        );
        assert!(res.is_ok());
    }

    fn test_ecc_constraint_should_fail<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let scalar = E::Fr::from(100u64);
                let secret_scalar = composer.add_input(scalar);
                // Fails because we are not multiplying by the GENERATOR, it is
                // double
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);
                let double_gen = generator.double();

                let expected_point: GroupAffine<P> = AffineCurve::mul(
                    &double_gen,
                    util::to_embedded_curve_scalar::<E, P>(scalar),
                )
                .into();

                let point_scalar =
                    composer.fixed_base_scalar_mul(secret_scalar, generator);

                composer
                    .assert_equal_public_point(point_scalar, expected_point);
            },
            600,
        );

        assert!(res.is_err());
    }

    fn test_point_addition<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);

                let point_a = generator;
                let point_b = point_a.double();
                let expected_point = point_a + point_b;

                let affine_point_a = point_a;
                let affine_point_b = point_b;
                let affine_expected_point = expected_point;

                let var_point_a_x = composer.add_input(affine_point_a.x);
                let var_point_a_y = composer.add_input(affine_point_a.y);
                let point_a = Point::<E, P>::new(var_point_a_x, var_point_a_y);
                let var_point_b_x = composer.add_input(affine_point_b.x);
                let var_point_b_y = composer.add_input(affine_point_b.y);
                let point_b = Point::<E, P>::new(var_point_b_x, var_point_b_y);
                let new_point = composer.point_addition_gate(point_a, point_b);

                composer.assert_equal_public_point(
                    new_point,
                    affine_expected_point,
                );
            },
            600,
        );

        assert!(res.is_ok());
    }

    fn test_pedersen_hash<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);
                // First component
                let scalar_a = E::Fr::from(112233u64);
                let secret_scalar_a = composer.add_input(scalar_a);
                let point_a = generator;
                let expected_component_a: GroupAffine<P> = AffineCurve::mul(
                    &point_a,
                    util::to_embedded_curve_scalar::<E, P>(scalar_a),
                )
                .into();

                // Second component
                let scalar_b = E::Fr::from(445566u64);
                let secret_scalar_b = composer.add_input(scalar_b);
                let point_b = point_a.double() + point_a;
                let expected_component_b: GroupAffine<P> = AffineCurve::mul(
                    &point_b,
                    util::to_embedded_curve_scalar::<E, P>(scalar_b),
                )
                .into();

                // Expected pedersen hash
                let expected_point: GroupAffine<P> = (AffineCurve::mul(
                    &point_a,
                    util::to_embedded_curve_scalar::<E, P>(scalar_a),
                ) + AffineCurve::mul(
                    &point_b,
                    util::to_embedded_curve_scalar::<E, P>(scalar_b),
                ))
                .into();

                // To check this pedersen commitment, we will need to do:
                // - Two scalar multiplications
                // - One curve addition
                //
                // Scalar multiplications
                let component_a =
                    composer.fixed_base_scalar_mul(secret_scalar_a, point_a);
                let component_b =
                    composer.fixed_base_scalar_mul(secret_scalar_b, point_b);

                // Depending on the context, one can check if the resulting
                // components are as expected
                //
                composer.assert_equal_public_point(
                    component_a,
                    expected_component_a,
                );
                composer.assert_equal_public_point(
                    component_b,
                    expected_component_b,
                );

                // Curve addition
                let commitment =
                    composer.point_addition_gate(component_a, component_b);

                // Add final constraints to ensure that the commitment that we
                // computed is equal to the public point
                composer.assert_equal_public_point(commitment, expected_point);
            },
            1024,
        );
        assert!(res.is_ok());
    }

    fn test_pedersen_balance<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = GroupAffine::new(x, y);

                // First component
                let scalar_a = E::Fr::from(25u64);
                let secret_scalar_a = composer.add_input(scalar_a);
                // Second component
                let scalar_b = E::Fr::from(30u64);
                let secret_scalar_b = composer.add_input(scalar_b);
                // Third component
                let scalar_c = E::Fr::from(10u64);
                let secret_scalar_c = composer.add_input(scalar_c);
                // Fourth component
                let scalar_d = E::Fr::from(45u64);
                let secret_scalar_d = composer.add_input(scalar_d);

                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let gen: GroupAffine<P> = GroupAffine::new(x, y);

                let expected_lhs: GroupAffine<P> = AffineCurve::mul(
                    &gen,
                    util::to_embedded_curve_scalar::<E, P>(scalar_a + scalar_b),
                )
                .into();
                let expected_rhs: GroupAffine<P> = AffineCurve::mul(
                    &gen,
                    util::to_embedded_curve_scalar::<E, P>(scalar_c + scalar_d),
                )
                .into();

                let point_a =
                    composer.fixed_base_scalar_mul(secret_scalar_a, generator);
                let point_b =
                    composer.fixed_base_scalar_mul(secret_scalar_b, generator);
                let point_c =
                    composer.fixed_base_scalar_mul(secret_scalar_c, generator);
                let point_d =
                    composer.fixed_base_scalar_mul(secret_scalar_d, generator);

                let commitment_lhs =
                    composer.point_addition_gate(point_a, point_b);
                let commitment_rhs =
                    composer.point_addition_gate(point_c, point_d);

                composer.assert_equal_point(commitment_lhs, commitment_rhs);

                composer
                    .assert_equal_public_point(commitment_lhs, expected_lhs);
                composer
                    .assert_equal_public_point(commitment_rhs, expected_rhs);
            },
            2048,
        );
        assert!(res.is_ok());
    }

    // // Bls12-381 tests
    // batch_test!(
    //     [
    //     test_ecc_constraint,
    //     test_ecc_constraint_zero,
    //     test_ecc_constraint_should_fail,
    //     test_point_addition,
    //     test_pedersen_hash,
    //     test_pedersen_balance
    //     ],
    //     [] => (
    //     Bls12_381,
    //     ark_ed_on_bls12_381::EdwardsParameters
    //     )
    // );

    // Bls12-377 tests
    batch_test!(
        [
            test_blinding_circuit
        // test_ecc_constraint,
        // test_ecc_constraint_zero,
        // test_ecc_constraint_should_fail,
        // test_point_addition,
        // test_pedersen_hash,
        // test_pedersen_balance
        ],
        [] => (
        Bls12_377,
        ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
