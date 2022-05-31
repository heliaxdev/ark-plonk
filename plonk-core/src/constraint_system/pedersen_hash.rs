// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Pedersen Hash Gate

use crate::constraint_system::{ecc::Point, StandardComposer};
use ark_ec::{models::{
    twisted_edwards_extended::GroupAffine as TEGroupAffine, TEModelParameters,
}, AffineCurve};
use ark_ff::PrimeField;

use super::Variable;

impl<F, P> StandardComposer<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{

    /// Computes a Pedersen hash on ed_on_bls12_377
    pub fn pedersen_hash(
        &mut self,
        elements: &[F],
    ) -> TEGroupAffine::<P> {

        let (x, y) = P::AFFINE_GENERATOR_COEFFS;
        // this would be hardocded
        let p0 = TEGroupAffine::<P>::new(x, y);
        // p1, p2, p3, p4 in the description
        let points: Vec<_> = (2..6).map(|i| p0.mul(i)).collect();

        // lets assume constant points are hardcoded.
        let CONSTANT_POINTS:Vec<_> = (7..200).map(|i| p0.mul(i)).collect();

        const N_ELEMENT_BITS_HASH: usize = 251; // instead of 252 in jubjub

        const FIELD_PRIME: usize = 251; // instead of 252 for jubjub

        let mut point = p0;

        for (i, mut x) in elements.iter().enumerate() {
            // assert 0 <= x < FIELD_PRIME
            let point_list = &CONSTANT_POINTS[2 + i * N_ELEMENT_BITS_HASH .. 2 + (i + 1) * N_ELEMENT_BITS_HASH];
            // assert len(point_list) == N_ELEMENT_BITS_HASH
            for pt in point_list {
                assert_ne!(point.x, pt.x);
                if (x & 1) {
                    point += pt;
                }
                x >>= 1;
            }
            assert_eq!(x, 0);
        }
        point
    }
}
/*
        // First component
        let scalar_a = F::from(112233u64);
        let secret_scalar_a = composer.add_input(scalar_a);
        let point_a = generator;
        let expected_component_a: TEGroupAffine<P> = AffineCurve::mul(
            &point_a,
            util::to_embedded_curve_scalar::<F, P>(scalar_a),
        )
        .into();

        // Second component
        let scalar_b = F::from(445566u64);
        let secret_scalar_b = composer.add_input(scalar_b);
        let point_b = point_a.double() + point_a;
        let expected_component_b: TEGroupAffine<P> = AffineCurve::mul(
            &point_b,
            util::to_embedded_curve_scalar::<F, P>(scalar_b),
        )
        .into();

        // Expected pedersen hash
        let expected_point = (AffineCurve::mul(
            &point_a,
            util::to_embedded_curve_scalar::<F, P>(scalar_a),
        ) + AffineCurve::mul(
            &point_b,
            util::to_embedded_curve_scalar::<F, P>(scalar_b),
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
*/

#[cfg(test)]
mod test {
    use super::*;
    use crate::{batch_test, constraint_system::helper::*};
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;

    use crate::commitment::HomomorphicCommitment;

    /// Adds two curve points together using the classical point addition
    /// algorithm. This method is slower than WNAF and is just meant to be the
    /// source of truth to test the WNAF method.
    pub fn classical_point_addition<F, P>(
        composer: &mut StandardComposer<P::BaseField, P>,
        point_a: Point<P>,
        point_b: Point<P>,
    ) -> Point<P>
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
    {
        let zero = composer.zero_var;
        let x1 = point_a.x;
        let y1 = point_a.y;

        let x2 = point_b.x;
        let y2 = point_b.y;

        // x1 * y2
        let x1_y2 = composer
            .arithmetic_gate(|gate| gate.mul(F::one()).witness(x1, y2, None));
        // y1 * x2
        let y1_x2 = composer
            .arithmetic_gate(|gate| gate.mul(F::one()).witness(y1, x2, None));
        // y1 * y2
        let y1_y2 = composer
            .arithmetic_gate(|gate| gate.mul(F::one()).witness(y1, y2, None));
        // x1 * x2
        let x1_x2 = composer
            .arithmetic_gate(|gate| gate.mul(F::one()).witness(x1, x2, None));
        // d x1x2 * y1y2
        let d_x1_x2_y1_y2 = composer.arithmetic_gate(|gate| {
            gate.mul(P::COEFF_D).witness(x1_x2, y1_y2, None)
        });

        // x1y2 + y1x2
        let x_numerator = composer.arithmetic_gate(|gate| {
            gate.witness(x1_y2, y1_x2, None).add(F::one(), F::one())
        });

        // y1y2 - a * x1x2
        let y_numerator = composer.arithmetic_gate(|gate| {
            gate.witness(y1_y2, x1_x2, None).add(F::one(), -P::COEFF_A)
        });

        // 1 + dx1x2y1y2
        let x_denominator = composer.arithmetic_gate(|gate| {
            gate.witness(d_x1_x2_y1_y2, zero, None)
                .add(F::one(), F::zero())
                .constant(F::one())
        });

        // Compute the inverse
        let inv_x_denom = composer
            .variables
            .get(&x_denominator)
            .unwrap()
            .inverse()
            .unwrap();
        let inv_x_denom = composer.add_input(inv_x_denom);

        // Assert that we actually have the inverse
        // inv_x * x = 1
        composer.arithmetic_gate(|gate| {
            gate.witness(x_denominator, inv_x_denom, Some(zero))
                .mul(F::one())
                .constant(-F::one())
        });

        // 1 - dx1x2y1y2
        let y_denominator = composer.arithmetic_gate(|gate| {
            gate.witness(d_x1_x2_y1_y2, zero, None)
                .add(-F::one(), F::zero())
                .constant(F::one())
        });

        let inv_y_denom = composer
            .variables
            .get(&y_denominator)
            .unwrap()
            .inverse()
            .unwrap();

        let inv_y_denom = composer.add_input(inv_y_denom);
        // Assert that we actually have the inverse
        // inv_y * y = 1
        composer.arithmetic_gate(|gate| {
            gate.mul(F::one())
                .witness(y_denominator, inv_y_denom, Some(zero))
                .constant(-F::one())
        });

        // We can now use the inverses

        let x_3 = composer.arithmetic_gate(|gate| {
            gate.mul(F::one()).witness(inv_x_denom, x_numerator, None)
        });

        let y_3 = composer.arithmetic_gate(|gate| {
            gate.mul(F::one()).witness(inv_y_denom, y_numerator, None)
        });

        Point::new(x_3, y_3)
    }

    fn test_curve_addition<F, P, PC>()
    where
        F: PrimeField,
        P: TEModelParameters<BaseField = F>,
        PC: HomomorphicCommitment<F>,
    {
        let res = gadget_tester::<F, P, PC>(
            |composer: &mut StandardComposer<F, P>| {
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator = TEGroupAffine::<P>::new(x, y);
                let x_var = composer.add_input(x);
                let y_var = composer.add_input(y);
                let expected_point = generator + generator;
                let point_a = Point::new(x_var, y_var);
                let point_b = Point::new(x_var, y_var);

                let point = composer.point_addition_gate(point_a, point_b);
                let point2 =
                    classical_point_addition(composer, point_a, point_b);

                composer.assert_equal_point(point, point2);

                composer.assert_equal_public_point(point, expected_point);
            },
            2000,
        );
        assert!(res.is_ok());
    }

    batch_test!(
        [test_curve_addition],
        []
        => (
            Bls12_381,
            ark_ed_on_bls12_381::EdwardsParameters
        )
    );

    batch_test!(
        [test_curve_addition],
        [] => (
            Bls12_377,
            ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
