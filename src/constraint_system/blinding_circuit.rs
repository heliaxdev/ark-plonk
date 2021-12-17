// PBC blinding circuit

use crate::constraint_system::ecc::Point;
use crate::constraint_system::{variable::Variable, StandardComposer};
use ark_ec::models::twisted_edwards_extended::{GroupAffine, GroupProjective};
use ark_ec::models::TEModelParameters;
use ark_ec::{ModelParameters, PairingEngine, ProjectiveCurve};
use ark_ff::{BigInteger, FpParameters, PrimeField};
use num_traits::{One, Zero};

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
                let mut buf = [
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
    
    // Bls12-377 tests
    batch_test!(
        [
            test_blinding_circuit
        ],
        [] => (
        Bls12_377,
        ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
