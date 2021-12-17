// Randomized signature circuit

#[cfg(test)]
mod tests {
    use crate::constraint_system::StandardComposer;
    use crate::{batch_test, constraint_system::helper::*, util};
    use ark_bls12_377::Bls12_377;
    use ark_ec::models::twisted_edwards_extended::GroupAffine;
    use ark_ec::models::TEModelParameters;
    use ark_ec::AffineCurve;
    use ark_ec::PairingEngine;

    use ark_serialize::CanonicalSerialize;
    use blake2::{Blake2b512, Digest};

    use ark_ff::{PrimeField, Zero};

    fn test_randomized_signature_circuit<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                /*
                The randomization of the signature public key circuit is the following:
                * Secret: alpha a random element of P::ScalarField
                * Public: pk, rk
                Checks that rk = [alpha]rk.

                The signature public keys are points of the curve `P`, so that the circuit is modulo P::PrimeField = E::ScalarField.
                Using KZG, we can use jubjub for the signature public key and BLS12_377 for the circuit.
                 */

                ////////////////////////////////////////////////////
                // Not useful to create the circuit, but useful in order to
                // recall how works the Schnorr signature
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator: GroupAffine<P> = GroupAffine::new(x, y);
                let sk = P::ScalarField::from(1234u64);
                let pk: GroupAffine<P> = generator.mul(sk).into();
                let mut pk_bytes = vec![];
                pk.serialize(&mut pk_bytes).unwrap();
                // message
                let msg = b"Hi, Anoma!";
                // signature (s, r)
                let random_bytes: Vec<u8> =
                    (0..80).map(|_| rand::random::<u8>()).collect();
                let mut hasher = Blake2b512::new();
                hasher.update(&random_bytes);
                hasher.update(&pk_bytes);
                hasher.update(msg);
                let nonce =
                    P::ScalarField::from_le_bytes_mod_order(&hasher.finalize());
                let r = generator.mul(nonce);
                let mut r_bytes = vec![];
                r.serialize(&mut r_bytes).unwrap();
                hasher = Blake2b512::new();
                hasher.update(&r_bytes);
                hasher.update(&pk_bytes);
                hasher.update(msg);
                let c =
                    P::ScalarField::from_le_bytes_mod_order(&hasher.finalize());
                let s = nonce + c * sk;
                // verification
                let s_generator = generator.mul(s);
                let c_pk = pk.mul(c);
                assert!((s_generator - c_pk - r).is_zero());
                ////////////////////////////////////////////////////
                
                // Randomization of the public key
                let alpha = E::Fr::from(5678u64);
                let rk:GroupAffine<P> = AffineCurve::mul(
                    &pk,
                    util::to_embedded_curve_scalar::<E, P>(alpha),
                )
                .into();

                // CIRCUIT
                // Adding the secret alpha in the circuit
                let secret_alpha = composer.add_input(alpha);
                let point_pk = composer.add_affine(pk);
                // Variable scalar multiplication constraint
                let point_rk =
                    composer.variable_base_scalar_mul(secret_alpha, point_pk);
                // Final constraint
                composer.assert_equal_public_point(point_rk, rk);
                assert_eq!(composer.q_l.len(), 2031);
            },
            4096,
        );
        assert!(res.is_ok());
    }

    // Bls12-377 tests
    batch_test!(
        [
            test_randomized_signature_circuit
        ],
        [] => (
        Bls12_377,
        ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
