// Randomized signature circuit

#[cfg(test)]
mod tests {
    use crate::{batch_test, constraint_system::helper::*, util};
    use ark_bls12_377::Bls12_377;
    use ark_ec::AffineCurve;
    use ark_ec::PairingEngine;
    use ark_ec::models::TEModelParameters;
    use crate::constraint_system::ecc::Point;
    use crate::constraint_system::StandardComposer;
    use ark_ec::models::twisted_edwards_extended::GroupAffine;

    use ark_serialize::CanonicalSerialize;
    use blake2::{Blake2b512,Digest};

    use ark_ff::{PrimeField, Zero};
    
    fn test_randomized_signature_circuit<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                
                // Before looking at a circuit, we create an example of Schnorr signature.
                // The signature is done using ed_on_bls12_377 so that we can build circuit with ed_on_bls12_377::BaseField, which is bls12_377::ScalarField.
                
                // secret key
                let mut sk = P::ScalarField::from(1234u64);

                
                // public key
                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator: GroupAffine<P> = GroupAffine::new(x, y);
                let mut pk:GroupAffine<P> = generator.mul(sk).into();
                let mut pk_bytes = vec![];
                pk.serialize(&mut pk_bytes).unwrap();
                

                // message
                let msg = b"Hi, Anoma!";

                // signature (s, r)
                let random_bytes: Vec<u8> = (0..80).map(|_| { rand::random::<u8>() }).collect();
        
                let mut hasher = Blake2b512::new();
                hasher.update(&random_bytes);
                hasher.update(&pk_bytes);
                hasher.update(msg);
                let nonce = P::ScalarField::from_le_bytes_mod_order(&hasher.finalize());
                
                let r = generator.mul(nonce);
                let mut r_bytes = vec![];
                r.serialize(&mut r_bytes).unwrap();
                
                hasher = Blake2b512::new();
                hasher.update(&r_bytes);
                hasher.update(&pk_bytes);
                hasher.update(msg);

                let c = P::ScalarField::from_le_bytes_mod_order(&hasher.finalize());

                let s = nonce + c * sk;

                // verification
                let s_generator = generator.mul(s);                
                let c_pk = pk.mul(c);
                assert!((s_generator - c_pk - r).is_zero());

                // randomization
                let rho = P::ScalarField::from(5678u64);
                sk += rho;
                pk = pk.mul(rho).into();

                // ???
            },
            600,
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
