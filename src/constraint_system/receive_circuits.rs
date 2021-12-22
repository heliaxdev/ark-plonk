// Receive circuits

#[cfg(test)]
mod tests {
    use crate::constraint_system::StandardComposer;
    use crate::{batch_test, constraint_system::helper::*};
    use ark_bls12_377::Bls12_377;
    use ark_ec::models::twisted_edwards_extended::GroupAffine;
    use ark_ec::models::TEModelParameters;
    use ark_ec::AffineCurve;
    use ark_ec::PairingEngine;
    use crate::prelude::Variable;
    use ark_ff::Zero;
    use ark_ff::One;

    fn test_allow_all_circuit<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {
                // Empty circuit...
                // I don't know what to write here, and what would be `reject_all`.
            },
            600,
        );
        assert!(res.is_ok());
    }

    fn test_whitelist_sender_circuit<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    >() {
        let res = gadget_tester(
            |composer: &mut StandardComposer<E, P>| {

                let (x, y) = P::AFFINE_GENERATOR_COEFFS;
                let generator: GroupAffine<P> = GroupAffine::new(x, y);
                
                const N: usize = 12;

                // `whitelist` is a (secret) list of senders authorized keys
                let whitelist: Vec<GroupAffine<P>> = (0..12)
                .map(|i| generator.mul(i).into())
                .collect();

                // `sender` is a potential sender
                let sender:GroupAffine<P> = generator.mul(4).into();

                // we compute the polynomial P(X) = \prod_i (X - whitelist[i].y)
                // and the circuit checks that P(sender.y) == 0
                let zero = composer.zero_var();
                let sender_y = composer.add_input(sender.y);
                
                let mut white_list_y: [Variable;N] = [zero;N];
                let mut subst: [Variable;N] = [zero;N];
                let mut mult:[Variable;N] = [zero;N];
                mult[0] = composer.add_input(E::Fr::one());

                for i in 0..N {
                    white_list_y[i] = composer.add_input(whitelist[i].y);
                    subst[i] = composer.big_add(
                        (E::Fr::one(), sender_y),
                        (-E::Fr::one(), white_list_y[i]),
                        Some((E::Fr::one(), zero)),
                        E::Fr::zero(),
                        None,
                    );
                    if i>0 {
                        mult[i] = composer.mul(E::Fr::one(), mult[i-1], subst[i], E::Fr::zero(), None);
                    }
                }
                composer.assert_equal(mult[N-1], zero);
            },
            600,
        );
        assert!(res.is_ok());
    }

    // Bls12-377 tests
    batch_test!(
        [
            test_allow_all_circuit,
            test_whitelist_sender_circuit
        ],
        [] => (
        Bls12_377,
        ark_ed_on_bls12_377::EdwardsParameters
        )
    );
}
