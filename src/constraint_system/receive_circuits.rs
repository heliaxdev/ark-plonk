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
    use crate::prelude::Point;
    use ark_ff::Zero;

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
                
                // `whitelist` is a (secret) list of senders authorized keys
                let whitelist: Vec<GroupAffine<P>> = (0..12)
                .map(|i| generator.mul(i).into())
                .collect();

                // `sender` is a potential sender
                let sender:GroupAffine<P> = generator.mul(1).into();

                // we compute the polynomial P(X) = \prod_i (X - whitelist[i].y)
                // and the circuit checks that P(sender.y) == 0
                let zero = composer.zero_var();
                let sender_y = composer.add_input(sender.y);
                let minus_white_list_0_y = composer.add_input(-whitelist[0].y);

                let output = sender.y - whitelist[0].y;
                
                let subst = composer.add(
                    (sender.y,sender_y), 
                    (-whitelist[0].y, minus_white_list_0_y),
                     -output,
                      None
                    );

                // This is not working ^
                // I use y instead of x because of TEModel (?)


                // let output2 = sender.y - whitelist[1].y;
                
                // let minus_white_list_1_y = composer.add_input(-whitelist[1].y);
                // let subst2 = composer.add(
                //     (sender.y,sender_y), 
                //     (-whitelist[1].y, minus_white_list_1_y),
                //     -output2,
                //     None
                //     );
                // composer.assert_equal(subst2, zero);

                // output *= output2;
                // let mult = composer.mul(E::Fr::from(1u64), subst, subst2, E::Fr::from(0u64), None);
                
                // composer.assert_equal(mult, zero);
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
