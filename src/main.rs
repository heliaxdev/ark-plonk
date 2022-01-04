// use core::marker::PhantomData;
use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ec::twisted_edwards_extended::GroupAffine;
use ark_ec::{AffineCurve, PairingEngine, TEModelParameters};
use ark_ed_on_bls12_381::EdwardsAffine as JubjubAffine;
use ark_ed_on_bls12_381::EdwardsParameters as JubjubParameters;
// use ark_ed_on_bls12_381::EdwardsProjective as JubjubProjective;
use ark_ed_on_bls12_381::Fr as JubjubScalar;

use ark_ff::{BigInteger, PrimeField};
use ark_plonk::circuit::{self, Circuit, PublicInputValue, GeIntoPubInput};
use ark_plonk::prelude::*;
use num_traits::{One, Zero};
use rand_core::OsRng;

use ark_poly_commit::kzg10::KZG10;
use ark_poly::univariate::DensePolynomial;
use ark_plonk::circuit::FeIntoPubInput;
use ark_poly_commit::kzg10::UniversalParams;
use ark_ec::ProjectiveCurve;


// Implement a circuit that checks:
// 1) a + b = c where C is a PI
// 2) a <= 2^6
// 3) b <= 2^5
// 4) a * b = d where D is a PI
// 5) Jubjub::GENERATOR * e(JubjubScalar) = f where F is a Public Input
#[derive(Debug, Default)]
pub struct TestCircuit<
    E: PairingEngine,
    P: TEModelParameters<BaseField = E::Fr>,
> {
    a: E::Fr,
    b: E::Fr,
    c: E::Fr,
    d: E::Fr,
    e: P::ScalarField,
    f: GroupAffine<P>,
}
impl<
        E: PairingEngine,
        P: TEModelParameters<BaseField = E::Fr>,
    > Circuit<E, P> for TestCircuit<E, P>
{
    const CIRCUIT_ID: [u8; 32] = [0xff; 32];
    fn gadget(
        &mut self,
        composer: &mut StandardComposer<E, P>,
    ) -> Result<(), Error> {
        let a = composer.add_input(self.a);
        let b = composer.add_input(self.b);
        // Make first constraint a + b = c
        let add_result = composer.add(
          (E::Fr::one(), a),
          (E::Fr::one(), b),
          E::Fr::zero(),
          Some(-self.c),
        );
	composer.assert_equal(add_result, composer.zero_var());

        // Check that a and b are in range
        composer.range_gate(a, 1 << 6);
        composer.range_gate(b, 1 << 5);
        // Make second constraint a * b = d
        let mul_result = composer.mul(E::Fr::one(), a, b, E::Fr::zero(), Some(-self.d));
        composer.assert_equal(mul_result, composer.zero_var());

        let e_repr = self.e.into_repr().to_bytes_le();
        let e = composer.add_input(E::Fr::from_le_bytes_mod_order(&e_repr));
        let (x, y) = P::AFFINE_GENERATOR_COEFFS;
        let generator = GroupAffine::new(x, y);
        let scalar_mul_result = composer.fixed_base_scalar_mul(e, generator);
        // Apply the constrain
        composer.assert_equal_public_point(scalar_mul_result, self.f);
        Ok(())
    }
    fn padded_circuit_size(&self) -> usize {
        1 << 11
    }
}

// Now let's use the Circuit we've just implemented!
fn main() {
    let pp: UniversalParams<Bls12_381> = KZG10::<Bls12_381,DensePolynomial<BlsScalar>,>::setup(
          1 << 12, false, &mut OsRng
    ).unwrap();
    // Initialize the circuit
    // let mut circuit: TestCircuit::<
    //     Bls12_381,
    //     JubjubParameters,
    // > = TestCircuit::default();

    let mut circuit = TestCircuit::<Bls12_381, JubjubParameters>{
        a:BlsScalar::zero(),
        b:BlsScalar::zero(),
        c:BlsScalar::zero(),
        d:BlsScalar::zero(),
        e:JubjubScalar::zero(),
        f:GroupAffine::<JubjubParameters>::zero(),
    };

    // Compile the circuit
    let (pk, vd) = circuit.compile(&pp).unwrap();
    // Generator
    let (x, y) = JubjubParameters::AFFINE_GENERATOR_COEFFS;
    let generator = JubjubAffine::new(x, y);
    let point_f_pi: JubjubAffine = AffineCurve::mul(
      &generator,
      JubjubScalar::from(2u64).into_repr(),
    ).into_affine();
    let proof = {
        let mut circuit = TestCircuit {
            a: BlsScalar::from(20u64),
            b: BlsScalar::from(5u64),
            c: BlsScalar::from(25u64),
            d: BlsScalar::from(100u64),
            e: JubjubScalar::from(2u64),
            f: point_f_pi,
        };
        circuit.gen_proof(&pp, pk, b"Test").unwrap()
    };

    let public_inputs: Vec<PublicInputValue<JubjubParameters>> = vec![
        BlsScalar::from(25u64).into_pi(),
        BlsScalar::from(100u64).into_pi(),
        GeIntoPubInput::into_pi(point_f_pi)
    ];

    let ver_key = vd.key().clone();
    
    circuit::verify_proof(
        &pp,
        ver_key,
        &proof,
        &public_inputs,
        &vd.pi_pos(),
        b"Test",
    )
    .unwrap();
}
