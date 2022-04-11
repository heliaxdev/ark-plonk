// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Elliptic Curve Fixed-Base Scalar Multiplication Gate
//!
//! NOTE: The ECC gadget does not check that the initial point is on the
//! curve for two reasons:
//! - We constrain the accumulator to start from the identity point, which the
//!   verifier knows is on the curve
//! - We are adding multiples of the generator to the accumulator which the
//!   verifier also knows is on the curve and is prime order
//! - We do allow arbitrary BlsScalar multiplication, and possibly XXX: may add
//!   constraints to ensure the generator is correct (prime order)
//!
//! Bits are accumulated in base2. So we use d(Xw) - 2d(X) to extract the
//! base2 bit.

use crate::proof_system::widget::{GateConstraint, GateValues};
use ark_ec::{ModelParameters, SWModelParameters};
use ark_ff::PrimeField;
use core::marker::PhantomData;

/// Fixed-Base Scalar Multiplication Gate
#[derive(derivative::Derivative)]
#[derivative(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FixedBaseScalarMul<F, P>(PhantomData<(F, P)>)
where
    F: PrimeField,
    P: ModelParameters<BaseField = F>;

impl<F, P> GateConstraint<F> for FixedBaseScalarMul<F, P>
where
    F: PrimeField,
    P: SWModelParameters<BaseField = F>,
{
    #[inline]
    fn constraints(separation_challenge: F, values: GateValues<F>) -> F {
        let kappa = separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;

        let x_beta_eval = values.left_selector;
        let y_beta_eval = values.right_selector;

        let acc_x = values.left;
        let acc_x_next = values.left_next;
        let acc_y = values.right;
        let acc_y_next = values.right_next;

        let xy_alpha = values.output;

        let accumulated_bit = values.fourth;
        let accumulated_bit_next = values.fourth_next;
        let bit = extract_bit(accumulated_bit, accumulated_bit_next);

        // Check bit consistency
        let bit_consistency = check_bit_consistency(bit);

        let y_alpha = bit.square() * (y_beta_eval - F::one()) + F::one();
        let x_alpha = x_beta_eval * bit;

        // xy_alpha consistency check
        let xy_consistency =
            ((bit * values.constant_selector) - xy_alpha) * kappa;

        // x accumulator consistency check
        // X3 = (X1*Y2 + X2*Y1)*(Y1*Y2-3*E.a6()) - 3*E.a6()*(Y1+Y2)*(X1+X2)
        // Z3 = (Y1+Y2)*(Y1*Y2+3*E.a6()) + 3*X1*X2*(X1*Y2 + X2*Y1)
        // Z3 * x_3 == X3
        let x_3 = acc_x_next;
        let lhs = x_3 * (acc_y+y_alpha)*(acc_y*y_alpha+3*P::COEFF_B) + x_3 * 3*acc_x*x_alpha*(acc_x*y_alpha + x_alpha*acc_y);
        let rhs = (acc_x*y_alpha + x_alpha*acc_y)*(acc_y*y_alpha-3*P::COEFF_B) - 3*P::COEFF_B*(acc_y+y_alpha)*(acc_x+x_alpha);
        let x_acc_consistency = (lhs - rhs) * kappa_sq;

        // y accumulator consistency check
        // Y3 = (Y1*Y2 + 3*E.a6())*(Y1*Y2-3*E.a6()) + 9*E.a6()*X1*X2*(X1+X2)
        // Z3 = (Y1+Y2)*(Y1*Y2+3*E.a6()) + 3*X1*X2*(X1*Y2 + X2*Y1)
        // Z3 * y_3 == Y3
        let y_3 = acc_y_next;
        let lhs = y_3 * (acc_y+y_alpha)*(acc_y*y_alpha+3*P::COEFF_B) + y_3 * 3*acc_x*x_alpha*(acc_x*y_alpha + x_alpha*acc_y);
        let rhs = (acc_y*y_alpha + 3*P::COEFF_B)*(acc_y*y_alpha-3*P::COEFF_B) + 9*P::COEFF_B*acc_x*x_alpha*(acc_x+x_alpha);
        let y_acc_consistency = (lhs - rhs) * kappa_cu;

        let checks = bit_consistency
            + x_acc_consistency
            + y_acc_consistency
            + xy_consistency;

        checks * separation_challenge
    }
}

/// Extracts the bit value from the accumulated bit.
pub(crate) fn extract_bit<F>(curr_acc: F, next_acc: F) -> F
where
    F: PrimeField,
{
    next_acc - curr_acc - curr_acc
}

/// Ensures that the bit is either `+1`, `-1`, or `0`.
pub(crate) fn check_bit_consistency<F>(bit: F) -> F
where
    F: PrimeField,
{
    let one = F::one();
    bit * (bit - one) * (bit + one)
}
