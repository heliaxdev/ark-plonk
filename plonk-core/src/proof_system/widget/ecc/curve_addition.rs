// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Elliptic Curve Point Addition Gate

use crate::proof_system::widget::{GateConstraint, GateValues};
use ark_ec::{ModelParameters, SWModelParameters};
use ark_ff::PrimeField;
use core::marker::PhantomData;

/// Curve Addition Gate
#[derive(derivative::Derivative)]
#[derivative(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct CurveAddition<F, P>(PhantomData<(F, P)>)
where
    F: PrimeField,
    P: ModelParameters<BaseField = F>;

impl<F, P> GateConstraint<F> for CurveAddition<F, P>
where
    F: PrimeField,
    P: SWModelParameters<BaseField = F>,
{
    #[inline]
    fn constraints(separation_challenge: F, values: GateValues<F>) -> F {
        let x_1 = values.left;
        let x_3 = values.left_next;
        let y_1 = values.right;
        let y_3 = values.right_next;
        let x_2 = values.output;
        let y_2 = values.fourth;
        let x1_y2 = values.fourth_next;

        let kappa = separation_challenge.square();

        // Check that `x1 * y2` is correct
        let xy_consistency = x_1 * y_2 - x1_y2;

        /*
        p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
        Fp = GF(p)
        E = EllipticCurve(Fp, [0,5])
        assert E.order().is_prime()

        P = E.random_point()
        Q = E.random_point()

        def complete_addition(P, Q):
            X1,Y1 = P[0],P[1]
            X2,Y2 = Q[0],Q[1]

            X3 = (X1*Y2 + X2*Y1)*(Y1*Y2-3*E.a6()) - 3*E.a6()*(Y1+Y2)*(X1+X2)
            Y3 = (Y1*Y2 + 3*E.a6())*(Y1*Y2-3*E.a6()) + 9*E.a6()*X1*X2*(X1+X2)
            Z3 = (Y1+Y2)*(Y1*Y2+3*E.a6()) + 3*X1*X2*(X1*Y2 + X2*Y1)
            return E(X3/Z3, Y3/Z3)

        for i in range(10):
            assert P+Q == complete_addition(P, Q)
            assert 2*P == complete_addition(P, P)
        */
        
        // Formula of Algorithm 7 of eprint 2015/1060 with affine points (z=1)
        // X3 = (X1*Y2 + X2*Y1)*(Y1*Y2-3*E.a6()) - 3*E.a6()*(Y1+Y2)*(X1+X2)
        // Y3 = (Y1*Y2 + 3*E.a6())*(Y1*Y2-3*E.a6()) + 9*E.a6()*X1*X2*(X1+X2)
        // Z3 = (Y1+Y2)*(Y1*Y2+3*E.a6()) + 3*X1*X2*(X1*Y2 + X2*Y1)
        // i.e.
        // X3 = (x1_y2 + x2_y1)*(y1_y2-b_3) - b_3*y1_p_y2*x1_p_x2
        // Y3 = (y1_y2 + b_3)*(y1_y2-b_3) + 3* b_3*x1_x2*x1_p_x2
        // Z3 = y1_p_y2*(y1_y2+b_3) + 3*x1_x2*(x1_y2 + x2_y1)

        let b_3 = P::COEFF_B+P::COEFF_B+P::COEFF_B;
        let x1_x2 = x_1.mul(x_2);
        let y1_y2 = y_1.mul(y_2);
        let x1_y2 = x_1.mul(y_2);
        let x2_y1 = x_2.mul(y_1);
        let x1_p_x2 = x_1 + x_2;
        let y1_p_y2 = y_1 + y_2;
        
        let x3_lhs = x_3 * (y1_p_y2*(y1_y2+b_3) + 3*x1_x2*(x1_y2 + x2_y1));
        let x3_rhs = (x1_y2 + x2_y1)*(y1_y2-b_3) - b_3*y1_p_y2*x1_p_x2;
        let x3_consistency = (x3_lhs - x3_rhs) * kappa;

        let y3_lhs = y_3 * (y1_p_y2*(y1_y2+b_3) + 3*x1_x2*(x1_y2 + x2_y1));
        let y3_rhs = (y1_y2 + b_3)*(y1_y2-b_3) + 3* b_3*x1_x2*x1_p_x2;
        let y3_consistency = (y3_lhs - y3_rhs) * kappa.square();

        (xy_consistency + x3_consistency + y3_consistency)
            * separation_challenge
    }
}
