

# This file was *autogenerated* from the file naf.sage
from sage.all_cmdline import *   # import sage library

_sage_const_4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 = Integer(4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787); _sage_const_52435875175126190479447740508185965837690552500527637822603658699938581184513 = Integer(52435875175126190479447740508185965837690552500527637822603658699938581184513); _sage_const_0 = Integer(0); _sage_const_4 = Integer(4); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1)
p=_sage_const_4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 
Fp = GF(p)
r=_sage_const_52435875175126190479447740508185965837690552500527637822603658699938581184513 
Fr = GF(r)
E = EllipticCurve([_sage_const_0 , Fp(_sage_const_4 )])

assert E.order()%r == _sage_const_0 
cof=E.order()//r
P = cof*E.random_point()
while P.is_zero():
    P = cof*E.random_point()

def NAF(x):
    if x == _sage_const_0 :
        return []
    z = _sage_const_0  if x % _sage_const_2  == _sage_const_0  else _sage_const_2  - (x % _sage_const_4 )
    return NAF( (x-z) // _sage_const_2  ) + [z]

n = ZZ(GF(r).random_element())

# check
naf_n = NAF(n)[::-_sage_const_1 ]
assert sum([naf_n[i] * (_sage_const_1 <<i) for i in range(len(naf_n))]) % r  == ZZ(n)


def double_and_add(n) :
    # le NAF representation
    naf_n = NAF(n)[::-_sage_const_1 ]
    point_acc = E(_sage_const_0 )
    scalar_acc = _sage_const_0 
    for i in range(len(naf_n)):
        point_acc = point_acc + naf_n[i] * (_sage_const_1 <<i) * P
        scalar_acc = scalar_acc + naf_n[i] *(_sage_const_1 <<i)
        # check circuit
        acc_x = point_acc[_sage_const_0 ]
        acc_y = point_acc[_sage_const_1 ]
        multiple = (_sage_const_1 <<i) * P
        naf_multiple = naf_n[i] * multiple
        xβ = multiple[_sage_const_0 ]
        yβ = multiple[_sage_const_1 ]
        xyβ = xβ*yβ
        xα = naf_multiple[_sage_const_0 ]
        yα = naf_multiple[_sage_const_1 ]
        xyα = xα*yα
        assert acc_x * xβ + acc_y * yβ + xyβ == _sage_const_0 

    assert point_acc == n*P
    assert scalar_acc == n
    return point_acc

Q = double_and_add(n)

