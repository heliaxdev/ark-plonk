p=4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
Fp = GF(p)
r=52435875175126190479447740508185965837690552500527637822603658699938581184513
Fr = GF(r)
E = EllipticCurve([0, Fp(4)])

assert E.order()%r == 0
cof=E.order()//r
P = cof*E.random_point()
while P.is_zero():
    P = cof*E.random_point()

def NAF(x):
    if x == 0:
        return []
    z = 0 if x % 2 == 0 else 2 - (x % 4)
    return NAF( (x-z) // 2 ) + [z]

n = ZZ(GF(r).random_element())

# check
naf_n = NAF(n)[::-1]
assert sum([naf_n[i] * (1<<i) for i in range(len(naf_n))]) % r  == ZZ(n)


def double_and_add(n) :
    # le NAF representation
    naf_n = NAF(n)[::-1]
    point_acc = E(0)
    scalar_acc = 0
    for i in range(len(naf_n)):
        if i>0:
            old_acc_x = acc_x
            old_acc_y = acc_y
            old_xy_α = xy_α
        point_acc = point_acc + naf_n[i] * (1<<i) * P
        scalar_acc = scalar_acc + naf_n[i] *(1<<i)
        # check circuit
        acc_x = point_acc[0]
        acc_y = point_acc[1]
        multiple = (1<<i) * P
        naf_multiple = naf_n[i] * multiple
        xβ = multiple[0]
        yβ = multiple[1]
        xyβ = xβ*yβ
        xα = naf_multiple[0]
        yα = naf_multiple[1]
        xyα = xα*yα
    assert point_acc == n*P
    assert scalar_acc == n
    return point_acc

Q = double_and_add(n)