"""Exact controls for the group law, generator construction and witness recovery."""
from itertools import product
from functools import cache
from groups import (Field, decode_conjugator, evaluate, identity,
                    restrict_to_three, subgroup_generators, substitute, translation)


def mm(k, a, b):
    out = [[0]*len(b[0]) for _ in a]
    for i, row in enumerate(a):
        for j, x in enumerate(row):
            if x:
                for s, y in enumerate(b[j]):
                    if y:
                        out[i][s] = k.add(out[i][s], k.mul(x, y))
    return out


def transporter(k, h):
    (a, b), (c, d) = h
    det = k.add(k.mul(a, d), k.mul(2, k.mul(b, c)))
    inverse_det = k.power(det, k.q-2)
    dual = [[k.mul(inverse_det, z) for z in row] for row in ((d, k.mul(2, c)), (k.mul(2, b), a))]
    m = identity(6)
    for i in range(2):
        for j in range(2):
            m[1+i][1+j], m[3+i][3+j] = h[i][j], dual[i][j]
    return m


def fast_field(modulus):
    k = Field(modulus)
    k.mul = cache(k.mul)
    k.add = cache(k.add)
    return k


if __name__ == "__main__":
    k = fast_field((0, 1))
    ext = fast_field((1, 0, 1))
    triples = [(0,0,0), (0,0,1), (0,1,1), (1,1,1)]
    bases = [[[a,b],[c,d]] for a,b,c,d in product(range(3), repeat=4) if (a*d-b*c) % 3]
    vectors = list(product(range(3), repeat=2))
    laws = transports = 0
    for values in product(range(3), repeat=4):
        g = dict(zip(triples, values))
        matrices = {x: translation(k, 2, g, x) for x in vectors}
        for x in vectors:
            for y in vectors:
                xy = tuple(k.add(i,j) for i,j in zip(x,y))
                assert mm(k, matrices[x], matrices[y]) == matrices[xy]
                laws += 1
        target_gens = subgroup_generators(k, 2, g)
        # A genuine target group element involving Frobenius, both tori and a translation.
        twist = mm(k, target_gens[1], mm(k, target_gens[-3], mm(k, target_gens[-2], target_gens[-1])))
        for h in bases:
            f = substitute(k, g, h)
            C = mm(k, twist, restrict_to_three(ext, transporter(ext, h)))
            found = decode_conjugator(k, 2, f, g, C)
            assert (found[0][0]*found[1][1]-found[0][1]*found[1][0]) % 3
            assert substitute(k, g, found) == f
            transports += 1
    # These forms first become equivalent over F_9.
    f = {(0,0,1):1, (1,1,1):1}
    g = {(0,0,1):1, (1,1,1):2}
    assert all(substitute(k, g, h) != f for h in bases)
    h = [[6,0],[0,2]]  # -i, -1
    assert substitute(ext, g, h) == f
    c = transporter(ext, h)
    shifts = subgroup_generators(ext, 2, g)
    adjusted = mm(ext, shifts[1], mm(ext, shifts[-1], c))
    recovered = decode_conjugator(ext, 2, f, g, adjusted)
    assert substitute(ext, g, recovered) == f
    xchecks = 0
    for x in product(range(9), repeat=2):
        hx = tuple(ext.total(ext.mul(a,b) for a,b in zip(row,x)) for row in h)
        assert mm(ext, c, translation(ext, 2, f, x)) == mm(ext, translation(ext, 2, g, hx), c)
        xchecks += 1
    print(f"{laws} group-law checks, {transports} prime-field transporter decodes, "
          f"{xchecks} extension-field intertwining checks. Descent example separates.")
