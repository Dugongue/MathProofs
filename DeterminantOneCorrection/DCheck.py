"""Check the ring construction over the dual numbers over F2."""
from itertools import product

ONE, EPSILON, RHO = 1, 2, 3


def mul(a, b):
    constant = (a & 1) & (b & 1)
    linear = ((a >> 1) & (b & 1)) ^ ((b >> 1) & (a & 1))
    return constant | (linear << 1)


def incidence_check(yes):
    widths = (1, 2, 2, 2, 2, 2, 2, 4, 6, 1)
    payloads = {1: (2, 3, EPSILON), 4: (5, 6, EPSILON if yes else 0)}
    slopes = {1: (ONE, ONE), 4: (RHO, ONE), 7: (ONE, 0), 8: (0, ONE)}
    pairs = {(i, i): 1 for i in range(len(widths))}
    pairs[0, 9] = 2
    for a, (b, c, _) in payloads.items():
        pairs[a, b] = pairs[b, c] = pairs[a, c] = 1
    for i in slopes:
        pairs[0, i] = pairs[i, 9] = 1
    basis = [
        (i, j, a, b, h)
        for (i, j), copies in sorted(pairs.items())
        for a, b, h in product(range(widths[i]), range(widths[j]), range(copies))
    ]
    iota = {v: i for i, v in enumerate(basis)}

    def bracket(u, v):
        i, j, a, b, h = u
        J, k, B, c, H = v
        if j != J or b != B:
            return []
        if i == j or j == k:
            return [((i, k, a, c, h if j == k else H), ONE)]
        if i == 0 and k == 9 and j in slopes:
            return [((0, 9, 0, 0, h), t) for h, t in enumerate(slopes[j]) if t]
        if i in payloads and (j, k) == payloads[i][:2] and payloads[i][2]:
            return [((i, k, a, c, 0), payloads[i][2])]
        return []

    def rotation(u):
        i, j, a, b, h = u
        p = (0, 4, 5, 6, 1, 2, 3, 7, 8, 9)
        scale = RHO if (i, j) == (0, 7) or ((i, j, h) == (0, 9, 0)) else ONE
        return (p[i], p[j], a, b, h), scale

    image = [rotation(u) for u in basis]
    assert len({iota[v] for v, _ in image}) == len(basis) == 132
    determinant = ONE
    for _, scale in image:
        determinant = mul(determinant, scale)
    assert determinant == RHO
    failures = 0
    for u, v in product(basis, repeat=2):
        left = {}
        for term, coefficient in bracket(u, v):
            moved, scale = rotation(term)
            left[moved] = mul(coefficient, scale)
        u1, scale_u = rotation(u)
        v1, scale_v = rotation(v)
        right = {term: mul(k, mul(scale_u, scale_v)) for term, k in bracket(u1, v1)}
        failures += left != right
    assert (failures == 0) == yes

    rotations = set()
    for x, y in product((ONE, RHO), repeat=2):
        action = {}
        for a in payloads:
            line = (mul(mul(x, y), slopes[a][0]), ONE)
            action[a] = 1 if line == slopes[1] else 4
            assert line == slopes[action[a]]
        if all(payloads[a][2] == payloads[b][2] for a, b in action.items()):
            rotations.add(tuple(action.items()))
    assert len(rotations) == (2 if yes else 1)
    return len(basis) ** 2, failures


if __name__ == "__main__":
    positive, _ = incidence_check(True)
    negative, failed = incidence_check(False)
    print(f"{positive} basis products preserved by the determinant-RHO rotation")
    print(f"{negative} basis products checked on the negative control, {failed} mismatches")
    print("Both tests used inputs with the same residue tensor, and the label lines reduce to the same line.")
