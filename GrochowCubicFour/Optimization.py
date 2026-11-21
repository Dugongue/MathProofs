from itertools import combinations, product
from math import gcd
from random import Random


def additive(table, key, value, mod):
    total = (table.get(key, 0) + value) % mod
    if total:
        table[key] = total
    else:
        table.pop(key, None)


def mul(left, right, top, mod):
    out = {}
    for a, av in left.items():
        for b, bv in right.items():
            c = tuple(x + y for x, y in zip(a, b))
            if sum(c) > 3 or c[2] and (c[0] or c[1]):
                continue
            if c == (0, 0, 3):
                for monomial, coefficient in top.items():
                    additive(out, monomial, av * bv * coefficient, mod)
            else:
                additive(out, c, av * bv, mod)
    return out


def substitute(poly, images, top, mod):
    out = {}
    for monomial, coefficient in poly.items():
        term = {(0, 0, 0): coefficient}
        for i, power in enumerate(monomial):
            for _ in range(power):
                term = mul(term, images[i], top, mod)
        for key, value in term.items():
            additive(out, key, value, mod)
    return out


def jet_trials():
    xs = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    degree_three = tuple((i, 3 - i, 0) for i in range(4))
    basis = tuple((i, k - i, 0) for k in range(4) for i in range(k + 1))
    basis += ((0, 0, 1), (0, 0, 2))
    rng = Random(918)
    product_checks = 0
    for mod in (3, 4, 7, 8):
        for run in range(8):
            f = {monomial: rng.randrange(mod) for monomial in degree_three} if run else {}
            shear = rng.randrange(mod)
            normalized = ({xs[0]: 1}, {xs[0]: shear, xs[1]: 1}, {xs[2]: 1})
            g = substitute(f, normalized, {}, mod)
            units = tuple(k for k in range(1, mod) if gcd(k, mod) == 1)
            a = units[run % len(units)]
            filtered = ({xs[0]: a, (2, 0, 0): 1},
                        {xs[0]: (a * shear) % mod, xs[1]: a, (1, 1, 0): 1},
                        {xs[2]: a, (0, 0, 2): 1})
            if not f:
                filtered[0][(0, 0, 2)] = 1
            for u, v in product(basis, repeat=2):
                up = substitute({u: 1}, filtered, g, mod)
                vp = substitute({v: 1}, filtered, g, mod)
                left = substitute(mul({u: 1}, {v: 1}, f, mod), filtered, g, mod)
                assert left == mul(up, vp, g, mod)
                product_checks += 1
            inverse_scalar = pow(a, -1, mod)
            extracted = tuple({monomial: coefficient * inverse_scalar % mod
                               for monomial, coefficient in image.items() if sum(monomial) == 1}
                              for image in filtered[:2]) + ({xs[2]: 1},)
            assert substitute(f, extracted, {}, mod) == g
    return product_checks


def minor_trials():
    checked = 0
    nilpotent_example = False
    for mod in (3, 4, 7, 8):
        for x, y, a in product(range(mod), repeat=3):
            mat = [[x, 0, 0], [y, x, 0], [0, y, 0], [0, 0, a]]
            minors = [(mat[i][k] * mat[j][ell] - mat[i][ell] * mat[j][k]) % mod
                      for i, j in combinations(range(4), 2)
                      for k, ell in combinations(range(3), 2)]
            vanishes = not any(minors)
            assert vanishes == (not any(v % mod for v in (x*x, y*y, x*y, a*x, a*y)))
            if vanishes and gcd(x, y, a, mod) == 1:
                assert x == y == 0
            if mod == 4 and (x, y, a) == (2, 0, 0):
                nilpotent_example = vanishes
            checked += 1
    assert nilpotent_example
    return checked


def matrix_mul(left, right, mod):
    return [[sum(x * y for x, y in zip(row, col)) % mod
             for col in zip(*right)] for row in left]


def matrix_add(left, right, mod, coefficient=1):
    return [[(x + coefficient * y) % mod for x, y in zip(row, line)]
            for row, line in zip(left, right)]


def geometric_trials():
    rng = Random(137)
    mod = 16
    size = 3
    identity = [[int(i == j) for j in range(size)] for i in range(size)]
    for trial in range(64):
        e = [[2 * rng.randrange(8) for _ in range(size)] for _ in range(size)]
        if trial == 0:
            e = [[2 * x for x in row] for row in identity]
        e2 = matrix_mul(e, e, mod)
        e3 = matrix_mul(e2, e, mod)
        e4 = matrix_mul(e3, e, mod)
        assert all(not any(row) for row in e4)
        if trial == 0:
            assert e3 != e4
        u_prime = [row[:] for row in identity]
        multiplier = rng.randrange(mod)
        u_prime[0][1] = multiplier
        inverse = [row[:] for row in identity]
        inverse[0][1] = -multiplier
        u = matrix_mul(inverse, matrix_add(identity, e, mod, -1), mod)
        series = matrix_add(matrix_add(matrix_add(identity, e, mod), e2, mod), e3, mod)
        corrected = matrix_mul(series, u_prime, mod)
        assert matrix_mul(corrected, u, mod) == identity
        assert matrix_mul(u, corrected, mod) == identity
    return 64


def main():
    assert jet_trials() == 4608
    assert minor_trials() == 946
    assert geometric_trials() == 64
    print("4,608 filtered jet multiplication tests, 946 complete minor cases, "
          "and 64 geometric-inverse tests passed.")


if __name__ == "__main__":
    main()

