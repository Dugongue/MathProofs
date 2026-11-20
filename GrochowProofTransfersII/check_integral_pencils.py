"""Exact cyclic cubic, biquadratic and ideal-lattice examples."""
from fractions import Fraction
from functools import reduce
from itertools import product
import json
from math import gcd, lcm


def rref(rows):
    rows = [list(map(Fraction, row)) for row in rows]
    pivots = []
    for col in range(len(rows[0])):
        i = len(pivots)
        pivot = next((j for j in range(i, len(rows)) if rows[j][col]), None)
        if pivot is None:
            continue
        rows[i], rows[pivot] = rows[pivot], rows[i]
        div = rows[i][col]
        rows[i] = [v / div for v in rows[i]]
        for j in range(len(rows)):
            if j != i and rows[j][col]:
                mul = rows[j][col]
                rows[j] = [v - mul * w for v, w in zip(rows[j], rows[i])]
        pivots.append(col)
    return rows, pivots


def coordinates(basis, value):
    rows, pivots = rref([(*row, t) for row, t in zip(zip(*basis), value)])
    assert pivots == list(range(len(basis)))
    return tuple(row[-1] for row in rows)


def times(a, b, f):
    n = len(f)
    temp = [0] * (2 * n - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            temp[i + j] += x * y
    for i in range(len(temp) - 1, n - 1, -1):
        for j, c in enumerate(f):
            temp[i - n + j] -= temp[i] * c
    return tuple(temp[:n])


def evaluate(f, root):
    n = len(f)
    total = (1,) + (0,) * (n - 1)
    for a in reversed(f):
        nxt = times(total, root, f)
        total = (nxt[0] + a, *nxt[1:])
    return total


def primitive(values):
    mult = lcm(*(Fraction(x).denominator for x in values))
    row = tuple(int(x * mult) for x in values)
    div = reduce(gcd, row)
    return tuple(x // div for x in row)


def maps(f, roots):
    n = len(f)
    theta = (0, 1) + (0,) * (n - 2)
    one = (1,) + (0,) * (n - 1)
    found = {}
    assert len(set(roots)) == n and theta in roots
    for eta in roots:
        assert evaluate(f, eta) == (0,) * n
        cols = (theta, one, tuple(-x for x in times(eta, theta, f)), tuple(-x for x in eta))
        rows, pivots = rref(list(zip(*cols)))
        free = [i for i in range(4) if i not in pivots]
        if not free:
            continue
        assert len(free) == 1
        solution = [Fraction(0)] * 4
        solution[free[0]] = Fraction(1)
        for i, j in enumerate(pivots):
            solution[j] = -rows[i][free[0]]
        a, b, c, d = rep = primitive(solution)
        assert a * d - b * c
        found[eta] = rep
    return found


def dilation(f, roots):
    reps = maps(f, roots)
    nonidentity = [(a, b, c, d) for a, b, c, d in reps.values() if a != d or b or c]
    m = 1 + reduce(lambda x, y: x * abs(y), (c for _, _, c, _ in nonidentity), 1)
    determinants = []
    for a, b, c, d in nonidentity:
        assert gcd(m, c) == 1
        A, B, C, D = primitive((m * a, m * m * b, c, m * d))
        det = A * D - B * C
        assert det and det % m == 0 and abs(det) > 1
        determinants.append(det)
    return m, determinants


def biquadratic_product(a, b):
    result = [0] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            common = i & j
            result[i ^ j] += x * y * (2 if common & 1 else 1) * (3 if common & 2 else 1)
    return tuple(result)


def biquadratic_presentation(value):
    powers = [(1, 0, 0, 0)]
    for _ in range(4):
        powers.append(biquadratic_product(powers[-1], value))
    basis = powers[:4]
    f = tuple(-a for a in coordinates(basis, powers[4]))
    roots = tuple(coordinates(basis, (0, u, v, value[3] * u * v))
                  for u, v in product((-1, 1), repeat=2))
    return f, roots


def main():
    f = (-1, -2, 1)
    t = (0, 1, 0)
    u = (-2, 0, 1)
    u2 = times(u, u, f)
    v = (u2[0] - 2, *u2[1:])
    cubic = (t, u, v)
    assert len(maps(f, cubic)) == 3
    m, dets = dilation(f, cubic)
    assert m == 2 and dets == [4, 4]

    f0, roots0 = biquadratic_presentation((0, 1, 1, 0))
    assert any(a != d and not c for a, b, c, d in maps(f0, roots0).values())
    f1, roots1 = biquadratic_presentation((0, 1, 1, 1))
    reps = maps(f1, roots1)
    assert all(c or (a == d and b == 0) for a, b, c, d in reps.values())
    m1, dets1 = dilation(f1, roots1)

    # The order ideal (2, theta - 1) in Z[cube_root(7)] has index two.
    pure = (-7, 0, 0)
    nroot = (0, 2, 0)
    basis = [(2, 0, 0), (-1, 1, 0), (-1, 0, 1)]
    matrix = [coordinates(basis, times(nroot, z, pure)) for z in basis]
    assert all(v.denominator == 1 for col in matrix for v in col)
    assert all(sum(v) % 2 == 0 for v in basis)
    assert {pow(a, 3, 7) for a in range(7)}.isdisjoint({2, 5})
    print(json.dumps(dict(cyclic_scale=m, cyclic_primitive_determinants=dets,
        biquadratic_scale=m1, biquadratic_primitive_determinants=dets1,
        nonprincipal_index_two_scaled_columns=[[int(x) for x in col] for col in matrix]),
        indent=2))


if __name__ == "__main__":
    main()
