"""Exact check of split factor recovery in characteristic two.

Uses a pencil which has no invertible evaluation over F_2.  The treatment of
multiplicities 2 and 4 needs higher coefficients, because first derivatives
of the relevant factors vanish.  This is a control for the recovery step.
"""
from itertools import combinations
from random import Random


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 256:
            a ^= 0x11B
        b >>= 1
    return result


PRODUCT = [bytes(multiply(a, b) for b in range(256)) for a in range(256)]
INVERSE = [0] + [row.index(1) for row in PRODUCT[1:]]


def xor_all(values):
    result = 0
    for value in values:
        result ^= value
    return result


def dot(a, b):
    return xor_all(PRODUCT[x][y] for x, y in zip(a, b))


def matmul(a, b):
    columns = list(zip(*b))
    return [[dot(row, column) for column in columns] for row in a]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def det(a):
    rows = [row[:] for row in a]
    result = 1
    for i, row in enumerate(rows):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i]), None)
        if pivot is None:
            return 0
        rows[i], rows[pivot] = rows[pivot], row
        row = rows[i]
        result = PRODUCT[result][row[i]]
        for other in rows[i + 1:]:
            table = PRODUCT[PRODUCT[other[i]][INVERSE[row[i]]]]
            for k in range(i + 1, len(row)):
                other[k] ^= table[row[k]]
    return result


def inverse(a):
    n = len(a)
    rows = [x[:] + y for x, y in zip(a, eye(n))]
    for i in range(n):
        j = next(j for j in range(i, n) if rows[j][i])
        rows[i], rows[j] = rows[j], rows[i]
        rows[i] = [PRODUCT[INVERSE[rows[i][i]]][x] for x in rows[i]]
        for j in range(n):
            if j != i:
                rows[j] = [a ^ PRODUCT[rows[j][i]][b] for a, b in zip(rows[j], rows[i])]
    return [row[n:] for row in rows]


def pick_matrix(n, rng):
    while True:
        a = [[rng.randrange(2) for _ in range(n)] for _ in range(n)]
        if det(a):
            return a


def interpolate(values):
    n = len(values)
    coefficients = [0] * n
    for i, value in enumerate(values):
        basis, denom = [1], 1
        for j in range(n):
            if i == j:
                continue
            basis = [PRODUCT[j][x] ^ y for x, y in zip(basis + [0], [0] + basis)]
            denom = PRODUCT[denom][i ^ j]
        scale = PRODUCT[value][INVERSE[denom]]
        coefficients = [x ^ PRODUCT[scale][b] for x, b in zip(coefficients, basis)]
    return coefficients


def char_eval(m, y, shift=None, s=0):
    a = [row[:] for row in m]
    for i, row in enumerate(a):
        row[i] ^= y
        if shift is not None and s:
            for j, value in enumerate(shift[i]):
                row[j] ^= PRODUCT[s][value]
    return det(a)


def evaluate(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = PRODUCT[value][x] ^ coefficient
    return value


def div_linear(poly, root):
    quotient = [0] * (len(poly) - 1)
    carry = 0
    for i in range(len(poly) - 1, 0, -1):
        carry = poly[i] ^ PRODUCT[root][carry]
        quotient[i - 1] = carry
    return quotient


def roots(poly):
    result = {}
    for root in range(256):
        while len(poly) > 1 and evaluate(poly, root) == 0:
            result[root] = result.get(root, 0) + 1
            poly = div_linear(poly, root)
    assert len(poly) == 1
    return result


def pencil(coordinates, slices):
    n = len(slices[0])
    return [[dot(coordinates, [a[i][j] for a in slices]) for j in range(n)] for i in range(n)]


def moment(t):
    return 1, t, PRODUCT[t][t]


def reconstruct(slices):
    n = len(slices[0])
    a0 = next(a for t in range(2*n + 1) if det(a := pencil(moment(t), slices)))
    a0_inverse = inverse(a0)
    normalized = [matmul(a0_inverse, a) for a in slices]
    v, profile = None, {}
    for t in range(1 + 2 * len(list(combinations(range(n), 2)))):
        m = pencil(moment(t), normalized)
        found = roots(interpolate([char_eval(m, y) for y in range(n + 1)]))
        if len(found) > len(profile):
            v, profile = m, found
    polynomials = []
    for shift in normalized:
        by_s = [interpolate([char_eval(v, y, shift, s) for y in range(n + 1)])
                for s in range(n + 1)]
        polynomials.append([interpolate(list(values)) for values in zip(*by_s)])
    result = {}
    for root, mult in profile.items():
        b = mult & -mult
        form = []
        for coefficients in polynomials:
            local0 = interpolate([shifted(coefficients, root ^ z, 0) for z in range(n + 1)])
            locals_power = interpolate([shifted(coefficients, root ^ z, b) for z in range(n + 1)])
            assert local0[mult]
            power = PRODUCT[locals_power[mult - b]][INVERSE[local0[mult]]]
            form.append(next(x for x in range(256) if power_over_extension(x, b) == power))
        inv = INVERSE[next(x for x in form if x)]
        result[mult] = tuple(PRODUCT[v][inv] for v in form)
    return result


def shifted(coefficients, y, s_exponent):
    return evaluate([row[s_exponent] for row in coefficients], y)


def power_over_extension(x, b):
    while b > 1:
        x = PRODUCT[x][x]
        b >>= 1
    return x


def run():
    rng = Random(867421)
    forms = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (1, 1, 0)]
    profile = [form for m, form in enumerate(forms, 1) for _ in range(m)]
    n = len(profile)
    hidden_slice_map = pick_matrix(3, rng)
    expected = {m: tuple(matmul([form], hidden_slice_map)[0])
                for m, form in enumerate(forms, 1)}
    transformed_diag = matmul(profile, hidden_slice_map)
    left, right = pick_matrix(n, rng), pick_matrix(n, rng)
    upper = [
        [[transformed_diag[i][k] if i == j else rng.randrange(2) if i < j else 0
          for j in range(n)] for i in range(n)]
        for k in range(3)
    ]
    slices = [matmul(matmul(left, a), right) for a in upper]
    assert all(det(pencil((t & 1, (t >> 1) & 1, t >> 2), slices)) == 0 for t in range(8))
    assert reconstruct(slices) == expected
    print('Recovered five labeled lines in F_2^3, including multiplicities 2 and 4.')
    print('Verified that every base-field evaluation is singular.')


if __name__ == '__main__':
    run()
