"""Small exact controls for profiles, Frobenius shears and parabolic counts."""

from itertools import product
from math import gcd
from random import Random


def profile_control(p, e, n_input):
    modulus = p ** e
    units = [a for a in range(modulus) if gcd(a, p) == 1]
    n0 = 32 * n_input + 204
    epsilon = int(n0 % p == 0)
    n = n0 + epsilon
    powers = {pow(a, n, modulus) for a in units}
    if epsilon:
        parameters = [(a * a % modulus, pow(a, n, modulus)) for a in units]
        allowed_diag = powers
    else:
        parameters = [(a, pow(a, n // 2, modulus)) for a in units]
        allowed_diag = {d for _, d in parameters}
    actual = set()
    actual_diag = set()
    for eta, delta in parameters:
        for a in units:
            da = delta * pow(a, n, modulus) % modulus
            if a ** 3 * eta % modulus == 1:
                actual_diag.add(da)
            for b in units:
                c = pow(eta * a * b, -1, modulus)
                db = delta * pow(b, n, modulus) % modulus
                dc = delta * pow(c, n, modulus) % modulus
                actual.add((da, db, dc))
    if epsilon:
        expected = set(product(powers, repeat=3))
    else:
        expected = {
            (d * a % modulus, d * b % modulus, pow(d * a * b, -1, modulus))
            for d in allowed_diag for a, b in product(powers, repeat=2)
        }
    assert actual == expected and actual_diag == allowed_diag
    number = len(powers) ** 3 if epsilon else len(allowed_diag) * len(powers) ** 2
    assert len(actual) == number
    print(f"R=Z/{modulus}, N={n}, epsilon={epsilon}: {number} independent and "
          f"{len(actual_diag)} diagonal determinant profiles")


def c_entry(i, j, r):
    return int({i, j, r} == {0, 1, 2})


def c_product(left, right, field_order):
    return [
        sum(left[i] * right[j] * c_entry(i, j, r) for i, j in product(range(3), repeat=2))
        % field_order
        for r in range(3)
    ]


def multiply(a, b, p, exponent):
    modulus = p ** exponent
    s = p ** (exponent - 1)
    x, y = a[1:-1], b[1:-1]
    result = [a[0] * b[0]]
    result.extend(a[0] * v + b[0] * u for u, v in zip(x, y))
    for i, coefficient in enumerate(c_product(x, y, p), 4):
        result[i] += s * coefficient
    pairing = sum(x[i] * y[i + 3] + x[i + 3] * y[i] for i in range(3))
    result.append(a[0] * b[-1] + b[0] * a[-1] + pairing)
    return tuple(entry % modulus for entry in result)


def shear_control(p, exponent, rng):
    modulus = p ** exponent
    s = p ** (exponent - 1)
    basis = tuple(tuple(int(i == j) for i in range(8)) for j in range(8))
    for _ in range(8):
        ell = tuple(rng.randrange(modulus) for _ in range(6))
        pairing_change = [
            [sum(ell[r + 3] * c_entry(i, j, r) for r in range(3)) % p for j in range(3)]
            for i in range(3)
        ]
        if p == 2:
            assert all(pairing_change[i][i] == 0 for i in range(3))
            t = [[pairing_change[i][j] if i < j else 0 for j in range(3)] for i in range(3)]
        else:
            t = [[entry * pow(2, -1, p) % p for entry in row] for row in pairing_change]

        def apply(a):
            result = list(a)
            for i in range(3):
                result[i + 4] += s * sum(t[i][j] * a[j + 1] for j in range(3))
            result[-1] += sum(x * y for x, y in zip(ell, a[1:-1]))
            return tuple(x % modulus for x in result)

        for a, b in product(basis, repeat=2):
            assert apply(multiply(a, b, p, exponent)) == multiply(apply(a), apply(b), p, exponent)

    cube_checks = 0
    units = [r for r in range(modulus) if gcd(r, p) == 1]
    for _ in range(10):
        x = tuple(rng.randrange(modulus) for _ in range(6))
        for r in units:
            count = 0
            for cz in range(modulus):
                u = (r, *x, cz)
                cube = multiply(multiply(u, u, p, exponent), u, p, exponent)
                count += cube[-1] == 0
                cube_checks += 1
            assert count == gcd(3, modulus)
    print(f"R=Z/{modulus}: 512 basis-level shear checks and {cube_checks} cube evaluations")


def parabolic_control(p, middle):
    d = len(middle)
    q = range(p)

    def pair(a, b):
        return (a[0] * b[-1] + a[-1] * b[0]
                + sum(a[i + 1] * middle[i][j] * b[j + 1]
                      for i, j in product(range(d), repeat=2))) % p

    block_order = 0
    for entries in product(q, repeat=d * d):
        columns = [(0, *entries[j*d:(j+1)*d], 0) for j in range(d)]
        if all(pair(a, b) == middle[i][j]
               for (i, a), (j, b) in product(enumerate(columns), repeat=2)):
            block_order += 1

    count = 0
    last = (0, *(0,) * d, 1)
    for middle_entries in product(q, repeat=d * d):
        for generic in product(q, repeat=2*d+1):
            first = (1, *generic[:d], generic[d])
            columns = [(0, *middle_entries[j*d:(j+1)*d], generic[d+j+1]) for j in range(d)]
            full = (first, *columns, last)
            expected = ((0, *(0,) * d, 1), *((0, *row, 0) for row in middle),
                        (1, *(0,) * d, 0))
            if all(pair(a, b) == expected[i][j]
                   for (i, a), (j, b) in product(enumerate(full), repeat=2)):
                count += 1
    assert count == block_order * p ** d
    print(f"F_{p}, orthogonal middle dimension {d}: {count} direct parabolic completions")


if __name__ == "__main__":
    for case in ((2, 3, 3), (3, 3, 3), (5, 2, 4), (7, 2, 3)):
        profile_control(*case)
    rng = Random(101)
    for p, e in ((2, 2), (3, 2), (5, 2)):
        shear_control(p, e, rng)
    parabolic_control(3, ((1,),))
    parabolic_control(3, ((0, 1), (1, 0)))
