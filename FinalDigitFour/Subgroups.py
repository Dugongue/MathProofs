"""Finite checks of the regular socle representations and explicit reductions."""
from itertools import product
from random import Random


def add(x, y, modulus):
    return tuple((a + b) % modulus for a, b in zip(x, y))


def build(p, e, coeff):
    modulus = p**e
    socle = p**(e - 1)
    # Coordinate order: X, Y, X*, two hyperbolic axes, two outputs, padding.
    d = 1 if 9 % p else 2
    n = 7 + d
    zero = (0,) * n
    basis = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))

    def bilinear(x, y):
        data = coeff * (x[0] * y[1] + x[1] * y[0])
        tag = x[0] * y[2] + x[2] * y[0] + x[3] * y[4] + x[4] * y[3]
        return (0,) * 5 + (socle * data % modulus, socle * tag % modulus) + (0,) * d

    def affine(x, y):
        return add(add(x, y, modulus), bilinear(x, y), modulus)

    def ordered_coordinates(values):
        result = zero
        for i, value in enumerate(values):
            result = affine(result, tuple(value * a for a in basis[i]))
        return result

    def matrix(x):
        cols = ((1,) + x,) + tuple((0,) + add(b, bilinear(x, b), modulus) for b in basis)
        return tuple(zip(*cols))

    return modulus, socle, basis, bilinear, affine, ordered_coordinates, matrix


def multiply(left, right, modulus):
    return tuple(
        tuple(sum(a * b for a, b in zip(row, col)) % modulus for col in zip(*right))
        for row in left
    )


def rank(m, p):
    a = [list(row) for row in m]
    i = 0
    for j in range(len(a[0])):
        pivot = next((r for r in range(i, len(a)) if a[r][j] % p), None)
        if pivot is None:
            continue
        a[i], a[pivot] = a[pivot], a[i]
        inv = pow(a[i][j] % p, -1, p)
        for r in range(i + 1, len(a)):
            scale = a[r][j] * inv
            a[r] = [(u - scale * v) % p for u, v in zip(a[r], a[i])]
        i += 1
    return i


def run_case(p, e):
    rng = Random(2027)
    modulus, socle, basis, bilinear, affine, coords, matrix = build(p, e, 1)
    _, _, _, _, _, _, matrix_zero = build(p, e, 0)
    _, _, _, _, _, _, matrix_scaled = build(p, e, p - 1)
    n = len(basis)
    for v in basis:
        assert bilinear(v, v) == (0,) * n
        left = matrix(v)
        right = matrix_zero(v)
        assert all((x - y) % socle == 0 for ra, rb in zip(left, right) for x, y in zip(ra, rb))
        assert all(left[i][i] == 1 for i in range(n + 1))
        assert all(left[i][j] == 0 for i in range(n + 1) for j in range(i + 1, n + 1))

    for _ in range(24):
        x, y = [tuple(rng.randrange(modulus) for _ in basis) for _ in range(2)]
        assert affine(coords(x), coords(y)) == coords(add(x, y, modulus))
        raw = coords(x)
        correction = coords(raw[:5] + (0, 0) + raw[7:])
        recovered = raw[:5] + tuple((raw[i] - correction[i]) % modulus for i in (5, 6)) + raw[7:]
        assert recovered == x
        assert multiply(matrix(x), matrix(y), modulus) == matrix(affine(x, y))
        scale = p - 1
        diag = [1] * (n + 1)
        diag[6] = scale
        diag[-1] = pow(scale, -1, modulus)
        transported = tuple(a * d % modulus for a, d in zip(x, diag[1:]))
        source = matrix(x)
        target = matrix_scaled(transported)
        assert all(
            diag[i] * source[i][j] % modulus == target[i][j] * diag[j] % modulus
            for i, j in product(range(n + 1), repeat=2)
        )

    for data, tag in product(range(p), repeat=2):
        m = [[0] * 5 for _ in range(5)]
        for i, j, v in [(0, 1, data), (0, 2, tag), (3, 4, tag)]:
            m[i][j] = m[j][i] = v
        assert rank(m, p) == (4 if tag else 2 if data else 0)
    print(f"Z/{modulus}: {n} generators, 24 group-law and SL conjugator checks, {p*p} slice ranks")


def main():
    for p, e in [(2, 2), (2, 3), (3, 2), (5, 2)]:
        run_case(p, e)


if __name__ == "__main__":
    main()
