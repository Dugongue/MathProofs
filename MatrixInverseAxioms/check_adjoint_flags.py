"""Check the two corner flags and fixed-factor involution dimensions."""

from itertools import product
from random import Random

from check_quiver_degree import rref


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b, p):
    return [[sum(x * y for x, y in zip(row, col)) % p for col in zip(*b)]
            for row in a]


def inverse(a, p):
    n = len(a)
    rows, pivots = rref([row + unit for row, unit in zip(a, identity(n))], 2 * n, p)
    assert pivots == list(range(n))
    return [row[n:] for row in rows]


def flatten(a):
    return [x for row in a for x in row]


def basis_matrices(n):
    for i, j in product(range(n), repeat=2):
        unit = [[0] * n for _ in range(n)]
        unit[i][j] = 1
        yield unit


def adjoint(a, h, h_inv, p):
    return multiply(h_inv, multiply(transpose(a), h, p), p)


def conjugate_corner(h, cut, p, rng):
    n = len(h)
    change = identity(n)
    if n > 1:
        for _ in range(3 * n):
            i, j = rng.sample(range(n), 2)
            scalar = rng.randrange(1, p)
            change[i] = [(x + scalar * y) % p for x, y in zip(change[i], change[j])]
    e = [[int(i == j and i < cut) for j in range(n)] for i in range(n)]
    form = multiply(transpose(change), multiply(h, change, p), p)
    projector = multiply(inverse(change, p), multiply(e, change, p), p)
    return form, projector


def check(h, cut, sign, p, rng):
    n = len(h)
    form, e = conjugate_corner(h, cut, p, rng)
    h_inv = inverse(form, p)
    assert adjoint(e, form, h_inv, p) == e
    image = []
    for unit in basis_matrices(n):
        dual = adjoint(unit, form, h_inv, p)
        image.append([(x - y) % p for x, y in zip(flatten(unit), flatten(dual))])
    rank = len(rref(image, n * n, p)[1])
    if p != 2:
        expected = n * (n - sign) // 2
        assert rank == expected
    else:
        other = [[(int(i == j) - e[i][j]) % p for j in range(n)] for i in range(n)]
        for projector, indices in ((e, range(cut)), (other, range(cut, n))):
            in_image = len(rref(image + [flatten(projector)], n * n, p)[1]) == rank
            assert in_image == all(h[i][i] == 0 for i in indices)


def run():
    rng = Random(260301)
    controls = 0
    for p in (2, 3, 5, 7):
        for n in range(1, 8):
            for cut in range(n + 1):
                check(identity(n), cut, 1, p, rng)
                controls += 1
                if p == 2:
                    h = identity(n)
                    for start, stop in ((0, cut), (cut, n)):
                        if (stop - start) % 2 == 0 and rng.randrange(2):
                            for k in range(start, stop, 2):
                                h[k][k] = h[k + 1][k + 1] = 0
                                h[k][k + 1] = h[k + 1][k] = 1
                    check(h, cut, 1, p, rng)
                    controls += 1
                elif n % 2 == 0 and cut % 2 == 0:
                    h = [[0] * n for _ in range(n)]
                    for i in range(0, n, 2):
                        h[i][i + 1], h[i + 1][i] = 1, p - 1
                    check(h, cut, -1, p, rng)
                    controls += 1
    print(f"Checked {controls} adjoint and corner cases in hidden bases over four primes.")


if __name__ == "__main__":
    run()
