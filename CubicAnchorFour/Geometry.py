"""Finite controls for the cubic-anchor groupoid and the translation planes."""

from itertools import product
from random import Random


def matrix_product(left, right, p):
    return tuple(tuple(sum(a * b for a, b in zip(row, column)) % p
                       for column in zip(*right)) for row in left)


def matrix_sum(*matrices, p):
    return tuple(tuple(sum(entries) % p for entries in zip(*rows))
                 for rows in zip(*matrices))


def delta(f, u, p):
    a, b, c, d = u
    columns = ((2 * a[0], 2 * b[0], 2 * c[0], 0),
               (a[1], b[1] + a[0], c[1] + b[0], c[0]),
               (0, 2 * a[1], 2 * b[1], 2 * c[1]),
               tuple(2 * d[2] * scalar for scalar in f))
    return tuple(tuple(x % p for x in row) for row in zip(*columns))


def full(f, u, w, p):
    correction = delta(f, u, p)
    rows = []
    for i in range(11):
        row = [int(i == j) for j in range(11)]
        if 3 <= i < 7:
            row[:3] = u[i - 3]
        if i >= 7:
            row[:3] = w[i - 7]
            row[3:7] = correction[i - 7]
        rows.append(tuple(row))
    return tuple(rows)


def add_tuple(x, y, p):
    return tuple((a + b) % p for a, b in zip(x, y))


def scale(x, a, p):
    return tuple(a * b % p for b in x)


def relation_shift(f, q, lam, p):
    return (add_tuple((*q, 0), scale(f, lam[0], p), p),
            add_tuple((0, *q), scale(f, lam[1], p), p))


def product_vector(f, phi, left, right, p):
    # Orders x,y,z ; x²,xy,y²,z² ; x³,x²y,xy²,y³, without the unit.
    out = [0] * 11
    basis = ((1, 0, 0), (0, 1, 0), (0, 0, 1),
             (2, 0, 0), (1, 1, 0), (0, 2, 0), (0, 0, 2),
             (3, 0, 0), (2, 1, 0), (1, 2, 0), (0, 3, 0))
    indices = {item: j for j, item in enumerate(basis)}
    for i, a in enumerate(left):
        if not a:
            continue
        for j, b in enumerate(right):
            if not b:
                continue
            x, y, z = (c + d for c, d in zip(basis[i], basis[j]))
            if x + y + z > 3:
                continue
            if z and x + y == 1 and z == 1:
                for k, entry in enumerate(phi[y]):
                    out[7 + k] += a * b * entry
            elif z and x + y:
                continue
            elif z == 3:
                for k, entry in enumerate(f):
                    out[7 + k] += a * b * entry
            else:
                out[indices[(x, y, z)]] += a * b
    return tuple(x % p for x in out)


def apply(matrix, vector, p):
    return tuple(sum(a * b for a, b in zip(row, vector)) % p for row in matrix)


def check_groupoid():
    rng = Random(729)
    checks = 0
    for p in (2, 3, 5):
        def random_vector(dim):
            return tuple(rng.randrange(p) for _ in range(dim))

        basis = tuple(tuple(int(i == j) for j in range(11)) for i in range(11))
        for _ in range(30):
            f = random_vector(4)
            u, v, u2, v2 = (tuple(random_vector(3) for _ in range(4)) for _ in range(4))
            first, second = full(f, u, v, p), full(f, u2, v2, p)
            central = matrix_sum(v, v2, matrix_product(delta(f, u, p), u2, p), p=p)
            assert matrix_product(first, second, p) == full(f, matrix_sum(u, u2, p=p), central, p)
            phi = (random_vector(4), random_vector(4))
            shift = relation_shift(f, tuple(row[2] for row in u[:3]), u[3][:2], p)
            target = tuple(add_tuple(source, scale(correction, -1, p), p)
                           for source, correction in zip(phi, shift))
            columns = tuple(zip(*first))
            for i, j in product(range(11), repeat=2):
                assert apply(first, product_vector(f, phi, basis[i], basis[j], p), p) == \
                       product_vector(f, target, columns[i], columns[j], p)
                checks += 1
    return checks


def plane(f, p):
    out = set()
    for a, b in product(range(p), repeat=2):
        fx, fy = scale(f, a, p), scale(f, b, p)
        out.add((fx[3], fy[0], (fy[1] - fx[0]) % p,
                 (fy[2] - fx[1]) % p, (fy[3] - fx[2]) % p))
    return frozenset(out)


def check_grassmannian():
    points, tangents = 0, 0
    for p in (2, 3, 5):
        all_cubics = tuple(product(range(p), repeat=4))
        projective = tuple(f for f in all_cubics if next((x for x in f if x), 0) == 1)
        planes = set()
        for f in projective:
            image = plane(f, p)
            assert len(image) == p * p and image not in planes
            planes.add(image)
            line = {scale(f, x, p) for x in range(p)}
            for g in all_cubics:
                assert (plane(g, p) <= image) == (g in line)
                tangents += 1
        points += len(planes)
    return points, tangents


if __name__ == "__main__":
    print("Ring-homomorphism products checked:", check_groupoid())
    print("Projective translation planes and tangent choices:", check_grassmannian())
