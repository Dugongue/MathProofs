"""Exact controls for the trace centroid and the radical cube correction."""
from itertools import permutations, product
from math import gcd


def matrix_rank(rows, prime):
    basis = {}
    for row in rows:
        v = [a % prime for a in row]
        for i in range(len(v)):
            if not v[i]:
                continue
            if i not in basis:
                scale = pow(v[i], -1, prime)
                basis[i] = [a * scale % prime for a in v]
                break
            scale = v[i]
            v = [(a - scale*b) % prime for a, b in zip(v, basis[i])]
    return len(basis)


def polar_entries(blocks):
    return {entry for i in range(blocks)
            for entry in permutations(range(3*i, 3*i+3))}


def centroid_rows(blocks):
    n = 3 * blocks
    support = polar_entries(blocks)
    for a, b, c in product(range(n), repeat=3):
        for slot in (1, 2):
            row = [0] * (n*n)
            argument = (a, b, c)[slot]
            for i in range(n):
                row[i*n + a] += int((i, b, c) in support)
                value = (a, i, c) if slot == 1 else (a, b, i)
                row[i*n + argument] -= int(value in support)
            if any(row):
                yield row


def check_centroids():
    cases = 0
    for prime in (2, 3, 5):
        for blocks in range(1, 6):
            n = 3*blocks
            assert n*n - matrix_rank(centroid_rows(blocks), prime) == blocks
            cases += 1
    return cases


def check_shears():
    tests = 0
    for a, b, c, x, y, z in product(range(3), repeat=6):
        assert pow(a*x+b*y+c*z, 3, 3) == (a**3*x**3+b**3*y**3+c**3*z**3) % 3
        tests += 1
    return tests


def check_constant_fields():
    tests = 0
    for parts in ((4,3), (9,5,2), (2,7), (16,), (3,7,11)):
        for extension in range(1, 701):
            # d-cycle splits into gcd(d,extension) cycles of length d/gcd.
            total_split_factors = sum(gcd(d, extension) for d in parts)
            assert (total_split_factors == sum(parts)) == all(extension % d == 0 for d in parts)
            tests += 1
    return tests


if __name__ == "__main__":
    print("Split-centroid rank cases:", check_centroids())
    print("Pure-cube shear evaluations:", check_shears())
    print("Constant-field splitting profiles:", check_constant_fields())
