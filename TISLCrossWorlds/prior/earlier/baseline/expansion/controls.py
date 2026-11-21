"""Exact bounded audits of complementary channels, count normalization, and matrix criteria."""

import itertools
import json
import math


def channel_cases():
    tested = 0
    for modulus in range(2, 16):
        for bit, x in itertools.product(range(2), range(modulus)):
            valid = [
                (p, q) for p, q in itertools.product(range(modulus), repeat=2)
                if (p + q) % modulus == x and (not p if bit == 0 else not q)
            ]
            assert valid == [(bit * x, (1 - bit) * x)]
            tested += modulus ** 2
    return tested


def bounded_counts():
    tested = 0
    for bound in range(1, 65):
        for count in range(bound + 1):
            exact = sum((-1) ** (i + 1) * math.comb(count, i)
                        for i in range(1, bound + 1))
            assert exact == int(count > 0)
            tested += 1
    values = (3, 5, 11, 27, 81)
    normalization = math.prod(values)
    for count in (0,) + values:
        assert normalization - math.prod(s - count for s in values) == (
            normalization if count else 0
        )
        tested += 1
    return tested


def vmul(matrix, vector, prime):
    return tuple(sum(a * b for a, b in zip(row, vector)) % prime for row in matrix)


def rank(matrix, prime):
    work = [list(row) for row in matrix]
    height = len(work)
    pivots = 0
    for col in range(len(work[0])):
        pivot = next((i for i in range(pivots, height) if work[i][col] % prime), None)
        if pivot is None:
            continue
        work[pivots], work[pivot] = work[pivot], work[pivots]
        scale = pow(work[pivots][col] % prime, -1, prime)
        for row in range(pivots + 1, height):
            factor = work[row][col] * scale
            work[row] = [(a - factor * b) % prime for a, b in zip(work[row], work[pivots])]
        pivots += 1
        if pivots == height:
            break
    return pivots


def rank_controls():
    tests = 0
    for entries in itertools.product(range(5), repeat=4):
        matrix = (entries[:2], entries[2:])
        true_rank = rank(matrix, 5)
        for r in (1, 2):
            witnesses = []
            for t, s in itertools.product(range(5), repeat=2):
                left = [[pow(t, i*j, 5) for j in range(2)] for i in range(1, r+1)]
                right = [[pow(s, i*j, 5) for j in range(2)] for i in range(1, r+1)]
                compressed = [[sum(a*b for a, b in zip(row, vmul(matrix, col, 5))) % 5
                               for col in right] for row in left]
                witnesses.append(rank(compressed, 5) == r)
                tests += 1
            assert any(witnesses) == (true_rank >= r)
    return tests


def matmul(a, b, p):
    return tuple(tuple(sum(x*y for x, y in zip(row, col)) % p
                       for col in zip(*b)) for row in a)


def minimal_controls():
    tests = 0
    identity = ((1, 0), (0, 1))
    for p in (2, 3):
        for entries in itertools.product(range(p), repeat=4):
            matrix = (entries[:2], entries[2:])
            square = matmul(matrix, matrix, p)
            power_vectors = [tuple(itertools.chain.from_iterable(x))
                             for x in (identity, matrix, square)]
            for degree in (1, 2):
                for cf in itertools.product(range(p), repeat=degree):
                    coeff = cf + (1,)
                    annihilates = all(sum(w*v for w, v in zip(coeff, vec)) % p == 0
                                      for vec in zip(*power_vectors[:degree+1]))
                    independent = rank(list(power_vectors[:degree]), p) == degree
                    if degree == 1:
                        expected = matrix == (((-cf[0]) % p, 0), (0, (-cf[0]) % p))
                    else:
                        a,b,c,d = entries
                        expected = not (b==c==0 and a==d) and cf == ((a*d-b*c)%p, (-a-d)%p)
                    assert (annihilates and independent) == expected
                    tests += 1
    return tests


def planar_matching_controls():
    tested = 0
    for availability in itertools.product((0, 1), repeat=4):
        a, b, c, d = availability
        host_signed_determinant = a*d+b*c
        matching_count = sum(all(availability[2*i+perm[i]] for i in range(2))
                             for perm in itertools.permutations(range(2)))
        assert host_signed_determinant == matching_count
        tested += 1
    return tested


if __name__ == "__main__":
    print(json.dumps({
        "cyclic_complementary_channel_assignments": channel_cases(),
        "gap_count_normalizations": bounded_counts(),
        "two_sided_rank_compressions": rank_controls(),
        "minimal_polynomial_coefficient_tests": minimal_controls(),
        "planar_subgraph_matching_tests": planar_matching_controls(),
    }, indent=2))
