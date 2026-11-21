"""Finite controls for determinant transport on truncated-polynomial modules."""
from itertools import product
from math import comb
from random import Random


def det(matrix, prime):
    rows = [row[:] for row in matrix]
    result = 1
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i] % prime), None)
        if pivot is None:
            return 0
        if pivot != i:
            rows[pivot], rows[i] = rows[i], rows[pivot]
            result = -result
        entry = rows[i][i]
        result = result * entry % prime
        inverse = pow(entry, -1, prime)
        for row in rows[i + 1:]:
            scale = row[i] * inverse
            row[i:] = [(x - scale * y) % prime for x, y in zip(row[i:], rows[i][i:])]
    return result % prime


def test_map(prime, lengths, substitution, images):
    """Build the actual semilinear matrix from the images of the chain tops."""
    starts = [sum(lengths[:i]) for i in range(len(lengths))]
    size = sum(lengths)
    columns = []
    for source, top in enumerate(images):
        vector = top[:]
        for _ in range(lengths[source]):
            columns.append(vector)
            following = [0] * size
            for begin, length in zip(starts, lengths):
                for j in range(length):
                    following[begin + j] = sum(coef * vector[begin + j - d]
                                               for d, coef in enumerate(substitution, start=1)
                                               if d <= j) % prime
            vector = following
        assert not any(vector)
    expected = pow(substitution[0], sum(comb(k, 2) for k in lengths), prime)
    for k in sorted(set(lengths)):
        group = [i for i, length in enumerate(lengths) if length == k]
        heads = [[images[j][starts[i]] for j in group] for i in group]
        expected = expected * pow(det(heads, prime), k, prime) % prime
    actual = det([list(row) for row in zip(*columns)], prime)
    assert actual == expected
    return actual


def check_dual_numbers():
    count = 0
    for entries in product(range(3), repeat=8):
        images = [list(entries[:4]), list(entries[4:])]
        for a in (1, 2):
            d = test_map(3, (2, 2), (a,), images)
            if d:
                assert d == 1
                count += 1
    assert count == 7776
    return count


def check_mixed():
    rng = Random(57)
    tested = 0
    for p in (3, 5):
        for lengths in ((1, 2, 2, 3), (2, 3, 4), (2, 4, 4), (1, 3, 3)):
            for _ in range(120):
                sub = [rng.randrange(1, p)] + [rng.randrange(p) for _ in range(max(lengths) - 2)]
                images = [[0 if j < length - k else rng.randrange(p)
                           for length in lengths for j in range(length)] for k in lengths]
                test_map(p, lengths, sub, images)
                tested += 1
    return tested


def check_quadrics():
    """For beta and -beta test the quotient determinant from independent frames."""
    tests = 0
    for a, b, c, d in product(range(3), repeat=4):
        p = [[a, b], [c, d]]
        if not det(p, 3):
            continue
        sym = [[a*a, a*b, b*b], [2*a*c, a*d+b*c, 2*b*d], [c*c, c*d, d*d]]
        for sign in (1, 2):
            quotient = [[sign * x % 3 for x in row] for row in sym]
            assert det(p, 3) * det(quotient, 3) % 3 == pow(sign, 3, 3)
            tests += 1
    return tests


if __name__ == "__main__":
    print("Invertible dual-number maps:", check_dual_numbers())
    print("Mixed-length maps:", check_mixed())
    print("Free quadratic sign comparisons:", check_quadrics())
