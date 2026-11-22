"""Direct arithmetic control for the degree-64 dihedral genus and its probe panel."""

from itertools import permutations
from math import isqrt, prod


def is_prime(p):
    return p > 1 and all(p % j for j in range(2, isqrt(p) + 1))


def neg_symbol(a, p):
    return int(pow(a % p, (p - 1) // 2, p) == p - 1)


def parity(a):
    return a.bit_count() % 2


def central_probes():
    found = {0: [], 1: []}
    q = 5
    while min(map(len, found.values())) < 8:
        if q != 97 and is_prime(q) and not neg_symbol(97, q):
            state = int(pow(97, (q - 1) // 4, q) != 1)
            if len(found[state]) < 8:
                found[state].append(q)
        q += 4
    return [found[(g >> 2) & 1][(g & 3) | ((g >> 1) & 4)] for g in range(16)]


def interpolate(probes):
    pivots = {}
    chosen = []
    p = -1
    while len(chosen) < 16:
        p += 8 * 97
        if not is_prime(p):
            continue
        value = sum(neg_symbol(-p, q) << i for i, q in enumerate(probes))
        combination = 1 << len(chosen)
        while value and (pivot := value.bit_length() - 1) in pivots:
            row, previous = pivots[pivot]
            value ^= row
            combination ^= previous
        if value:
            pivots[value.bit_length() - 1] = (value, combination)
            chosen.append(p)

    radicands = []
    for bit in (0, 1, 3):
        value = sum(((g >> bit) & 1) << g for g in range(16))
        combination = 0
        while value:
            row, previous = pivots[value.bit_length() - 1]
            value ^= row
            combination ^= previous
        radicands.append(prod(-p for i, p in enumerate(chosen) if combination & (1 << i)))
    assert all(d % 8 == 1 and d % 97 == 1 for d in radicands)
    for g, q in enumerate(probes):
        assert not neg_symbol(97, q)
        assert int(pow(97, (q - 1) // 4, q) != 1) == ((g >> 2) & 1)
        assert [neg_symbol(d, q) for d in radicands] == [(g >> i) & 1 for i in (0, 1, 3)]
    return chosen


def check_inversion():
    all_singles = set()
    all_pairs = set()
    for f in permutations(range(4)):
        if len({x ^ f[x] for x in range(4)}) < 4:
            continue
        planes = {frozenset((4 | x, 8 | f[x], (4 | x) ^ (8 | f[x]))) for x in range(4)}
        split = [[all(parity(u & g) == 0 for u in w) for g in range(16)] for w in planes]
        table = [[16 * sum(row[g] * row[h] for row in split) for h in range(16)]
                 for g in range(16)]
        all_singles.add(tuple(table[i][i] for i in range(16)))
        all_pairs.add(tuple(x for row in table for x in row))
        for u in range(1, 16):
            for v in range(u + 1, 16):
                coef = sum((-1) ** (parity(u & g) ^ parity(v & h)) * table[g][h]
                           for g in range(16) for h in range(16))
                assert coef == 256 * int(frozenset((u, v, u ^ v)) in planes)
    assert len(all_singles) == 1 and len(all_pairs) == 8


if __name__ == "__main__":
    points = central_probes()
    primes = interpolate(points)
    check_inversion()
    print(f"Verified 16 central Frobenius probes up to {max(points)} using 16 ramification "
          f"labels up to {max(primes)}. All 8 degree-64 classes pass pair Fourier inversion.")
