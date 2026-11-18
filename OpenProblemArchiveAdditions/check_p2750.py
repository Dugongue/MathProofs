"""Enumerate the complete TheoremDB P2750 orbit atlas without input data."""

import argparse
import csv
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

P = 5
BASE = P**3
TOTAL = BASE**3


def multiply(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P,
            (c * e + d * g) % P, (c * f + d * h) % P)


def trace(matrix):
    return (matrix[0] + matrix[3]) % P


def inverse(matrix, determinant):
    a, b, c, d = matrix
    inv_det = pow(determinant, -1, P)
    return tuple(x * inv_det % P for x in (d, -b, -c, a))


def encode(i, j, k):
    return (i * BASE + j) * BASE + k


def decode(code):
    return code // BASE**2, code // BASE % BASE, code % BASE


def actions(matrices, index):
    rows = set()
    for g in product(range(P), repeat=4):
        a, b, c, d = g
        determinant = (a * d - b * c) % P
        if determinant:
            inv = inverse(g, determinant)
            rows.add(tuple(index[multiply(multiply(g, x), inv)] for x in matrices))
    assert len(rows) == 120
    assert all(len(set(row)) == BASE for row in rows)
    return sorted(rows)


def orbit(action, i, j, k):
    return {encode(row[i], row[j], row[k]) for row in action}


def enumerate_atlas(output):
    matrices = [(a, b, c, -a % P) for a, b, c in product(range(P), repeat=3)]
    index = {entry: i for i, entry in enumerate(matrices)}
    action = actions(matrices, index)
    products = [[multiply(x, y) for y in matrices] for x in matrices]
    pair = [[trace(xy) for xy in row] for row in products]

    def profile(i, j, k):
        return (pair[i][i], pair[j][j], pair[k][k], pair[i][j], pair[i][k],
                pair[j][k], trace(multiply(products[i][j], matrices[k])))

    marked = bytearray(TOTAL)
    buckets = defaultdict(list)
    sizes = Counter()
    rows = []
    for code in range(TOTAL):
        if marked[code]:
            continue
        i, j, k = decode(code)
        members = orbit(action, i, j, k)
        assert min(members) == code
        key = profile(i, j, k)
        for member in members:
            assert not marked[member] and profile(*decode(member)) == key
            marked[member] = 1
        buckets[key].append(code)
        sizes[len(members)] += 1
        if output:
            rows.append((code, len(members), *key, *matrices[i], *matrices[j], *matrices[k]))

    assert marked.count(1) == TOTAL and sum(sizes.values()) == 16400
    assert sizes == Counter({1: 1, 20: 62, 24: 31, 30: 62, 120: 16244})
    assert len(buckets) == 15625
    histogram = Counter(map(len, buckets.values()))
    assert histogram == Counter({1: 15562, 13: 62, 32: 1})
    zero = (0,) * 7

    points = [(0, 0, 0), (0, 0, 1)]
    points.extend((0, 1, c) for c in range(P))
    points.extend((1, b, c) for b, c in product(range(P), repeat=2))
    canonical = {min(orbit(action, *(index[(0, t, 0, 0)] for t in point)))
                 for point in points}
    assert len(canonical) == 32 and canonical == set(buckets[zero])
    print(f"{TOTAL:,} triples, {sum(sizes.values()):,} orbits, {len(buckets):,} fibers")
    print("Fiber sizes:", dict(sorted(histogram.items())))
    print("Unique maximizing profile:", zero, "with 32 representative orbits")

    if output:
        with output.open("x", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
            writer.writerow(("code", "size", "AA", "BB", "CC", "AB", "AC", "BC", "ABC",
                             *(f"{name}{r}{c}" for name in "ABC"
                               for r, c in product(range(2), repeat=2))))
            writer.writerows(rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, help="write a new TSV orbit atlas")
    args = parser.parse_args()
    enumerate_atlas(args.certificate)
