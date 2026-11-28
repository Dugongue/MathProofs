"""Verify the order-4792 inequivalence certificate from two local JSON files."""

import argparse
from array import array
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path


ORDER = 4792
GROUP = (7, 19, 3, 3)
SHA_268 = "5953fc1f8ad4cfcd38c782b9e7be909af4b0d7dc5bd94073a98dc4765e57eab6"
SHA_523 = "f2dac720bb9f6e4ef13a22bb20e35b2baa5f0a5546c714aafaf4c619e2a717da"
LABELS = ((1, 2, 3, 4), (-2, 1, 4, -3), (-3, -4, 1, 2), (-4, 3, -2, 1))
COLLISIONS = [
    ((0, 1), (2, 3)),
    ((0, 2), (1, 3)),
    ((0, 3), (1, 2)),
]
BIT_TO_TEXT = bytes.maketrans(bytes((0, 1)), b"01")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_sequences(path, expected_digest, size):
    certificate = json.loads(path.read_text(encoding="utf-8"))
    require(certificate["order"] == ORDER and tuple(certificate["group"]) == GROUP
            and certificate["construction"] == "spence", "Wrong certificate format")
    strings = certificate["sequences"]
    require(len(strings) == 4 and all(len(s) == size and set(s) <= {"+", "-"} for s in strings),
            "Wrong sign data")
    require(certificate["sha256"] == expected_digest, "Wrong certificate digest field")
    return [bytes(c == "-" for c in s) for s in strings]


def translate_index(point, shift, index, point_sign, shift_sign):
    argument = tuple((point_sign * a + shift_sign * b) % m
                     for a, b, m in zip(point, shift, GROUP))
    return index[argument]


def build_rows(signs, points, index):
    size = len(points)
    sums = [size - 2 * sum(sequence) for sequence in signs]
    require(all(abs(s) == 1 for s in sums), "Invalid border signs")
    border = [
        bytes((sums[abs(label) - 1] < 0) ^ (label < 0) for label in row)
        for row in LABELS
    ]
    rows = [
        bytes(1 ^ bit for bit in row) + b"".join(bytes((bit,)) * size for bit in row)
        for row in border
    ]
    shifts = [
        [
            array("H", (translate_index(point, shift, index, u, v) for point in points))
            for u, v in ((1, -1), (-1, -1), (1, 1))
        ]
        for shift in points
    ]
    for i, labels in enumerate(LABELS):
        for shift_tables in shifts:
            parts = [border[i]]
            for j, label in enumerate(labels):
                table = 0 if i == j else (1 if i == 0 or j == 0 else 2)
                sequence = signs[abs(label) - 1]
                negative = int(label < 0)
                parts.append(bytes(sequence[k] ^ negative for k in shift_tables[table]))
            rows.append(b"".join(parts))
    return rows


def validate_hash(rows, expected):
    digest = sha256()
    symbols = (b"1", b"-1")
    for row in rows:
        digest.update(b",".join(symbols[bit] for bit in row))
        digest.update(b"\n")
    require(digest.hexdigest() == expected, "Reconstructed matrix digest mismatch")


def require_hadamard(signs, points, index):
    """Check the four autocorrelations using exact integer differences."""
    counts = [[0] * len(points) for _ in signs]
    for sequence, tally in zip(signs, counts):
        negative = [point for point, bit in zip(points, sequence) if bit]
        for u in negative:
            for v in negative:
                tally[translate_index(v, u, index, 1, -1)] += 1
    maximum = None
    for shift in range(1, len(points)):
        values = [len(points) - 4 * sum_sequence + 4 * tally[shift]
                  for sum_sequence, tally in zip(map(sum, signs), counts)]
        require(sum(values) == -4, f"Autocorrelation identity failed at shift {shift}")
        maximum = max(values) if maximum is None else max(maximum, *values)
    return maximum


def normalize_and_pack(rows, coordinates):
    projections = []
    full = []
    for row in rows:
        head = row[0]
        bits = bytes(bit ^ head for bit in row)
        full.append(int(bits.translate(BIT_TO_TEXT), 2))
        projected = 0
        for j in coordinates:
            projected = (projected << 1) | bits[j]
        projections.append(projected)
    return projections, full


def pair_collisions(rows):
    """Find equal sign-normalized full pair products, with an exact filter."""
    coordinates = [(7 + 1879 * i) % ORDER for i in range(64)]
    projected, full = normalize_and_pack(rows, coordinates)
    buckets = [array("Q") for _ in range(256)]
    for i, a in enumerate(projected):
        for j in range(i):
            key = a ^ projected[j]
            buckets[key >> 56].append(key)
    repeated = set()
    for bucket in buckets:
        ordered = sorted(bucket)
        repeated.update(a for a, b in zip(ordered, ordered[1:]) if a == b)
    del buckets
    exact = {}
    for i, a in enumerate(projected):
        for j in range(i):
            if a ^ projected[j] in repeated:
                key = full[i] ^ full[j]
                exact.setdefault(key, []).append((j, i))
    collisions = sorted(tuple(sorted(pairs)) for pairs in exact.values() if len(pairs) > 1)
    return len(repeated), collisions


def check_certificate(path, digest, expected_repeats, expected_maximum):
    points = tuple(product(*(range(m) for m in GROUP)))
    index = {point: i for i, point in enumerate(points)}
    signs = read_sequences(path, digest, len(points))
    maximum = require_hadamard(signs, points, index)
    require(maximum == expected_maximum, "Unexpected bulk autocorrelation maximum")
    rows = build_rows(signs, points, index)
    validate_hash(rows, digest)
    row_repeats, row_collisions = pair_collisions(rows)
    col_repeats, col_collisions = pair_collisions(zip(*rows))
    require((row_repeats, col_repeats) == expected_repeats, "Unexpected projected repeats")
    require(row_collisions == col_collisions == COLLISIONS, "Unexpected full collisions")
    print(f"{digest[:12]}  projected repeats ({row_repeats}, {col_repeats})  "
          f"unique border on each axis  bulk maximum {maximum}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case268", type=Path)
    parser.add_argument("case523", type=Path)
    args = parser.parse_args()
    check_certificate(args.case268, SHA_268, (45, 21), 157)
    check_certificate(args.case523, SHA_523, (9, 6), 125)
    print("The two order-4792 Hadamard matrices are inequivalent, also allowing transposition.")


if __name__ == "__main__":
    main()
