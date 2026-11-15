"""Create certified larger, correlated controls from the published Oxford pair."""
import argparse
import json
from pathlib import Path
from random import Random

from dataset_meds import (
    OXFORD_SOURCE, OXFORD_PARAMETERS, OXFORD_C, OXFORD_D,
    OXFORD_LEFT, OXFORD_RIGHT, product, rref, transform, verify_pair, write_pair,
)


def random_invertible(size, p, rng):
    while True:
        matrix = [[rng.randrange(p) for _ in range(size)] for _ in range(size)]
        if len(rref(matrix, p)) == size:
            return matrix


def inverse(matrix, p):
    size = len(matrix)
    augmented = [list(row) + [int(i == j) for j in range(size)] for i, row in enumerate(matrix)]
    reduced = rref(augmented, p)
    if len(reduced) != size or any(reduced[i][j] != int(i == j) for i in range(size) for j in range(size)):
        raise ValueError("a proposed mask is singular")
    return [row[size:] for row in reduced]


def with_identity(matrix, copies):
    return [[matrix[i][j] if a == b else 0
             for j in range(len(matrix[0])) for b in range(copies)]
            for i in range(len(matrix)) for a in range(copies)]


def replicate(code, n, copies):
    for flattened in code:
        matrix = [flattened[i:i + n] for i in range(0, len(flattened), n)]
        yield tuple(x for row in with_identity(matrix, copies) for x in row)


def create(out, replicas):
    prime, m, n, k = OXFORD_PARAMETERS
    out.mkdir(parents=True, exist_ok=True)
    cases = []
    for repeat in replicas:
        rng = Random(91442 + repeat)
        params = (prime, m * repeat, n * repeat, k)
        _, rows, cols, _ = params
        source = tuple(replicate(OXFORD_C, n, repeat))
        target = tuple(replicate(OXFORD_D, n, repeat))
        left = with_identity(OXFORD_LEFT, repeat)
        right = with_identity(OXFORD_RIGHT, repeat)
        if repeat > 1:
            source_left = random_invertible(rows, prime, rng)
            source_right = random_invertible(cols, prime, rng)
            target_left = random_invertible(rows, prime, rng)
            target_right = random_invertible(cols, prime, rng)
            source = tuple(transform(source, source_left, source_right, prime, cols))
            target = tuple(transform(target, target_left, target_right, prime, cols))
            left = product(product(target_left, left, prime), inverse(source_left, prime), prime)
            right = product(product(inverse(source_right, prime), right, prime), target_right, prime)
        source = product(random_invertible(k, prime, rng), source, prime)
        target = product(random_invertible(k, prime, rng), target, prime)
        if not verify_pair(params, source, target, left, right):
            raise ValueError("amplification or rebase witness failed")
        path = out / (f"oxford-derived-r{repeat}.txt" if repeat > 1 else "oxford-rebased.txt")
        digest = write_pair(path, params, source, target)
        cases.append({
            "source": OXFORD_SOURCE, "parameters": params,
            "classification": "derived-amplification" if repeat > 1 else "derived-rebase",
            "replicas": repeat, "label": "equivalent", "verified_constructed_witness": True,
            "file": path.name, "sha256": digest,
        })
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--copies", nargs="+", type=int, default=[1, 2, 3, 4])
    opts = parser.parse_args()
    if min(opts.copies) < 1 or len(set(opts.copies)) != len(opts.copies):
        parser.error("copy counts must be distinct positive integers")
    print(json.dumps(create(opts.output, opts.copies), indent=2))


if __name__ == "__main__":
    main()
