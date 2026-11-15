"""Reproduce and classify published Morrison self-dual matrix-code pairs."""
import argparse
import json
from itertools import combinations, product as choices
from pathlib import Path

from dataset_meds import product, rref, verify_pair, write_pair


SOURCE = "https://arxiv.org/abs/1505.07363"
TABLES = (
    ((2, 2, 2, 2), (
        ("1010 0101", 3),
        ("1001 0110", 1),
    )),
    ((2, 2, 3, 3), (
        ("100100 010010 001001", 7),
        ("001100 110000 000011", 3),
        ("100001 010100 001010", 1),
        ("100100 011000 000011", 5),
        ("100001 010010 001100", 3),
    )),
    ((3, 2, 4, 4), (
        ("10002020 01000202 00102010 00010201", 0),
        ("10112022 01011221 00110002 00001220", 8),
        ("10111022 02211110 00020011 00211122", 0),
        ("10000011 01022121 00020021 00101100", 4),
        ("10011212 02202211 00010012 00200011", 0),
        ("10021000 02100200 00011002 00200210", 0),
        ("10112022 02120121 00012020 00100101", 16),
        ("10111022 01210121 00111000 00000121", 8),
        ("10222011 02210221 00002011 00000221", 32),
        ("10002020 01000202 00202010 00010201", 0),
        ("10212022 01011221 00210002 00001220", 8),
        ("10000011 01022121 00020021 00201100", 4),
        ("10111011 01120121 00001011 00000121", 20),
    )),
)


def rows(flat, n):
    return tuple(flat[i:i+n] for i in range(0, len(flat), n))


def linear_combinations(basis, width, p):
    columns = tuple(zip(*basis))
    for weights in choices(range(p), repeat=len(basis)):
        if not weights:
            yield (0,) * width
            continue
        yield tuple(sum(x * y for x, y in zip(weights, col)) % p for col in columns)


def nullspace(equations, width, p):
    reduced = rref(equations, p)
    pivots = tuple(next(i for i, x in enumerate(row) if x) for row in reduced)
    for free in range(width):
        if free in pivots:
            continue
        vector = [0] * width
        vector[free] = 1
        for row, pivot in zip(reduced, pivots):
            vector[pivot] = -row[free] % p
        yield tuple(vector)


def find_witness(parameters, source, target):
    p, m, n, _ = parameters
    members = tuple(rows(g, n) for g in source)
    normals = tuple(rows(h, n) for h in nullspace(target, m*n, p))
    max_nullity, tested = 0, 0
    for flat in choices(range(p), repeat=m*m):
        if next((x for x in flat if x), 0) != 1:
            continue
        left = rows(flat, m)
        if len(rref(left, p)) != m:
            continue
        tested += 1
        equations = []
        for source_matrix in members:
            moved = product(left, source_matrix, p)
            for normal in normals:
                equations.append(tuple(
                    sum(moved[r][u] * normal[r][c] for r in range(m)) % p
                    for u in range(n) for c in range(n)
                ))
        right_space = tuple(nullspace(equations, n*n, p))
        max_nullity = max(max_nullity, len(right_space))
        for right_flat in linear_combinations(right_space, n*n, p):
            right = rows(right_flat, n)
            if len(rref(right, p)) != n:
                continue
            if not verify_pair(parameters, source, target, left, right):
                raise ValueError("intertwiner equations and exact span check disagree")
            return (left, right), tested, max_nullity
    if tested != p * (p*p - 1):
        raise ValueError("projective GL2 enumeration incomplete")
    return None, tested, max_nullity


def build(destination):
    destination.mkdir(parents=True, exist_ok=True)
    manifest = []
    for parameters, table in TABLES:
        p, m, n, k = parameters
        bases = []
        for index, (digits, rank_one_count) in enumerate(table, 1):
            basis = tuple(tuple(map(int, row)) for row in digits.split())
            if len(rref(basis, p)) != k:
                raise ValueError(f"rank failure for ({p}, {m}, {n}) generator {index}")
            if any(sum(x*y for x, y in zip(a, b)) % p for a in basis for b in basis):
                raise ValueError(f"self-duality failure for ({p}, {m}, {n}) generator {index}")
            rank_histogram = tuple(
                len(rref(rows(word, n), p)) for word in linear_combinations(basis, m*n, p)
            )
            if rank_histogram.count(1) != rank_one_count:
                raise ValueError(f"rank distribution differs from table for {parameters} G{index}")
            bases.append((index, basis, rank_one_count))
        for (i, source, source_rank_count), (j, target, target_rank_count) in combinations(bases, 2):
            file = f"morrison-f{p}-{m}x{n}-g{i:02}-g{j:02}.txt"
            witness, checked, max_nullity = find_witness(parameters, source, target)
            manifest.append({
                "file": file,
                "sha256": write_pair(destination / file, parameters, source, target),
                "source": SOURCE,
                "source_table": 1 if p == 2 else 2,
                "generators": [i, j],
                "parameters": parameters,
                "label": "equivalent" if witness else "inequivalent",
                "published_rank_one_counts": [source_rank_count, target_rank_count],
                "left_projective_matrices_checked": checked,
                "maximum_right_space_nullity": max_nullity,
                "witness": witness,
            })
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n",
                                                encoding="ascii")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    manifest = build(parser.parse_args().output)
    yes = sum(row["label"] == "equivalent" for row in manifest)
    print(f"{len(manifest)} classified pairs, {yes} yes and {len(manifest) - yes} no")


if __name__ == "__main__":
    main()
