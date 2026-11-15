"""Exact binary matrix-code controls for the rank-autocorrelation executable."""

from __future__ import annotations

import argparse
import collections
import itertools
import json
import random
import statistics
import subprocess
import time
from pathlib import Path


def rk(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def gl(rng, n):
    """Sample a dense invertible transformation using independent shears."""
    rows = [1 << i for i in range(n)]
    if n > 1:
        for _ in range(12 * n):
            i, j = rng.sample(range(n), 2)
            rows[i] ^= rows[j]
    return tuple(rows)


def linear_combination(rows, x):
    value = 0
    while x:
        bit = x & -x
        value ^= rows[bit.bit_length() - 1]
        x ^= bit
    return value


def mul(a, b):
    return tuple(linear_combination(b, row) for row in a)


def flatten(rows, n):
    return sum(row << (n * i) for i, row in enumerate(rows))


def unflatten(x, m, n):
    mask = (1 << n) - 1
    return tuple((x >> (n * i)) & mask for i in range(m))


def apply(a, l, r):
    return mul(mul(l, a), r)


def make_case(rng, m, n, k, positive=True):
    def random_basis():
        flat = []
        while len(flat) < k:
            v = rng.getrandbits(m * n)
            if rk(flat + [v]) > len(flat):
                flat.append(v)
        return tuple(unflatten(v, m, n) for v in flat)

    a = random_basis()
    if not positive:
        return a, random_basis()
    l, r, s = gl(rng, m), gl(rng, n), gl(rng, k)
    images = [flatten(apply(matrix, l, r), n) for matrix in a]
    return a, tuple(unflatten(linear_combination(images, row), m, n) for row in s)


def encode_pair(a, b, n):
    m, k = len(a[0]), len(a)
    rows = [f"2 {m} {n} {k}"]
    for matrix in a + b:
        rows += [" ".join(str(row >> j & 1) for j in range(n)) for row in matrix]
    return "\n".join(rows) + "\n"


def check(a, b, n, response):
    for field in ("L", "R", "S"):
        mat = response[field]
        assert len(mat) > 0 and len(mat) == len(mat[0]), field
        p = tuple(sum(x << j for j, x in enumerate(row)) for row in mat)
        assert rk(p) == len(p), field
    l = tuple(sum(x << j for j, x in enumerate(row)) for row in response["L"])
    r = tuple(sum(x << j for j, x in enumerate(row)) for row in response["R"])
    for i, ai in enumerate(a):
        coord = sum(row[i] << j for j, row in enumerate(response["S"]))
        expected = linear_combination([flatten(bi, n) for bi in b], coord)
        assert flatten(apply(ai, l, r), n) == expected


class Solver:
    def __init__(self, exe, rank_only, budget):
        command = [str(exe.resolve()), "--budget-ms", str(budget)]
        if rank_only:
            command.append("--rank-only")
        self.process = subprocess.Popen(
            command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True
        )

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.process.stdin.close()
        self.process.wait(timeout=10)
        self.process.stdout.close()

    def solve(self, a, b, n):
        before = time.perf_counter()
        self.process.stdin.write(encode_pair(a, b, n))
        self.process.stdin.flush()
        response = json.loads(self.process.stdout.readline())
        if response["result"] == "yes":
            check(a, b, n, response)
        response["checked_wall_ms"] = (time.perf_counter() - before) * 1000
        return response


def tiny_control(solver):
    def key(a, b):
        return min(tuple(sorted((x, y, x ^ y))) for x, y in ((a, b), (b, a)))

    gl2 = [x for x in itertools.product(range(4), repeat=2) if rk(x) == 2]
    representatives = {}
    for a in range(1, 16):
        for b in range(a + 1, 16):
            representatives.setdefault(key(a, b), (a, b))
    stems = list(representatives.values())
    orbit = {}
    for a, b in stems:
        if key(a, b) in orbit:
            continue
        for l in gl2:
            for r in gl2:
                image = tuple(flatten(apply(unflatten(x, 2, 2), l, r), 2) for x in (a, b))
                orbit[key(*image)] = key(a, b)
    n = 0
    for i, (a, b) in enumerate(stems):
        for c, d in stems[i:]:
            first = tuple(unflatten(x, 2, 2) for x in (a, b))
            second = tuple(unflatten(x, 2, 2) for x in (c, d))
            actual = solver.solve(first, second, 2)["result"]
            expected = "yes" if orbit[key(a, b)] == orbit[key(c, d)] else "no"
            assert actual == expected, (a, b, c, d, actual, expected)
            n += 1
    return {"subspaces": len(stems), "orbits": len(set(orbit.values())), "unordered_pairs": n}


def remainder(f, g):
    while f.bit_length() >= g.bit_length():
        f ^= g << (f.bit_length() - g.bit_length())
    return f


def field_product(a, b, f):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
    return remainder(out, f)


def field_power(a, exponent, f):
    product = 1
    while exponent:
        if exponent & 1:
            product = field_product(product, a, f)
        a = field_product(a, a, f)
        exponent >>= 1
    return product


def field_matrix(theta, f, n):
    images = [field_product(theta, 1 << i, f) for i in range(n)]
    return tuple(sum((x >> i & 1) << j for j, x in enumerate(images)) for i in range(n))


def colliding_rank_pencils(solver):
    # A pair of genuinely different regular pencils with identical full-rank
    # profiles. Prove inequivalence independently by the six Mobius transforms.
    n, f = 6, 0b1000011
    proper_monic_divisors = range(2, 1 << (n // 2 + 1))
    assert all(remainder(f, p) for p in proper_monic_divisors)
    companion = field_matrix(2, f, n)
    one = tuple(1 << i for i in range(n))
    transforms = set()
    for change in itertools.product(range(4), repeat=2):
        if rk(change) != 2:
            continue
        a, b = (part & 1 ^ (part >> 1) * 2 for part in change)
        transforms.add(field_product(a, field_power(b, 62, f), f))
    def evaluate(poly, root):
        value = 0
        for index in range(n, -1, -1):
            value = field_product(value, root, f) ^ (poly >> index & 1)
        return value

    other = next(
        g for g in range(1 << n, 1 << (n + 1))
        if all(remainder(g, p) for p in proper_monic_divisors)
        and all(evaluate(g, elt) for elt in transforms)
    )
    a, b = (one, companion), (one, field_matrix(2, other, n))
    for code in (a, b):
        for x in range(1, 4):
            assert rk(unflatten(linear_combination([flatten(z, n) for z in code], x), n, n)) == n
    result = solver.solve(a, b, n)
    assert result["result"] == "no"
    assert result["lifted"] == 6
    return {"polynomials_as_binary_masks": [f, other], "lifted": result["lifted"]}


def summarize(runs):
    return {
        "verdicts": dict(collections.Counter(row["result"] for row in runs)),
        **{
            f"median_{field}": statistics.median(row[field] for row in runs)
            for field in ("total_ms", "checked_wall_ms", "forced_dimension", "branches", "lifted")
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, default=Path(__file__).with_name("mce_backend.exe"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--small-only", action="store_true")
    parser.add_argument("--budget-ms", type=int, default=2000)
    args = parser.parse_args()
    rng = random.Random(1907)
    controls = {}
    with Solver(args.exe, False, args.budget_ms) as solver, Solver(
        args.exe, True, args.budget_ms
    ) as ablation:
        controls["exhaustive"] = tiny_control(solver)
        controls["identical_rank_pencils"] = colliding_rank_pencils(solver)
        print(json.dumps({
            "exhaustive": controls["exhaustive"],
            "identical_rank_pencils": controls["identical_rank_pencils"],
        }), flush=True)
        if not args.small_only:
            controls["cohorts"] = []
            for m, n, k in [
                (12, 12, 6), (24, 24, 8), (48, 48, 10), (64, 64, 12),
                (96, 96, 12), (128, 128, 12), (16, 18, 8), (16, 32, 6), (32, 64, 6),
            ]:
                for positive in (True, False):
                    all_data = {"rank-autocorrelation": [], "rank-only": []}
                    for _ in range(4):
                        a, b = make_case(rng, m, n, k, positive)
                        for name, proc in [("rank-autocorrelation", solver), ("rank-only", ablation)]:
                            result = proc.solve(a, b, n)
                            if result["result"] not in ("unknown", "yes" if positive else "no"):
                                raise AssertionError((m, n, k, positive, name, result))
                            for field in ("L", "R", "S"):
                                result.pop(field, None)
                            all_data[name].append(result)
                    row = {
                        "m": m, "n": n, "k": k, "label": "yes" if positive else "no",
                        "summary": {name: summarize(data) for name, data in all_data.items()},
                        "runs": all_data,
                    }
                    print(json.dumps({key: value for key, value in row.items() if key != "runs"}),
                          flush=True)
                    controls["cohorts"].append(row)
    if args.output is not None:
        args.output.write_text(json.dumps(controls, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
