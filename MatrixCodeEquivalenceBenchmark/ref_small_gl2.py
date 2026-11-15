"""Exact two-row reference: enumerate projective GL_2 and right-kernel points."""
import argparse
import json
from pathlib import Path
from time import perf_counter

from dataset_meds import product, rref, transform
from dataset_morrison import find_witness
from ref_io import read_pair, verify


def solve(path):
    start = perf_counter()
    p, m, n, k, a, b = read_pair(path)
    if m != 2 or p not in (2, 3):
        raise ValueError("This reference targets the two-row binary and ternary Morrison cases")
    after_read = perf_counter()
    parameters = p, m, n, k
    source, target = (tuple(tuple(x for row in mat for x in row) for mat in code)
                      for code in (a, b))
    witness, tested, max_nullity = find_witness(parameters, source, target)
    after_search = perf_counter()
    result = {
        "case": path.name, "format": list(parameters), "backend": "Projective GL2 and right-kernel enumeration",
        "result": "yes" if witness else "no", "read_ms": 1000 * (after_read - start),
        "search_ms": 1000 * (after_search - after_read),
        "left_maps": tested, "max_right_nullity": max_nullity,
    }
    if witness:
        left, right = witness
        reduced = rref(tuple(row + tuple(int(i == j) for j in range(k))
                             for i, row in enumerate(target)), p)
        pivots = [next(i for i, entry in enumerate(row) if entry) for row in reduced]
        if len(pivots) != k or max(pivots) >= m * n:
            raise AssertionError("The target generators are not a basis")
        images = tuple(tuple(row[i] for i in pivots)
                       for row in transform(source, left, right, p, n))
        mixing = product(images, tuple(row[m * n:] for row in reduced), p)
        left, right, mixing = ([list(row) for row in matrix] for matrix in (left, right, mixing))
        if not verify(p, m, n, k, a, b, left, right, mixing):
            raise AssertionError("Enumerated witness failed verification")
        result.update(left=left, right=right, mixing=mixing)
    end = perf_counter()
    result.update(verify_ms=1000 * (end - after_search), total_ms=1000 * (end - start))
    return result


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("cases", nargs="+", type=Path)
    cli.add_argument("--repeats", type=int, default=3)
    args = cli.parse_args()
    if args.repeats <= 0:
        cli.error("Repeats must be positive")
    for _ in range(args.repeats):
        for path in args.cases:
            print(json.dumps(solve(path)), flush=True)
