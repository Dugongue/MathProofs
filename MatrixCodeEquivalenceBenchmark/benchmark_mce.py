"""Benchmark and independently verify the prime-field MCE implementation."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from pathlib import Path
from random import Random
from statistics import median
from time import perf_counter
import json

import numpy as np

import mce


def check_witness(a, b, p, witness):
    l, r, s = (np.asarray(witness[key], dtype=np.int64) for key in ("L", "R", "S"))
    k, m, n = a.shape
    if (l.shape, r.shape, s.shape) != ((m, m), (n, n), (k, k)):
        raise AssertionError("Wrong witness dimensions")
    for matrix in (l, r, s):
        if len(mce.echelon(matrix, p, native=False)[1]) != len(matrix):
            raise AssertionError("Singular witness")
    image = (s.T @ b.reshape(k, m * n) % p).reshape(a.shape)
    for i in range(k):
        if not np.array_equal(l @ a[i] % p, image[i] @ r % p):
            raise AssertionError(f"Witness failed on basis word {i}")


def kernel_controls():
    rng = np.random.default_rng(40219)
    controls = 0
    for p in (2, 3, 5, 13, 31):
        for m, n in ((2, 4), (4, 2), (4, 4), (7, 8), (12, 12)):
            for _ in range(20):
                a = rng.integers(p, size=(m, n), dtype=np.int64)
                expected, old = mce.echelon(a, p, native=False)
                got, new = mce.echelon(a, p)
                if old != new or not np.array_equal(got, expected):
                    raise AssertionError("Native RREF mismatch")
                controls += 1
        points = mce.projective(p, 3, 100_000)
        a = rng.integers(p, size=(3, 5, 7), dtype=np.int64)
        if not np.array_equal(mce.rank_word_table(a, points, p),
                              mce.rank_word_table(a, points, p, native=False)):
            raise AssertionError("Native codeword-rank mismatch")
        controls += len(points)

    for p, m, n, k in ((2, 2, 4, 3), (3, 4, 2, 3), (5, 5, 5, 3), (13, 16, 24, 5)):
        for _ in range(5):
            a = rng.integers(p, size=(k, m, n), dtype=np.int64)
            l = np.eye(m, dtype=np.int64)
            if m > 1:
                l[0, 1] = 1
            r = np.eye(n, dtype=np.int64)
            if n > 1:
                r[1, 0] = 1
            b = l @ a @ mce.inverse(r, p) % p
            w, _, method = mce.fixed_map(a, b, np.eye(k, dtype=np.int64), p, rng, 8192)
            if w is None:
                raise AssertionError(f"Planted fixed map failed ({method})")
            ll, rr = w
            check_witness(a, b, p, {"L": ll, "R": rr, "S": np.eye(k, dtype=np.int64)})
            controls += 1
    return controls


def protocol(path, mode, rounds):
    start = perf_counter()
    p, a, b = mce.read_pair(path)
    read = perf_counter()
    outcome = mce.solve(p, a, b, rounds=rounds)
    if outcome["status"] == "yes":
        check_witness(a, b, p, outcome["witness"])
    end = perf_counter()
    outcome.pop("witness", None)
    return {"case": path.name, "mode": mode, **outcome,
            "read_ms": (read - start) * 1000, "end_to_end_ms": (end - start) * 1000}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--controls", action="store_true")
    parser.add_argument("--compare-python", action="store_true")
    parser.add_argument("--out", type=Path, default=Path("mce-results.json"))
    args = parser.parse_args()
    native = mce.NATIVE_RANK_WORDS, mce.NATIVE_RREF
    if args.controls and not all(native):
        raise RuntimeError("Build the native library to run the independent kernel tests")
    results = {"exact_kernel_and_lift_controls": kernel_controls() if args.controls else None}
    samples = []
    rng = Random(27014)
    jobs = [(f, "native" if all(native) else "python", i) for f in args.files
            for i in range(args.repeats)]
    if args.compare_python:
        if not all(native):
            raise RuntimeError("Comparison requires the native extension")
        jobs.extend((f, "python", i) for f in args.files if f.name in (
            "oxford-meds-13-4-6-5.txt", "oxford-rebased.txt"
        ) for i in range(args.repeats))
    rng.shuffle(jobs)
    for path, mode, repeat in jobs:
        mce.NATIVE_RANK_WORDS, mce.NATIVE_RREF = native if mode == "native" else (None, None)
        result = protocol(path, mode, 3)
        result["repeat"] = repeat
        samples.append(result)
    results["samples"] = samples
    clusters = defaultdict(list)
    for line in samples:
        clusters[line["case"], line["mode"]].append(line)
    by_case = []
    for (name, mode), group in sorted(clusters.items()):
        by_case.append({
            "case": name, "mode": mode, "format": group[0]["format"],
            "status": dict(Counter(item["status"] for item in group)),
            "median_end_to_end_ms": median(item["end_to_end_ms"] for item in group),
        })
    results["summary"] = by_case
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for item in by_case:
        print(item["case"], item["status"], item["mode"], f"{item['median_end_to_end_ms']:.2f} ms")


if __name__ == "__main__":
    main()
