"""Standalone checks and solver-only benchmarks for solver_transfer.cpp."""

import argparse
import itertools
import json
import random
import statistics
import subprocess
import time
from pathlib import Path


MAPS = ((1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2))


def contract(bits, points):
    """Evaluate the multilinear tensor on a tuple of binary covectors."""
    indices = [0]
    for point in points:
        children = []
        for coordinate in range(2):
            if (point >> coordinate) & 1:
                children.extend(2 * index + coordinate for index in indices)
        indices = children
    return sum((bits >> index) & 1 for index in indices) % 2


def transform_by_evaluation(order, bits, choices):
    """Evaluate all target coordinates by definition for an independent check."""
    points = [MAPS[choice] for choice in choices]
    result = 0
    for index, covectors in enumerate(itertools.product(*points)):
        result |= contract(bits, covectors) << index
    return result


def transform(order, bits, choices):
    for axis, choice in enumerate(choices):
        stride = 1 << (order - axis - 1)
        block_mask = (1 << stride) - 1
        axis_mask = ((1 << (1 << order)) - 1) // (1 + (1 << stride))
        assert axis_mask & block_mask == block_mask
        low, high = bits & axis_mask, (bits >> stride) & axis_mask
        choices_at_axis = (0, low, high, low ^ high)
        a, b = MAPS[choice]
        bits = choices_at_axis[a] | (choices_at_axis[b] << stride)
    return bits


def covector_signature(order, value):
    counts = [[0] * 3 for _ in range(order)]
    for points in itertools.product((1, 2, 3), repeat=order):
        if contract(value, points):
            for row, point in zip(counts, points):
                row[point - 1] += 1
    return tuple(tuple(sorted(row)) for row in counts)


def matrix_rank(rows):
    basis = {}
    for row in rows:
        while row:
            bit = row.bit_length()
            if bit not in basis:
                basis[bit] = row
                break
            row ^= basis[bit]
    return len(basis)


def cut_signature(order, value):
    """Ranks of every nontrivial flattening. One orientation per cut."""
    answer = []
    for left_size in range(1, order // 2 + 1):
        for left in itertools.combinations(range(order), left_size):
            if 2 * left_size == order and 0 not in left:
                continue
            right = [axis for axis in range(order) if axis not in left]
            rows = [0] * (1 << len(left))
            for index in range(1 << order):
                if (value >> index) & 1:
                    i = j = 0
                    for axis in left:
                        i = 2 * i + ((index >> (order - axis - 1)) & 1)
                    for axis in right:
                        j = 2 * j + ((index >> (order - axis - 1)) & 1)
                    rows[i] |= 1 << j
            answer.append(matrix_rank(rows))
    return tuple(answer)


def orbit(order, value):
    candidates = {value}
    for axis in range(order):
        next_values = set()
        for current in candidates:
            for choice in range(6):
                maps = [0] * order
                maps[axis] = choice
                next_values.add(transform(order, current, maps))
        candidates = next_values
    return candidates


def hard_negative(rng):
    seen = {}
    for _ in range(15000):
        sample = rng.getrandbits(32)
        key = covector_signature(5, sample), cut_signature(5, sample)
        if key in seen:
            old = seen[key]
            if sample not in orbit(5, old):
                return old, sample
        else:
            seen[key] = sample
    raise RuntimeError("The fixed control seed failed to find an exact collision")


def outer(low, left, right_order, right):
    result = 0
    for i in range(1 << low):
        if (left >> i) & 1:
            result |= right << ((1 << right_order) * i)
    return result


def serialize(order, left, right):
    values = " ".join(str((word >> i) & 1) for word in (left, right) for i in range(1 << order))
    return f"{order} 2\n" + ("2 " * order).strip() + f"\n{values}\n"


def run(executable, order, left, right, method, repeat):
    data = serialize(order, left, right)
    start = time.perf_counter_ns()
    completed = subprocess.run(
        [str(executable), f"--{method}", "--repeat", str(repeat)],
        input=data,
        text=True,
        capture_output=True,
        check=True,
        timeout=30,
    )
    elapsed_ns = time.perf_counter_ns() - start
    result = json.loads(completed.stdout)
    result["process_total_ns"] = elapsed_ns
    if result["status"] == "yes":
        assert transform(order, left, result["witness"]) == right, result
        if order <= 4:
            assert transform_by_evaluation(order, left, result["witness"]) == right, result
    return result


def combine(executable, order, left, right, expected, repeat):
    results = {key: run(executable, order, left, right, key, repeat) for key in ("signature", "mitm")}
    assert results["signature"]["status"] == results["mitm"]["status"] == expected, results
    return results


def statistics_summary(records):
    rows = []
    for order, kind in sorted({(row["order"], row["kind"]) for row in records}):
        group = [row["results"] for row in records if (row["order"], row["kind"]) == (order, kind)]
        medians = {}
        for method in ("signature", "mitm"):
            medians[method] = statistics.median(
                statistics.median(result[method]["solve_ns"]) for result in group
            )
        rows.append({
            "order": order,
            "kind": kind,
            "cases": len(group),
            "median_signature_ns": medians["signature"],
            "median_mitm_ns": medians["mitm"],
            "mitm_over_signature": medians["mitm"] / max(medians["signature"], 1),
        })
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=Path(__file__).with_name("solver_transfer.exe"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--positive-cases", type=int, default=5)
    args = parser.parse_args()
    rng = random.Random(45657354)
    neg_a, neg_b = hard_negative(rng)
    records = []
    for order in (4, 6, 8, 10, 12):
        for _ in range(args.positive_cases):
            left = rng.getrandbits(1 << order)
            choices = [rng.randrange(6) for _ in range(order)]
            right = transform(order, left, choices)
            records.append({
                "order": order,
                "kind": "uniform-yes",
                "results": combine(args.solver, order, left, right, "yes", args.repeat),
            })
        if order >= 5:
            factor = rng.getrandbits(1 << (order - 5)) or 1
            left, right = [outer(5, value, order - 5, factor) for value in (neg_a, neg_b)]
            records.append({
                "order": order,
                "kind": "matched-counts-and-cuts-no",
                "results": combine(args.solver, order, left, right, "no", args.repeat),
            })
    summary = {
        "synthetic_cases": len(records),
        "exhaustive_base_counterexample": [hex(neg_a), hex(neg_b)],
        "counterexample_source_orbit_size": len(orbit(5, neg_a)),
        "summary": statistics_summary(records),
        "records": records,
    }
    if args.output is not None:
        args.output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary["summary"], indent=2))


if __name__ == "__main__":
    main()
