"""Reproducible end-to-end measurements and independent exact controls."""

import argparse
import itertools
import json
import random
import statistics
import subprocess
import time
from dataclasses import dataclass
from math import prod
from pathlib import Path

import numpy as np

from encoder import compile_published, compile_tensor
from pipeline import NativeSolver, read_case, solve_pair, verify_witness, write_input


def invertible_words(side):
    words = []
    for word in range(1 << (side * side)):
        span = {0}
        for row in range(side):
            bits = (word >> (side * row)) & ((1 << side) - 1)
            span |= {point ^ bits for point in span}
        if len(span) == 1 << side:
            words.append(word)
    return words


GL = {side: invertible_words(side) for side in (1, 2, 3)}


def transform(tensor, words):
    answer = tensor
    for axis, (side, word) in enumerate(zip(tensor.shape, words)):
        matrix = np.array([
            [(word >> (side * row + col)) & 1 for col in range(side)]
            for row in range(side)
        ], dtype=np.uint8)
        answer = np.moveaxis(np.tensordot(matrix, answer, axes=(1, axis)) % 2, 0, axis)
    return answer


def rank(matrix):
    rows = [sum(int(x) << i for i, x in enumerate(row)) for row in matrix]
    pivots = {}
    for row in rows:
        while row:
            bit = row.bit_length()
            if bit in pivots:
                row ^= pivots[bit]
            else:
                pivots[bit] = row
                break
    return len(pivots)


def cut_rank(tensor, side):
    other = tuple(i for i in range(tensor.ndim) if i not in side)
    return rank(tensor.transpose(side + other).reshape(prod(tensor.shape[i] for i in side), -1))


@dataclass
class Case:
    name: str
    source: np.ndarray
    target: np.ndarray
    expected: str
    provenance: str


def generate_cases():
    rng = np.random.default_rng(45201)
    shuffle = random.Random(66887)
    cases = []

    def random_tensor(shape):
        return rng.integers(0, 2, size=shape, dtype=np.uint8)

    def iso(name, a, label):
        for _ in range(24):
            witness = [shuffle.choice(GL[dim]) for dim in a.shape]
            b = transform(a, witness)
            if not np.array_equal(a, b):
                assert verify_witness(a, b, witness)
                cases.append(Case(name, a, b, "yes", label))
                return
        raise RuntimeError("Positive case had a trivial orbit")

    def no_with_matched_marginals(name, a):
        d = a.ndim
        profile = [cut_rank(a, (i,)) for i in range(d)]
        balanced_cuts = list(itertools.combinations(range(d), d // 2))[:32]
        records = [cut_rank(a, cut) for cut in balanced_cuts]
        for _ in range(1600):
            b = random_tensor(a.shape)
            if profile == [cut_rank(b, (i,)) for i in range(d)]:
                for cut, value in zip(balanced_cuts, records):
                    if cut_rank(b, cut) != value:
                        cases.append(Case(name, a, b, "no", "same marginal ranks; different cut rank"))
                        return
        raise RuntimeError("Could not generate a certified negative pair")

    for shape, count in [
        ((2,) * 3, 4), ((2,) * 4, 8), ((2,) * 6, 10), ((2,) * 8, 10),
        ((2,) * 10, 10), ((2,) * 12, 8), ((3,) * 4, 5), ((3,) * 6, 5),
        ((2, 3, 2, 3, 2, 2), 5),
    ]:
        family = f"d{len(shape)}-" + "".join(str(dim) for dim in shape)
        for i in range(count):
            a = random_tensor(shape)
            iso(f"{family}-iso-{i:02}", a, "uniform source; random independent GL factors")
            if i < (count + 1) // 2 and len(shape) >= 4:
                no_with_matched_marginals(f"{family}-no-{i:02}", a)

    shape = (2,) * 6
    multiplication = np.zeros(shape, dtype=np.uint8)
    for i, j, k in itertools.product(range(2), repeat=3):
        multiplication[i, j, j, k, k, i] = 1
    iso("matrix-multiplication-6-iso", multiplication, "2-by-2 matrix multiplication, six leaf modes")
    ghz = np.zeros(shape, dtype=np.uint8)
    ghz[(0,) * 6] = ghz[(1,) * 6] = 1
    iso("diagonal-6-iso", ghz, "rank-two diagonal tensor with many stabilizers")
    bell = np.zeros(shape, dtype=np.uint8)
    for i, j, k in itertools.product(range(2), repeat=3):
        bell[i, i, j, j, k, k] = 1
    assert cut_rank(ghz, (0, 2, 4)) != cut_rank(bell, (0, 2, 4))
    cases.append(Case("diagonal-v-bell-6-no", ghz, bell, "no", "same marginal ranks; different cut rank"))
    empty = np.zeros(shape, dtype=np.uint8)
    cases.append(Case("zero-6-iso", empty, empty.copy(), "yes", "zero control"))
    return cases


def write_corpus(directory, cases):
    directory.mkdir(exist_ok=True, parents=True)
    card = []
    for case in cases:
        path = directory / (case.name + ".ti")
        path.write_bytes(write_input(case.source.shape, case.source, case.target))
        card.append({
            "name": case.name, "expected": case.expected, "shape": case.source.shape,
            "provenance": case.provenance,
        })
    (directory / "manifest.json").write_text(json.dumps(card, indent=2) + "\n", encoding="utf-8")


def validate_entire_cube(executable):
    """Partition all 256 binary 2x2x2 tensors independently and check pair decisions."""
    n = 8
    arrays = [np.array([(word >> i) & 1 for i in range(n)], dtype=np.uint8).reshape(2, 2, 2)
              for word in range(1 << n)]
    known = {}
    for word, array in enumerate(arrays):
        if word in known:
            continue
        for witness in itertools.product(GL[2], repeat=3):
            result = sum(int(entry) << i for i, entry in enumerate(transform(array, witness).ravel()))
            if result in known and known[result] != word:
                raise RuntimeError("Independent orbit partition disagrees with itself")
            known[result] = word
    requests = [(i, j) for i in range(len(arrays)) for j in range(i, len(arrays))]
    unique_format = b"3 2\n2 2 2\n"
    cases = [write_input((2, 2, 2), a, a)[len(unique_format):].splitlines()[0] + b"\n" for a in arrays]
    request = b"".join(unique_format + cases[i] + cases[j] for i, j in requests)
    run = subprocess.run([str(executable.resolve())], input=request, capture_output=True, check=True)
    answers = run.stdout.splitlines()
    if len(answers) != len(requests):
        raise RuntimeError("Incorrect count of exhaustive answers")
    for (i, j), text in zip(requests, answers):
        answer = json.loads(text)
        expect = "yes" if known[i] == known[j] else "no"
        if answer["result"] != expect:
            raise RuntimeError(f"Exhaustive verdict failed on {i},{j}")
        if expect == "yes" and not verify_witness(arrays[i], arrays[j], answer["witness"]):
            raise RuntimeError(f"Exhaustive witness failed on {i},{j}")
    return {"pairs": len(requests), "orbits": len(set(known.values()))}


def run_experiment(executable, cases, repeats, budget_ms, algorithms, corpus):
    table = []
    by_algorithm = {
        "balanced": ("balanced", False),
        "balanced-grouped": ("balanced", False),
        "half-grouped": ("half", False),
        "balanced-runs": ("balanced-runs", False),
        "half-runs": ("half-runs", False),
        "published-runs": ("published-runs", False),
        "direct-rank": ("direct", False),
        "direct-exhaustive": ("direct", True),
    }
    traversal = random.Random(23144)
    warmup = cases[0]
    for algorithm in algorithms:
        name, direct = by_algorithm[algorithm]
        order = cases.copy()
        traversal.shuffle(order)
        launch_start = time.perf_counter_ns()
        grouping = name if algorithm.endswith("-grouped") else None
        with NativeSolver(executable, direct=direct, budget_ms=budget_ms, grouping=grouping) as session:
            solve_pair(session, warmup.source, warmup.target, name)
            ready_ms = (time.perf_counter_ns() - launch_start) / 1e6
            for case in order:
                repetitions = []
                for _ in range(repeats):
                    read_start = time.perf_counter_ns()
                    if corpus is None:
                        source, target = case.source, case.target
                    else:
                        source, target = read_case(corpus / (case.name + ".ti"))
                    read_ms = (time.perf_counter_ns() - read_start) / 1e6
                    record = solve_pair(session, source, target, name)
                    record["file_ms"] = read_ms
                    record["total_ms"] += read_ms
                    if record["result"] != "timeout" and record["result"] != case.expected:
                        raise RuntimeError(f"{algorithm} misclassified {case.name}: {record}")
                    repetitions.append(record)
                    if record["result"] == "timeout":
                        break
                table.append({
                    "algorithm": algorithm, "case": case.name, "expected": case.expected,
                    "shape": case.source.shape, "ready_ms": ready_ms, "samples": repetitions,
                })
    return table


def sizes():
    table = []
    for order in (6, 8, 9, 12, 15, 18):
        tensor = np.zeros((2,) * order, dtype=np.uint8)
        for case in ("published", "balanced", "compact", "half"):
            begin = time.perf_counter_ns()
            if case == "published":
                out = compile_published(tensor)
            else:
                out = compile_tensor(tensor, "half" if case == "half" else "balanced",
                                     tag_policy="geometric" if case == "balanced" else "compact")
            table.append({
                "order": order, "encoder": case, "shape": out.shape, "dense_entries": prod(out.shape),
                "fixed_nonzeros": sum(run.count for run in out.runs),
                "marker_runs": len(out.runs), "construct_marker_ms": (time.perf_counter_ns() - begin) / 1e6,
            })
    return table


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, default=Path(__file__).with_name("native_ti.exe"))
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--corpus-only", action="store_true")
    parser.add_argument("--extra-negatives", type=Path)
    parser.add_argument("--exhaustive", action="store_true")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--budget-ms", type=int, default=250)
    parser.add_argument("--output", type=Path, default=Path("native-results.json"))
    parser.add_argument("--algorithms", nargs="+", default=[
        "balanced", "balanced-runs", "half-runs", "direct-rank", "direct-exhaustive"
    ])
    args = parser.parse_args()
    cases = generate_cases()
    if args.extra_negatives:
        for path in sorted(args.extra_negatives.glob("*.ti")):
            a, b = read_case(path)
            cases.append(Case(path.stem, a, b, "no", "all-cut and projective-count adversary"))
    if args.corpus:
        write_corpus(args.corpus, cases)
    print(f"Prepared {len(cases)} deterministic cases", flush=True)
    if args.corpus_only:
        return
    report = {"encoder_sizes": sizes()}
    if args.exhaustive:
        report["exhaustive_binary_cube"] = validate_entire_cube(args.exe)
        print(report["exhaustive_binary_cube"], flush=True)
    report["samples"] = run_experiment(args.exe, cases, args.repeats, args.budget_ms, args.algorithms, args.corpus)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    for name in args.algorithms:
        selected = [r for r in report["samples"] if r["algorithm"] == name]
        completed = [r for r in selected if all(s["result"] != "timeout" for s in r["samples"])]
        times = [statistics.median(s["total_ms"] for s in r["samples"]) for r in completed]
        print(f"{name:18} {len(completed):3}/{len(selected)} completed, median {statistics.median(times):.4f} ms")


if __name__ == "__main__":
    main()
