"""Compare matching end-to-end compiler and binary solver variants."""

from collections import defaultdict
from contextlib import ExitStack
from pathlib import Path
import argparse
import hashlib
import json
import platform
import random
import statistics
import subprocess

from pipeline import NativeSolver, read_case, solve_pair
from solver_transfer_controls import MAPS, covector_signature, cut_signature, orbit, outer, serialize


class TransferSolver:
    def __init__(self, executable, method):
        self.process = subprocess.Popen(
            [str(executable.resolve()), f"--{method}"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.wait(timeout=5)

    def solve(self, request):
        self.process.stdin.write(request)
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("Native signature backend exited without a verdict")
        answer = json.loads(line)
        answer["result"] = answer.pop("status")
        answer["witness"] = [MAPS[choice][0] | (MAPS[choice][1] << 2) for choice in answer["witness"]]
        return answer


def make_adversarial_fixtures(path):
    left, right = 0x5D96E218, 0x95895EFC
    assert covector_signature(5, left) == covector_signature(5, right)
    assert cut_signature(5, left) == cut_signature(5, right)
    assert right not in orbit(5, left)
    rng = random.Random(543216789)
    fixtures = []
    path.mkdir(exist_ok=True)
    for order in (5, 6, 8, 10, 12):
        extra = order - 5
        factor = rng.getrandbits(1 << extra) or 1
        a, b = (outer(5, value, extra, factor) for value in (left, right))
        name = f"matched-counts-cuts-d{order}-no"
        (path / f"{name}.ti").write_text(serialize(order, a, b), encoding="ascii")
        fixtures.append((path / f"{name}.ti", "no", "matched-counts-cuts-no"))
    return fixtures


def summarize(records):
    groups = defaultdict(list)
    for item in records:
        groups[(item["order"], item["category"], item["expected"], item["method"])].append(item["samples"])
    rows = []
    for (order, category, expected, method), samples in sorted(groups.items()):
        rows.append({
            "order": order,
            "category": category,
            "verdict": expected,
            "method": method,
            "cases": len(samples),
            "median_total_ms": statistics.median(
                statistics.median(sample["total_ms"] for sample in runs) for runs in samples
            ),
            "median_solve_ms": statistics.median(
                statistics.median(
                    sample["solve_ns"][0] / 1e6
                    if "solve_ns" in sample else sample["rank_ms"] + sample["search_ms"]
                    for sample in runs
                )
                for runs in samples
            ),
        })
    return rows


def main():
    directory = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, default=directory / "solver_transfer.exe")
    parser.add_argument("--pair-solver", type=Path, default=directory / "native_ti.exe")
    parser.add_argument("--corpus", type=Path, default=directory / "corpus")
    parser.add_argument("--fixtures", type=Path, default=directory / "solver-transfer-fixtures")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repeats", type=int, default=5)
    args = parser.parse_args()
    manifest = json.loads((args.corpus / "manifest.json").read_text(encoding="utf-8-sig"))
    cases = [
        (args.corpus / (entry["name"] + ".ti"), entry["expected"], "shared-corpus")
        for entry in manifest if all(side == 2 for side in entry["shape"])
    ]
    cases += make_adversarial_fixtures(args.fixtures)
    repeats = args.repeats
    randomizer = random.Random(724653)
    records = []
    plans = {
        "direct-mitm": ("direct", "mitm"),
        "direct-signature": ("direct", "signature"),
        "direct-pair-rank": ("direct", "pair"),
        "balanced-linked-signature": ("balanced-runs", "signature"),
        "balanced-linked-pair-rank": ("balanced-runs", "pair"),
        "half-linked-signature": ("half-runs", "signature"),
        "published-linked-signature": ("published-runs", "signature"),
    }
    with ExitStack() as stack:
        solvers = {
            method: stack.enter_context(TransferSolver(args.solver, method))
            for method in ("signature", "mitm")
        }
        solvers["pair"] = stack.enter_context(NativeSolver(args.pair_solver, budget_ms=10000))
        for path, expected, category in cases:
            source, target = read_case(path)
            samples = {name: [] for name in plans}
            for _ in range(repeats):
                keys = list(plans)
                randomizer.shuffle(keys)
                for key in keys:
                    compiler, method = plans[key]
                    result = solve_pair(solvers[method], source, target, compiler)
                    assert result["result"] == expected, (path.name, key, result)
                    samples[key].append(result)
            for method, runs in samples.items():
                records.append({
                    "name": path.stem, "order": source.ndim, "category": category,
                    "expected": expected, "method": method, "samples": runs,
                })
    def sha256(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    report = {
        "cases": len(cases),
        "repeats": repeats,
        "python_version": platform.python_version(),
        "source_sha256": {
            name: sha256(directory / name) for name in (
                "encoder.py", "pipeline.py", "native_ti.cpp", "solver_transfer.cpp",
                "solver_transfer_controls.py", "solver_transfer_pipeline.py",
            )
        },
        "executables_sha256": {
            "covector-and-mitm": sha256(args.solver), "pair-rank": sha256(args.pair_solver),
        },
        "inputs_sha256": {path.name: sha256(path) for path, _, _ in cases},
        "summary": summarize(records),
        "records": records,
    }
    if args.output is not None:
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
