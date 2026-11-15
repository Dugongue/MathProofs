"""Matched benchmark for group-contraction profiles with balanced vs half splits."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import random
from statistics import median
import subprocess
import time

from pipeline import read_case, solve_pair


class GroupSolver:
    def __init__(self, executable, branch):
        self._worker = subprocess.Popen([str(executable.resolve()), branch],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def solve(self, request):
        self._worker.stdin.write(request)
        self._worker.stdin.flush()
        reply = self._worker.stdout.readline()
        if not reply:
            raise RuntimeError("group profile backend exited before the verdict")
        return json.loads(reply)

    def close(self):
        self._worker.stdin.close()
        self._worker.stdout.close()
        self._worker.wait(timeout=3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", type=Path, default=Path("baseline_group_rank.exe"))
    parser.add_argument("--corpus", type=Path, default=Path("corpus"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    labels = json.loads((args.corpus / "manifest.json").read_text())
    cases = [meta for meta in labels if set(meta["shape"]) == {2} and 3 <= len(meta["shape"]) <= 12]
    workers = {name: GroupSolver(args.executable, name) for name in ("balanced", "half")}
    samples = []
    rng = random.Random(20261115)
    try:
        for repeat in range(args.repeats):
            rng.shuffle(cases)
            for meta in cases:
                for branch in rng.sample(list(workers), 2):
                    start = time.perf_counter_ns()
                    source, target = read_case(args.corpus / (meta["name"] + ".ti"))
                    read_ms = (time.perf_counter_ns() - start) / 1e6
                    row = solve_pair(workers[branch], source, target, branch + "-runs")
                    row["total_including_read_ms"] = read_ms + row["total_ms"]
                    row["read_ms"] = read_ms
                    if meta["expected"] in ("yes", "no") and row["result"] != meta["expected"]:
                        raise RuntimeError(f"{branch} produced the wrong decision for {meta['name']}")
                    samples.append({"case": meta["name"], "order": len(meta["shape"]),
                                    "branch": branch, "repeat": repeat, **row})
    finally:
        for worker in workers.values():
            worker.close()
    groups = defaultdict(list)
    for row in samples:
        groups[row["branch"], row["order"]].append(row)
    summary = [{
        "branch": branch, "order": order, "cases": len(entries) // args.repeats,
        "fallback_cases": len({row["case"] for row in entries if row["group_fallback"]}),
        "median_compiler_ms": median(row["compiler_ms"] for row in entries),
        "median_backend_algorithm_ms": median(row["backend_ms"] for row in entries),
        "median_backend_wall_ms": median(row["backend_wall_ms"] for row in entries),
        "median_end_to_end_ms": median(row["total_including_read_ms"] for row in entries)
    } for (branch, order), entries in sorted(groups.items())]
    report = {"method": "Persistent workers independently apply the same exact algorithm; "
                        "the only change is where the sparse coordinate compiler partitions each mode. "
                        "Randomized interleaving compares the two modes for each input.",
              "repeats": args.repeats, "summary": summary, "samples": samples}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
