"""Replay the published synthetic corpus with actual Nauty/Traces."""
import argparse
import collections
import json
from pathlib import Path
import random
from statistics import median
import time

from baseline_nauty import DreadnautSession, solve_file


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=Path("corpus"))
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--max-order", type=int, default=12)
    parser.add_argument("--timeout", type=float, default=12)
    parser.add_argument("--algorithm", choices=["s", "t"], default="t")
    args = parser.parse_args()
    selected = [
        item for item in json.loads((args.corpus / "manifest.json").read_text())
        if set(item["shape"]) == {2} and len(item["shape"]) <= args.max_order
    ]
    rng = random.Random(19920431)
    samples = []
    worker = None
    startup_times = []
    try:
        for repeat in range(args.repeats):
            rng.shuffle(selected)
            for item in selected:
                if worker is None or worker.proc.poll() is not None:
                    start = time.perf_counter()
                    worker = DreadnautSession(None, args.runtime)
                    startup_times.append(time.perf_counter() - start)
                path = args.corpus / (item["name"] + ".ti")
                result = solve_file(path, None, args.runtime, args.timeout, args.algorithm, worker)
                result["repeat"] = repeat
                result["expected"] = item["expected"]
                if result["status"] == "decided":
                    want = item["expected"]
                    if want in ("yes", "no") and result["isomorphic"] != (want == "yes"):
                        raise AssertionError(f"{item['name']} disagreed with the expected decision")
                samples.append(result)
    finally:
        if worker is not None:
            worker.close()
    groups = collections.defaultdict(list)
    for result in samples:
        groups[result["order"]].append(result)
    summary = [{
        "order": order, "cases": len(entries) // args.repeats,
        "statuses": dict(collections.Counter(row["status"] for row in entries)),
        "with_full_solver": sum(row.get("method") == "canonical graph comparison" for row in entries),
        "median_total_ms": median(row["total_s"] for row in entries) * 1e3,
        "median_build_ms": median(row["build_s"] for row in entries) * 1e3,
        "median_full_solver_ms": (
            median(row["solver_s"] for row in entries if "solver_s" in row) * 1e3
            if any("solver_s" in row for row in entries) else None
        ),
    } for order, entries in sorted(groups.items())]
    report = {"backend": "Bundled nauty 2.7r1.p1, " + ("Traces" if args.algorithm == "t" else "sparse nauty"),
              "method": "One warm external worker, one complete file read and evaluation-incidence graph encoding per sample. "
                        "Times include request transfer, exact comparison and witness verification. One-time startup separate.",
              "worker_startup_s": startup_times, "summary": summary, "samples": samples}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
