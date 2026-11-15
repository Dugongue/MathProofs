"""The direct CaDiCaL baseline on fixed cases across the shared corpus."""
import argparse
import collections
import json
from pathlib import Path
from statistics import median
import subprocess

from baseline_cadical import solve_file


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, default=Path("corpus"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=2)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    version = subprocess.run([str(args.cadical), "--version"], capture_output=True,
                             check=True, text=True).stdout.strip()
    manifest = json.loads((args.corpus / "manifest.json").read_text())
    named = {case["name"]: case for case in manifest}
    chosen = []
    sizes = collections.defaultdict(list)
    for case in manifest:
        sizes[tuple(case["shape"])].append(case)
    for dims, entries in sizes.items():
        for answer in ("yes", "no"):
            candidates = [case["name"] for case in entries
                          if case["expected"] == answer and "-iso-" in case["name"] or
                          case["expected"] == answer and "-no-" in case["name"]]
            candidates.sort()
            chosen.extend(candidates[:2 if len(dims) <= 6 else 1])
    chosen += [name for name in named if "ambig" in name or "GHZ" in name]
    samples = []
    for name in chosen:
        for iteration in range(args.repeats):
            path = args.corpus / (name + ".ti")
            result = solve_file(path, args.cadical, args.timeout)
            result["repeat"] = iteration
            want = named[name]["expected"]
            result["expected"] = want
            if result["status"] == "decided" and want in ("yes", "no") and result["isomorphic"] != (want == "yes"):
                raise AssertionError(f"{name} disagreed with expected decision")
            samples.append(result)
            if result["status"] != "decided":
                break
    groups = collections.defaultdict(list)
    for result in samples:
        groups[tuple(result["format"])].append(result)
    summary = []
    for dims, entries in sorted(groups.items(), key=lambda item: (len(item[0]), item[0])):
        decided = [row for row in entries if row["status"] == "decided"]
        summary.append({
            "format": dims, "cases": len({row["case"] for row in entries}),
            "statuses": dict(collections.Counter(row["status"] for row in entries)),
            "median_decided_total_ms": median(row["total_s"] for row in decided) * 1e3 if decided else None,
            "median_build_ms": median(row["build_s"] for row in entries) * 1e3,
            "median_decided_solver_with_process_ms": (
                median(row["solver_including_process_s"] for row in decided) * 1e3 if decided else None
            ),
        })
    report = {"backend": f"CaDiCaL {version}", "repeats_for_decisions": args.repeats,
              "timeout_s": args.timeout,
              "method": "Read tensor pair; build exact staged Tseitin CNF; start new native solver; "
                        "verify SAT witness on original tensor.",
              "summary": summary, "samples": samples}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
