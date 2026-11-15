"""Replay timed witnesses and exhaust axis layouts on the binary corpora."""
import argparse
from collections import Counter
from itertools import permutations
import json
from pathlib import Path

from audit_tensor import (Field, classify, offset,
                          rank_signature, records, tensor_indices, tensor_values,
                          verify_results)


def audit_timing(pair_root, result_root, corank_path):
    labels = {}
    for path in pair_root.glob("*/labels.jsonl"):
        for row in records(path):
            labels[row["id"]] = row
    report = {}
    for path in sorted(result_root.glob("*.jsonl")):
        counts = Counter()
        for row in records(path):
            item = labels[row["id"]]
            methods = [(method, row[method]) for method in ("crossed", "baseline")]
            if "fallback" in row["hybrid"]:
                methods.append(("fallback", row["hybrid"]["fallback"]))
            for method, got in methods:
                if got["status"] != "unknown":
                    assert got["status"] == item["expected"], (method, row["id"], got["status"])
                tested = verify_results([item], [{**got, "id": row["id"]}], check_no=True)
                counts.update({f"{method}:{k}": v for k,v in tested.items()})
            counts["pairs"] += 1
        report[path.stem] = dict(counts)
    if corank_path is not None:
        reference = json.loads(corank_path.read_text(encoding="utf-8"))
        counts = Counter()
        for group in reference["families"].values():
            for row in group["rows"]:
                item = labels[row["id"]]
                for mode in ("fixed", "all"):
                    result = row[mode]
                    if result["status"] != "unknown":
                        assert result["status"] == item["expected"], (mode, row["id"], result["status"])
                    tested = verify_results([item], [{**result, "id": row["id"]}], check_no=True)
                    counts.update({f"{mode}:{k}": v for k, v in tested.items()})
                counts["pairs"] += 1
        report["published_corank_reimplementation"] = dict(counts)
    for name, detail in report.items():
        if not detail.get("pairs"):
            raise ValueError(f"Empty timing file for {name}")
        if any(key.startswith(("crossed:no_unknown", "baseline:no_unknown", "fallback:no_unknown",
                               "fixed:no_unknown", "all:no_unknown")) for key in detail):
            raise ValueError(f"A negative answer lacks an exact audit certificate for {name}")
    return report


def all_layouts(path):
    count = Counter()
    accepted = {}
    for obj in records(path):
        shape = obj["dims"]
        assert obj["field"] == 2 and len(shape) == 4 and len(set(shape)) == 1
        field = Field(2)
        values = tensor_values(obj, field)
        count["total"] += 1
        cuts = rank_signature(shape, values, field)[4:]
        side = shape[0] ** 2
        if sum(k == side for k in cuts) < 2:
            continue
        count["two_full_cuts"] += 1
        wins = []
        indices = tensor_indices(shape)
        for g in permutations(range(4)):
            inverse = tuple(g.index(i) for i in range(4))
            rotated = [values[offset(tuple(x[i] for i in inverse), shape)] for x in indices]
            if classify(shape,rotated,field)["gate"] == "scalar":
                wins.append(g)
        if wins:
            count["accepted"] += 1
            count["new_after_identity"] += (0,1,2,3) not in wins
            accepted[obj["id"]] = wins
    return {**count, "accepted_layouts_by_id": accepted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    layouts = commands.add_parser("layouts")
    layouts.add_argument("datasets", nargs="+", type=Path)
    timings = commands.add_parser("timings")
    timings.add_argument("pairs", type=Path)
    timings.add_argument("results", type=Path)
    timings.add_argument("--corank", type=Path)
    args = parser.parse_args()
    if args.command == "layouts":
        answer = {path.stem: all_layouts(path) for path in args.datasets}
    else:
        answer = audit_timing(args.pairs, args.results, args.corank)
    print(json.dumps(answer, indent=2))


if __name__ == "__main__":
    main()
