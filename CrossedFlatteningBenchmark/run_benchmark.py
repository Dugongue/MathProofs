"""Coverage scan and reproducible real-data TI benchmark."""
import argparse
from collections import Counter
from itertools import product
import json
from math import prod
from pathlib import Path
from random import Random
from statistics import median
from subprocess import TimeoutExpired, run
import sys
from time import perf_counter

import crossed
from audit_tensor import Field, certify_transport

HERE = Path(__file__).resolve().parent


def records(path):
    with path.open(encoding="utf-8-sig") as handle:
        for line in handle:
            if line.strip():
                yield json.loads(line)


def write(path, payload):
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + "\n", encoding="utf-8")


def values(obj):
    if "entries" in obj:
        entries = obj["entries"]
    else:
        support = {tuple(p) for p in obj["ones"]}
        entries = [int(p in support) for p in product(*(range(n) for n in obj["dims"]))]
    if len(entries) != prod(obj["dims"]):
        raise ValueError("Incorrect entry count.")
    return crossed.parse(obj["field"], entries)


def scan(source, output):
    counts, profiles = Counter(), Counter()
    start = perf_counter()
    with output.open("w", encoding="utf-8") as handle:
        for obj in records(source):
            field, dims = obj["field"], obj["dims"]
            if len(dims) != 4 or dims[:2] != dims[2:] or min(dims) < 2:
                row = {"id": obj["id"], "gate": "format_outside"}
            else:
                p = None if field == "Q" else field
                item, certificate = crossed.rank_certificate(values(obj), dims[:2], p)
                full = prod(dims[:2])
                counts["first_full"] += item.ranks[0] == full
                counts["cross_full"] += item.ranks[1] == full
                counts["both_full"] += item.ranks == (full, full)
                counts["modular_certificates"] += certificate
                gate = "scalar" if item.supported else "nonscalar" if item.commutants else "singular"
                profiles[str((item.ranks, item.commutants))] += 1
                row = {"id": obj["id"], "gate": gate, "ranks": item.ranks,
                       "commutants": item.commutants, "modular_certificate": certificate}
            counts[row["gate"]] += 1
            counts["total"] += 1
            handle.write(json.dumps(row, separators=(",", ":")) + "\n")
    summary = {"counts": counts, "profiles": profiles, "coverage_seconds": perf_counter() - start}
    write(output.with_suffix(".summary.json"), summary)
    print(json.dumps(summary, sort_keys=True))


def random_maps(dims, p, rng, general):
    maps = []
    for n in dims:
        a = crossed.identity(n)
        rng.shuffle(a)
        if general:
            for _ in range(2*n):
                i, j = rng.sample(range(n), 2)
                w = rng.choice((-1, 1)) if p is None else rng.randrange(1, p)
                vals = [x + w*y for x, y in zip(a[i], a[j])]
                a[i] = vals if p is None else [x % p for x in vals]
        maps.append(a)
    return maps


def balanced_ranks(entries, dims, p):
    answer = []
    for left, right in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
        order = left + right
        width = prod(dims[i] for i in right)
        strides = [prod(dims[i+1:]) for i in range(4)]
        view = [entries[sum(x*strides[i] for i, x in zip(order, j))]
                for j in product(*(range(dims[i]) for i in order))]
        _, pivots = crossed.reduce_rows(crossed.rows(view, width), width, p)
        answer.append(len(pivots))
    return tuple(answer)


def no_certificate(a, b):
    if (a["field"], a["dims"]) != (b["field"], b["dims"]):
        return None
    dims = a["dims"]
    p = None if a["field"] == "Q" else a["field"]
    x, y = values(a), values(b)
    if balanced_ranks(x, dims, p) != balanced_ranks(y, dims, p):
        return "rank negative"
    pa, pb = (crossed.profile(z, dims[:2], p) for z in (x, y))
    if pa.supported and pb.supported:
        am, bm = (z.covariants[0][0] for z in (pa, pb))
        difference = sum(am[i][i]-bm[i][i] for i in range(len(am)))
        if difference if p is None else difference % p:
            return "same-rank trace negative"
    return None


def make_pairs(dataset, coverage, out, label, seed, raw_count, accepted_count, negative_count):
    objects = list(records(dataset))
    gates = {r["id"]: r["gate"] for r in records(coverage)}
    if sorted(a["id"] for a in objects) != sorted(gates):
        raise ValueError("Mismatched coverage list.")
    rng = Random(seed)
    rng.shuffle(objects)
    cases = []

    def plant(a, stratum, general):
        field, dims = a["field"], a["dims"]
        p = None if field == "Q" else field
        x = values(a)
        witness = random_maps(dims, p, rng, general)
        y = crossed.apply(x, dims[:2], witness, p)
        if x == y:
            witness = random_maps(dims, p, rng, general)
            y = crossed.apply(x, dims[:2], witness, p)
        cases.append({"field": field, "dims": dims, "src": x, "dst": y, "expected": "yes",
                      "stratum": stratum, "source_id": a["id"], "input_gate": gates[a["id"]],
                      "planted": witness})

    accepted = [a for a in objects if gates[a["id"]] == "scalar"]
    for a in objects[:raw_count]:
        plant(a, "unconditional planted", True)
    for a in accepted[:accepted_count]:
        plant(a, "covered planted", True)
    for a in accepted[accepted_count:accepted_count+2]:
        plant(a, "covered permutation", False)
    counts = Counter()
    for pool in (objects[:20], accepted[:20]):
        for a, b in zip(pool[::2], pool[1::2]):
            reason = no_certificate(a, b)
            if reason is None or counts[reason] >= negative_count:
                continue
            counts[reason] += 1
            cases.append({"field": a["field"], "dims": a["dims"], "src": values(a), "dst": values(b),
                          "expected": "no", "stratum": reason, "source_id": a["id"], "target_id": b["id"]})
    out.mkdir(parents=True, exist_ok=False)
    with (out / "labels.jsonl").open("w", encoding="utf-8") as manifest:
        for i, item in enumerate(cases):
            item["id"] = f"{label}-{i:03}"
            write(out / f"{item['id']}.json", {k: item[k] for k in ("id", "field", "dims", "src", "dst")})
            manifest.write(json.dumps(item, default=str, separators=(",", ":")) + "\n")
    print(f"{len(cases)} pairs for {label}.")


def call(args, timeout):
    start = perf_counter()
    try:
        proc = run([sys.executable, "-B", *map(str, args)], timeout=timeout,
                   capture_output=True, text=True, encoding="utf-8")
    except TimeoutExpired:
        return {"status": "unknown", "reason": "process watchdog", "wall_seconds": perf_counter()-start}
    wall = perf_counter() - start
    if proc.returncode != 0:
        raise RuntimeError(f"Solver exited {proc.returncode}: {proc.stderr.strip()}")
    return {**json.loads(proc.stdout), "wall_seconds": wall}


def independently_check(item, result):
    if result["status"] == "unknown":
        return
    if result["status"] != item["expected"]:
        raise ValueError(f"Incorrect decision in {item['id']}")
    if result["status"] == "yes" and not certify_transport(
            item["dims"], item["src"], item["dst"], result["witness"], Field(item["field"])):
        raise ValueError(f"Independent witness check failed in {item['id']}")


def time_pairs(fixtures, output, cadical, timeout, rational_backend, warm, q_exact):
    if warm:
        from baseline_external import solve_file
        if rational_backend == "z3":
            import z3  # Load shared dependencies before resident timing.
        if q_exact:
            from crossed_q_exact import solve as solve_q

    with output.open("w", encoding="utf-8", buffering=1) as handle:
        for i, item in enumerate(records(fixtures / "labels.jsonl")):
            if "planted" in item:
                independently_check(item, {"status": "yes", "witness": item["planted"]})
            path = fixtures / f"{item['id']}.json"
            p = item["field"]
            backend = rational_backend if p == "Q" else "cadical" if p == 2 else "z3"
            base = [HERE / "baseline_external.py", "--backend", backend, "--timeout", timeout]
            if backend in ("cadical", "hensel"):
                if cadical is None:
                    raise ValueError("CaDiCaL executable path required.")
                base += ["--executable", cadical]
            base.append(path)
            use_fast = q_exact and p == "Q"
            then = [HERE / ("crossed_q_exact.py" if use_fast else "crossed.py"), path]
            watchdog = timeout + 8

            def run_crossed():
                if not warm:
                    return call(then, watchdog)
                start = perf_counter()
                solver = solve_q if use_fast else crossed.solve
                ans = solver(json.loads(path.read_text(encoding="utf-8")))
                return {**ans, "wall_seconds": perf_counter() - start}

            def run_base():
                if not warm:
                    return call(base, watchdog)
                start = perf_counter()
                ans = solve_file(path, backend, timeout, cadical)
                return {**ans, "wall_seconds": perf_counter() - start}

            if i % 2:
                reference = run_base()
            stage_start = perf_counter()
            gate = run_crossed()
            fallback = run_base() if gate["status"] == "unknown" else None
            hybrid = {"status": (fallback or gate)["status"],
                      "wall_seconds": perf_counter() - stage_start,
                      "used_fallback": fallback is not None}
            if fallback is not None:
                hybrid["fallback"] = fallback
            if i % 2 == 0:
                reference = run_base()
            runs = [gate, run_crossed(), run_crossed()]
            crossed_result = {**gate, "wall_seconds": median(x["wall_seconds"] for x in runs),
                              "wall_runs": [x["wall_seconds"] for x in runs]}
            for answer in [*runs, reference, *([fallback] if fallback else [])]:
                independently_check(item, answer)
            row = {k: v for k, v in item.items() if k not in ("src", "dst", "planted")}
            row.update(crossed=crossed_result, baseline=reference, hybrid=hybrid)
            handle.write(json.dumps(row, default=str, separators=(",", ":")) + "\n")
            print(f"{item['id']} {gate['status']} {crossed_result['wall_seconds']:.3f}s "
                  f"{reference['status']} {reference['wall_seconds']:.3f}s", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    scan_cli = commands.add_parser("coverage")
    scan_cli.add_argument("dataset", type=Path)
    scan_cli.add_argument("output", type=Path)
    pairs_cli = commands.add_parser("pairs")
    pairs_cli.add_argument("dataset", type=Path)
    pairs_cli.add_argument("coverage", type=Path)
    pairs_cli.add_argument("output_dir", type=Path)
    pairs_cli.add_argument("--label", required=True)
    pairs_cli.add_argument("--seed", default=191743, type=int)
    pairs_cli.add_argument("--unconditional", default=4, type=int)
    pairs_cli.add_argument("--covered", default=4, type=int)
    pairs_cli.add_argument("--negative", default=3, type=int)
    time_cli = commands.add_parser("time")
    time_cli.add_argument("fixtures", type=Path)
    time_cli.add_argument("output", type=Path)
    time_cli.add_argument("--cadical", type=Path)
    time_cli.add_argument("--timeout", default=3, type=float)
    time_cli.add_argument("--rational-backend", default="z3")
    time_cli.add_argument("--warm", action="store_true",
                          help="Keep Python resident and include each input read and witness verification.")
    time_cli.add_argument("--q-exact", action="store_true",
                          help="Use the integer-arithmetic crossed implementation over Q.")
    args = parser.parse_args()
    if args.command == "coverage":
        scan(args.dataset, args.output)
    elif args.command == "pairs":
        make_pairs(args.dataset, args.coverage, args.output_dir, args.label, args.seed,
                   args.unconditional, args.covered, args.negative)
    else:
        time_pairs(args.fixtures, args.output, args.cadical, args.timeout, args.rational_backend,
                   args.warm, args.q_exact)


if __name__ == "__main__":
    main()
