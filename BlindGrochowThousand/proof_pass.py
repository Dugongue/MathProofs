"""Freeze disjoint structural queues and independently audit their formal outputs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from fanin import freeze


def write_json(path, data):
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(data, handle, indent=2, ensure_ascii=False)
        handle.write("\n")


def plan(args):
    if args.keep < 1:
        raise SystemExit("Choose a positive candidate count.")
    full = freeze(args.bank, args.seed, args.keep * len(args.quotas))
    if len(full["motifs"]) < args.keep * len(args.quotas):
        raise SystemExit(f"Only {full['total']} structural candidates meet the filter.")
    args.output.mkdir(parents=True, exist_ok=False)
    worker_count = len(args.quotas)
    for i, quota in enumerate(args.quotas):
        write_json(args.output / f"worker-{i + 1}.json", {
            "seed": full["seed"],
            "declarations": full["declarations"],
            "total": full["total"],
            "quota": quota,
            "motifs": full["motifs"][i::worker_count],
        })
    print(f"{worker_count} disjoint queues, {args.keep} candidates per queue, "
          f"{sum(args.quotas)} audited conclusions targeted.")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(args):
    manifest = json.loads(args.manifest.read_bytes())
    workers = manifest["workers"]
    if args.target < 1 or len(workers) != args.workers:
        raise SystemExit("Manifest must contain the requested number of workers and a positive target.")
    names = [name for worker in workers for name in worker["theorems"]]
    claim_ids = [claim for worker in workers for claim in worker["claims"]]
    files = [(args.manifest.parent / worker["source"]).resolve(strict=True) for worker in workers]
    if (len(set(files)) != len(files) or len(set(names)) != len(names)
            or len(set(claim_ids)) != len(claim_ids)):
        raise SystemExit("Each batch must have distinct sources, declaration names and reviewed claim IDs.")
    for worker in workers:
        if not worker["theorems"] or len(worker["theorems"]) != len(worker["claims"]):
            raise SystemExit("Each theorem needs one reviewed claim ID.")
    args.output.mkdir(parents=True, exist_ok=False)
    rows, successes = {}, 0
    audit_root = args.output.resolve()
    for index, (worker, source) in enumerate(zip(workers, files), start=1):
        directory = audit_root / f"worker-{index}"
        original_hash = sha256(source)
        completed = subprocess.run([
            sys.executable, "-B", "-X", "utf8", str(args.checker.resolve()),
            str(source), "--runs-dir", str(directory), "--theorem", *worker["theorems"],
            "--timeout", str(args.seconds),
        ], capture_output=True, encoding="utf-8", errors="replace")
        (audit_root / f"worker-{index}.log").write_text(
            completed.stdout + completed.stderr, encoding="utf-8")
        receipts = list(directory.glob("*/receipt.json"))
        report = json.loads(receipts[0].read_bytes()) if len(receipts) == 1 else {}
        targets = report.get("theorems", [])
        valid = (
            completed.returncode == 0
            and report.get("status") == "VERIFIED"
            and original_hash == report.get("sha256") == sha256(source)
            and [row["theorem"] for row in targets] == worker["theorems"]
        )
        rows[worker["source"]] = {"sha256": original_hash,
                                  "status": "VERIFIED" if valid else "REJECTED",
                                  "theorems": targets if valid else []}
        if valid:
            successes += len(targets)
        print(f"{source.name} {'verified' if valid else 'rejected'}", flush=True)
    write_json(audit_root / "Audit.json", rows)
    print(f"{successes}/{args.target} distinct reviewed conclusions verified.")
    all_verified = all(row["status"] == "VERIFIED" for row in rows.values())
    return 0 if successes >= args.target and all_verified else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(required=True)
    planner = commands.add_parser("plan")
    planner.add_argument("bank", type=Path)
    planner.add_argument("output", type=Path)
    planner.add_argument("--seed", type=int, required=True)
    planner.add_argument("--keep", type=int, default=128)
    planner.add_argument("--quotas", nargs="+", type=int, default=[3, 3, 2, 2])
    planner.set_defaults(run=plan)
    verifier = commands.add_parser("audit")
    verifier.add_argument("manifest", type=Path)
    verifier.add_argument("checker", type=Path)
    verifier.add_argument("output", type=Path)
    verifier.add_argument("--target", type=int, default=10)
    verifier.add_argument("--workers", type=int, default=4)
    verifier.add_argument("--seconds", type=int, default=220)
    verifier.set_defaults(run=audit)
    args = parser.parse_args()
    if hasattr(args, "quotas") and any(n <= 0 for n in args.quotas):
        parser.error("All worker quotas must be positive.")
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
