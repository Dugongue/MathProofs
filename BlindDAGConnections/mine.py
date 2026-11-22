"""Discover bounded fan-in motifs on the checked port index, then reveal their names."""
import argparse
import hashlib
import json
import sqlite3
from functools import lru_cache
from pathlib import Path


def discover(db, seed, sample, cap):
    # The index IDs are opaque. Do not read names, module paths, or descriptions here.
    start = hashlib.sha256(seed.encode()).hexdigest()
    query = ("select id,content_id,type_node from operations where id >= ? "
             "and type_node is not null and kind='theorem' order by id limit ?")
    sinks = list(db.execute(query, (start, sample)))
    @lru_cache(maxsize=None)
    def producers(expr):
        hits = list(db.execute(
            "select operation from ports indexed by port_expression_role "
            "where expression=? and role='output' order by operation limit ?", (expr, cap + 1)))
        if len(hits) > cap:
            return []
        return [row for (op,) in hits for row in db.execute(
            "select id,content_id,type_node from operations where id=? and kind='theorem'", (op,))]
    motifs = []
    for sink, owner, typ in sinks:
        slots = db.execute("select position,expression from ports where operation=? and "
                           "role='input' and binder_info=0 order by position", (sink,))
        branches, owners, types, used = [], {owner}, {typ}, set()
        for slot, expr in slots:
            if expr in used:
                continue
            candidates = [p for p in producers(expr) if p[2] not in types]
            if not candidates:
                continue
            op, rev, ty = min(candidates, key=lambda p: (p[1] in owners,p[0]))
            owners.add(rev)
            types.add(ty)
            used.add(expr)
            branches.append(dict(slot=slot, expression=expr, producer=op))
        if len(branches) >= 2:
            motifs.append(dict(consumer=sink, inputs=branches, revisions=len(owners)))
    motifs.sort(key=lambda m: (-m["revisions"], -len(m["inputs"]), m["consumer"]))
    return dict(seed=seed, sample=len(sinks), cap=cap, total=len(motifs), matches=motifs)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("database", type=Path)
    cli.add_argument("--seed", default="indigo-43")
    cli.add_argument("--sample", type=int, default=2048)
    cli.add_argument("--cap", type=int, default=48)
    cli.add_argument("--keep", type=int, default=12)
    cli.add_argument("--reveal", type=Path, help="Read an already frozen JSON shortlist")
    cli.add_argument("--checkpoint", action="store_true", help="read a quiescent checkpoint without shared memory")
    args = cli.parse_args()
    # Immutable mode is opt-in for a quiescent checkpoint on read-only storage.
    suffix = "?mode=ro&immutable=1" if args.checkpoint else "?mode=ro"
    if args.checkpoint:
        wal = Path(str(args.database) + "-wal")
        if wal.exists() and wal.stat().st_size:
            cli.error("checkpoint mode requires an empty or absent WAL")
    with sqlite3.connect(args.database.resolve().as_uri()+suffix, uri=True) as db:
        if args.reveal:
            report = json.loads(args.reveal.read_text(encoding="utf-8-sig"))
            for motif in report["matches"]:
                nodes = [motif["consumer"]] + [i["producer"] for i in motif["inputs"]]
                print([db.execute("select name,module from operations where id=?",(op,)).fetchone() for op in nodes])
        else:
            report = discover(db,args.seed,args.sample,args.cap)
            report["matches"] = report["matches"][:args.keep]
            print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
