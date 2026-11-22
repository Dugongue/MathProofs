"""Find ports with multiple independent producers using only packed numeric term records."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
from struct import Struct

DECL = Struct("<IBBH6I")
BINDER = Struct("<3I")


def freeze(bank, seed, keep):
    declarations = list(DECL.iter_unpack((bank / "decls.bin").read_bytes()))
    binders = (bank / "binders.bin").read_bytes()
    outputs = defaultdict(list)
    for i, d in enumerate(declarations):
        if d[1] == 2:
            outputs[d[5]].append(i)
    samples = []
    total = 0
    for i, d in enumerate(declarations):
        if d[1] != 2:
            continue
        incoming = []
        modules, seen = {d[7]}, {d[5]}
        for j in range(d[3]):
            port, flags, head = BINDER.unpack_from(binders, BINDER.size*(d[8]+j))
            hits = outputs.get(port, ())
            if head == 4294967295 or flags % 4 or port in seen or not 1 <= len(hits) <= 16:
                continue
            for k in hits:
                other = declarations[k]
                if other[7] in modules:
                    continue
                modules.add(other[7])
                seen.add(port)
                incoming.append([j, k, port])
                break
        if len(incoming) >= 2:
            total += 1
            key = sha256(f"{seed}:{i}".encode()).hexdigest()
            samples.append((-len(incoming),key,dict(sink=i, sources=incoming)))
    samples.sort()
    return dict(seed=seed, declarations=len(declarations), total=total,
                motifs=[m for _,_,m in samples[:keep]])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bank",type=Path)
    parser.add_argument("--seed",type=int,default=47191)
    parser.add_argument("--keep",type=int,default=20)
    parser.add_argument("--reveal",type=Path)
    args=parser.parse_args()
    if args.reveal:
        decls=(args.bank/"decls.bin").read_bytes()
        names=(args.bank/"names.txt").read_text(encoding="utf8").splitlines()
        for m in json.loads(args.reveal.read_text(encoding="utf-8-sig"))["motifs"]:
            ids=[m["sink"]]+[x[1] for x in m["sources"]]
            print([(i,names[DECL.unpack_from(decls,i*DECL.size)[0]]) for i in ids])
    else:
        print(json.dumps(freeze(args.bank,args.seed,args.keep),indent=2))


if __name__=="__main__":
    main()
