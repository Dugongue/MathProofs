# Separating tensor slices and compressing orbit-closure tests

## A four-declaration tensor separation

Let the three modes all have size $n\ge 2$ over any field. Put an arbitrary square matrix $N$ in one slice normal to axis two, with zeros in the other slices. Put an invertible matrix $M$ in one slice normal to axis one of a second tensor. Independent invertible transformations of the three modes cannot carry the first tensor into the second. The source matrix may even be zero. This generalizes the single-tensor, same-matrix permutation example in the indexed source to arbitrary independent choices of the matrices and support indices. It follows classically by comparing the second flattening ranks, at most one and exactly $n$.

The proof composes four existing declarations. A private inactive coordinate annihilates a third-axis slab. Swapping the second and third axes transports this annihilator to the second axis. An invertible matrix on the target slab precludes a second-axis annihilator. The mismatched invariant implies inequivalence. In Lean the double swap simplifies by definitional equality. [Formal proof](AssemblyModes.lean)

## How the connection surfaced

The discovery pass streamed eight windows of 3,000 typed ports, starting at row IDs $1+220000k$ for $0\le k<8$, from the canonical indexed hypergraph. An edge required identical producer-output and explicit-consumer-input expression hashes. No names, documentation, proof bodies or subject keywords entered the joins. A preliminary window pass represented 3,579 operations and found 472 consumers with some cross-window match. Its largest fan-in used generic sort or function ports. A second pass required two theorem declarations in distinct modules (module labels were used for equality only), discarded producers whose output hash repeated an input hash, capped the within-window candidate count at 11 per input, and deduplicated by consumer type hash. This left 50 consumers and 46 distinct consumer signatures. Consumers were sorted by the number of distinct matched inputs, then opaque ID. Within each input the producer with lexicographically smallest ID was selected.

The tensor candidate was a lower-ranked one-input match in the first 25 distinct signatures revealed. The top two-input candidate involved generic logical implications. We selected the tensor match after seeing the frozen candidates. Port 5 of consumer `b1c43e0e919d` and the output of producer `70504bf1e715` shared the exact expression fingerprint beginning `18d09515ae`. These resolved to `not_glRel_of_mode2_mismatch` and `mode3Def_swap23`. Specialization to slabs and the two endpoint declarations `slab3_mode3Def` and `slab_not_mode2Def` were selected after revelation. This separates the blind search result from the mathematical completion. Sorting and extraction data are specific to the indexed revisions.

## One finite family decides all common degenerations

On a Noetherian topological space, an arbitrary family of orbit closures has a finite subfamily with precisely the same common points. The chosen source orbits work simultaneously for every target, including points chosen afterward. More generally this applies to every family of closed sets and to all closed upper cones of a project reduction system. No continuity hypothesis on the group action is needed for the orbit statement. There is no effective cardinality bound in this assertion.

A separate anonymous probe of 420 pseudorandom port row IDs (seed 2026112102) retained 42 theorem consumers and two rare cross-module exact matches. Producer `a24c149d9a7e` and input 4 of consumer `b271d3edb210` shared fingerprint `a30abbbb5c`. The consumer turned out to be universal reduction hardness transported through an intermediate object. The producer itself restated its own input and was discarded. After revelation, we asked whether the universal quantifier over sources admits finite replacement at all targets at once. In a Noetherian space the union of the complements of the tests is compact. The complements give an open cover and its finite subcover yields exactly that replacement. This lift uses identified Mathlib compactness theorems and is a standard consequence of Noetherianity; it is a human-directed extension of a blind seed. The theorem `finite_common_degenerations` applies directly to group orbits and `finite_reduction_tests` uses the existing project definition of a reduction system. [Formal proofs](Assembly.lean)

These bounded scans sample the checked typed index. Matching hashes alone do not settle how binder contexts align. The formal source supplies the required substitutions. Neither search establishes historical novelty.

## Replay the theorem-only search

Save this Python block as `window_search.py` and pass the checked port database path as its sole argument. The program opens the database read-only. Declaration names and descriptions never enter its queries. A new database revision can give different window populations.

```python
import sqlite3
import sys
from collections import defaultdict
from pathlib import Path

db = Path(sys.argv[1]).resolve().as_uri() + "?mode=ro"
conn = sqlite3.connect(db, uri=True)
ports = defaultdict(list)
for k in range(8):
    start = 220000 * k + 1
    query = """SELECT operation,position,role,expression,binder_info
               FROM ports WHERE rowid BETWEEN ? AND ? ORDER BY rowid"""
    for op, pos, role, expr, binder in conn.execute(query, (start, start + 2999)):
        ports[op].append((pos, role, expr, binder))

meta = {}
ops = list(ports)
for offset in range(0, len(ops), 500):
    batch = ops[offset:offset + 500]
    marks = ",".join("?" for _ in batch)
    query = f"SELECT id,kind,module,type_node FROM operations WHERE id IN ({marks})"
    for op, kind, module, typ in conn.execute(query, batch):
        meta[op] = (kind, module, typ)

producers = defaultdict(list)
for op, row in ports.items():
    if meta[op][0] == "theorem":
        inputs = {expr for _, role, expr, _ in row if role == "input"}
        for _, role, expr, _ in row:
            if role == "output" and expr not in inputs:
                producers[expr].append(op)

results = []
for op, row in ports.items():
    if meta[op][0] != "theorem":
        continue
    matches = []
    for pos, role, expr, binder in row:
        if role == "input" and binder == 0:
            choices = [p for p in producers[expr] if meta[p][1] != meta[op][1]]
            if 0 < len(choices) < 12:
                matches.append((pos, expr, min(choices)))
    if matches:
        results.append((len({e for _, e, _ in matches}), op, matches))

distinct = {}
for score, op, matches in sorted(results, reverse=True):
    distinct.setdefault(meta[op][2], (score, op, matches))
print(len(ops), len(results), len(distinct))
for score, op, matches in list(distinct.values())[:25]:
    print(score, op, matches)
```
