# A metric covering bound from a small product

Let $A,B$ be finite subsets of a seminormed commutative group. Suppose $B$ is nonempty, lies in the radius-$R$ ball around $c$, and is an $\varepsilon$-net for a possibly infinite set $U$. If $|AB|\le K|B|$, there is a finite $F\subseteq A$ with $|F|\le K$ such that every element of $AU$ has distance at most $3R+\varepsilon$ from some $fc$, $f\in F$. More generally, $A$ admits an internal $D$-net of the same size whenever all pairwise distances in $B$ are at most $D$. The third Lean declaration obtains nonemptiness from a factorization transversal and a cofinality witness. The same geometric conclusion follows directly assuming $B$ nonempty, by the identical proof using the first declaration. [Lean proof](Joint.lean)

**Argument.** Ruzsa's covering lemma gives $A\subseteq FBB^{-1}$. For $a=fxy^{-1}$ with $x,y\in B$, translation invariance gives $d(a,f)=d(x,y)\le 2R$. Given $u\in U$, choose $b\in B$ with $d(u,b)\le\varepsilon$. Thus $d(au,fc)\le d(a,f)+d(u,b)+d(b,c)\le 3R+\varepsilon$. The cost in centers depends on multiplicative expansion while the radius accounts for the metric uncertainty of the probe. Ruzsa's lemma and metric translation invariance are classical, and this corollary is an elementary consequence. [Mathlib's covering lemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/RuzsaCovering.html)

## What the blind pass found

The search read declaration and binder records from the 590,787-declaration Covenant v6 binary bank. Declaration names, descriptions and module strings were unavailable to candidate generation. The protocol compared module identifiers for inequality. It matched hash-consed expression-node identities between theorem outputs and explicit input binders, including their de Bruijn indices. Their surrounding binder contexts still require unification.

An initial scan admitted variable-headed outputs and yielded 78,186 four-node paths. Bare variables produced misleading matches when viewed in different contexts. Requiring constant heads on both endpoints and keeping heads used by between 3 and 3,200 theorem conclusions and expressions with at most 18 producers left 14,465 directed edges with distinct modules. There were 656 four-node paths traversing four distinct modules and four distinct output expressions. The selection protocol assigned pseudorandom priorities (Python seed 17713, bank enumeration order) before any theorem names were loaded. Of the first 24 exposed paths, the fifth supplied the following four compatible operations. Human choice after disclosure favored an independently interpretable conclusion.

| Producer record | Output node | Consumer record | Explicit binder position (zero-based) |
|---:|---:|---:|---:|
| 136823 | 1369063 | 58986 | 5 |
| 58986 | 2953386 | 165105 | 6 |
| 165105 | 389969 | 295508 | 7 |

The recovered chain is `Subgroup.IsComplement.nonempty_left` → `IsCofinalFor.nonempty` → `Metric.IsCover.nonempty` → `Set.ruzsa_covering_mul`. Its shared logical interface is nonemptiness. A group complement supplies a point in its left factor. Cofinality supplies a point above it, and a cover supplies a nearby probe point. The first two steps only witness existence. The metric radius enters the stronger product theorem when the cover is used a second time, quantitatively. The four-way chain was discovered structurally, and the metric extension was worked out after disclosure. The counts refer to this binary bank alone.

### Replaying the blind selection

Save the code below as a Python file and pass the v6 bank directory as its only argument. The output consists of declaration record numbers and slot positions. The script reads only the two tables that describe declarations and binders.

```python
from pathlib import Path
from struct import Struct
from collections import defaultdict,Counter
import random
import sys
base=Path(sys.argv[1])
ds=list(Struct('<IBBH6I').iter_unpack((base/'decls.bin').read_bytes()))
bb=(base/'binders.bin').read_bytes()
binder=Struct('<3I')
out=defaultdict(list); freq=Counter()
for i,d in enumerate(ds):
 if d[1]==2:
  out[d[5]].append(i); freq[d[6]]+=1
edges=defaultdict(list)
for i,d in enumerate(ds):
 if d[1]!=2:continue
 for j in range(d[3]):
  ty,bi,head=binder.unpack_from(bb,12*(d[8]+j))
  if head==4294967295 or ds[i][6]==4294967295 or bi%4 or not 3<=freq[head]<=3200 or not 1<=len(out.get(ty,()))<=18:continue
  for k in out[ty]:
   if ds[k][7]!=d[7]: edges[k].append((i,j))
rnd=random.Random(17713); paths=[]
for a in edges:
 for b,j in edges[a]:
  for c,k in edges.get(b,()):
   if len({ds[i][7] for i in [a,b,c]})!=3:continue
   for d,l in edges.get(c,()):
    if len({ds[i][7] for i in [a,b,c,d]})==4 and len({ds[i][5] for i in [a,b,c,d]})==4:
     paths.append((rnd.random(),a,b,c,d,j,k,l))
print(len(ds),sum(map(len,edges.values())),len(paths))
print(sorted(paths)[:24])
```
