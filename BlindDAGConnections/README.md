# Structural proof search with anonymous Lean ports

Four workers searched for compositions before reading the declaration names. Two used the packed term bank; a third sampled eight windows of the checked SQLite ports; the fourth used both. The packed bank has 590,787 declaration records. It represents a checkpoint of the registered library. Newer overlays, source-only catalogs and incompatible historical environments were outside that bank scan. The counts in the individual runs overlap.

## A common finite set of score observations

Let $A,B$ be nonempty finite sets in a seminormed commutative group, in multiplicative notation. Suppose $|AB|\le K|B|$, $B$ lies within distance $R$ of $c$, and $B$ is an $\varepsilon$-net for a nonempty set $U$. There exists a finite $F\subseteq A$ with $|F|\le K$ such that **simultaneously for every real 1-Lipschitz score** $\phi$,
$$
\sup_{z\in\overline{AU}}\phi(z)
\ \le\ \max_{f\in F}\phi(fc)+3R+\varepsilon .
$$
The closure is metric. $F$ can be chosen before seeing either the score or the values it takes.

The Ruzsa covering lemma gives $A\subseteq FBB^{-1}$. Two points of $B$ are at most $2R$ apart. Every $a$ is therefore within $2R$ of some $f$, and every $u$ is within $R+\varepsilon$ of $c$. Translation invariance puts $au$ within $3R+\varepsilon$ of $fc$. Take a score maximum over the translated centers and pass to the closure by continuity. For two products, apply the upper bound to $\phi$ on the first and to $-\phi$ on the second. A gap between the sampled scores greater than the sum of the two error allowances certifies disjoint closures.

Two independent walks supplied the covering and finite-observation parts of this argument. Lean checks both the version obtained from the first walk's cofinality and complement witnesses and the stronger statement above, which assumes only the geometric and cardinality hypotheses. For example, in additive notation take $A=\{0,\dots,99\}$, $B=\{0,\dots,9\}$, $U=[0,9]$ and $c=4.5$. Here $K=10.9$, $R=4.5$, and $\varepsilon=0.5$. At most ten observations bound the supremum of any such score on $[0,108]$ to within the stated one-sided additive allowance of 14. [Combined Lean source](Joint.lean) · [First search](Splice.md) · [Second search](Relation.md) · [Mathlib's Ruzsa lemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/RuzsaCovering.html)

## Other outputs

- An extremum test for a real Chebyshev polynomial encodes the return times of any periodic point. For permutations of a known degree $N$, the first $\lfloor N/2\rfloor$ extremum counts classify conjugacy, and every shorter initial prefix fails in the worst case. Lean verifies the return-time identity. The sharp cutoff has a written counting proof and exhaustive checks of all 28,627 cycle types in degrees 2 through 30. [Proof and controls](Return.md)
- Four project declarations combine to distinguish two families of tensors supported on slices normal to different axes. This is the familiar flattening-rank obstruction in a reusable all-field form. A separate seed led to a finite family of tests for arbitrary intersections of orbit closures in a Noetherian space. The latter is an existence theorem and supplies no effective bound on the family size. [Proofs and replay](Assembly.md)
- The metric route independently yields a score certificate for sampled isometric group orbits. A bounded covering radius in the Cayley graph converts generator displacements into explicit orbit-sampling errors. Scores may vary across a single orbit. [Certificate and sharpness example](Relation.md)

## Reproduce the anonymous selection

The packed-bank utility reads only the little-endian numeric declaration and binder arrays during discovery. It joins whole output expression IDs to explicit input expression IDs, requires distinct opaque module IDs, and caps the number of competing producers. A directed match between open terms still requires checking in the surrounding binder contexts. The seed controls deterministic tie-breaking. Only a separate reveal command reads the name table.

```text
python fanin.py BANK > shortlist.json
python fanin.py BANK --reveal shortlist.json
python mine.py PORT_DATABASE > sqlite-shortlist.json
python mine.py PORT_DATABASE --reveal sqlite-shortlist.json
python cycles.py
```

The retained shortlist contains 20 of 823 multiple-input matches. The notes report the actual paths chosen, including their pre-reveal positions. Selection among the revealed candidates, choice of additional lemmas and mathematical interpretation involved human-readable judgments. Exact port matches are discovery evidence. Thirteen named Lean declarations passed independent kernel and transitive axiom checks on their final sources. The shared metric file contains seven of them. The two assembly files additionally require the indicated Mathproof project imports. These corollaries show how the search can find usable connections; their priority as research theorems has not been established. [Frozen shortlist](Filtered.json) · [Packed-bank miner](fanin.py) · [SQLite miner](mine.py)
