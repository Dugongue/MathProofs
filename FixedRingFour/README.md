# Four extensions of tensor isomorphism over fixed finite rings

The fixed-ring theorem equates ordinary three-tensor isomorphism over fixed finite commutative rings with the same characteristic prime support. These four results isolate the cost of selecting a residue map, show how to lift a selected map, and classify all lifts in a concrete regular case. [Literature and priority audit](Priority.md)

| Result | Scope |
| --- | --- |
| [Complete tensor isomorphism in one congruence class](CongruenceClass.md) | For every finite local nonfield, ordinary residue-field TI reduces to tensors with full flattenings and identical entries modulo a fixed nonzero simple socle ideal. Over $\mathbb Z/p^e\mathbb Z$, the last digit carries the whole input. The reduction has linear side lengths and recovers transporters. |
| [Arbitrary prime-power precision](Algorithms.md) | Over $\mathbb Z/p^e\mathbb Z$, including nonfree modules, matrix logarithms reduce each shallow transporter test to linear congruences. The unrestricted decision, search and count bound is $p^{k\sum_i n_i^2}\operatorname{poly}(\text{input},e,\log p)$, with $k=1$ for odd $p$ and $2$ for $p=2$. |
| [Prescribed residue maps over arbitrary finite local rings](Tensor.md) | A deterministic bit-polynomial algorithm with a specified residue tuple works for presented nonfree modules and nonprincipal coefficient rings. It produces witnesses and counts, handles determinants on free modes, and canonizes congruence orbits. |
| [Normal forms and class counts for tame tensor lifts](Geometry.md) | When the infinitesimal stabilizer consists of the two scalar directions, a linear slice gives exact congruence normal forms. When the residual stabilizer is prime to the characteristic, the remaining orbit count and residual stabilizer distribution depend only on the residue tensor and the size of the maximal ideal. Explicit examples occur in unbounded dimension over each fixed residue field. |


## A common complexity consequence

Let $R$ be a finite local ring in additive cyclic coordinates with a multiplication table on the additive generators, and $q=|R/\mathfrak m|$. For dense presented tensors, let $n_i$ be the dimensions of their mode modules modulo $\mathfrak m$. Unrestricted decision, witness search, and exact counting take
$$
q^{\sum_i n_i^2}\operatorname{poly}(\text{input length}).
$$
To see this, recover the maximal ideal and the residue modules by the linear arithmetic of the prescribed-residue theorem. Construct residue-field bases greedily using additive linear span under a prime-field basis of the residue field. Enumerate all square matrices in these bases, discard singular tuples, and run that theorem on each remaining tuple. A full transporter has exactly one residue tuple, so the counts add without overlaps. This bound includes $p=2$ with only one enumerated residue digit on free prime-power modes. The logarithmic method provides a different certified linear description of all shallow stabilizers and a fast-field-algorithm transfer under the stated residue promise.

The proofs are written mathematics prepared for MathProofs with AI assistance. The accompanying finite scripts test selected cases. [NormalizeIsotopy.lean](NormalizeIsotopy.lean) independently verifies the monoid identity used for the first construction, with transitive axiom $\texttt{propext}$. The full results are written proofs.
