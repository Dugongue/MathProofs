# Intermediate problems for signed tensor isomorphism over F₃

Let P₀ be ordinary tensor isomorphism, P₁ one-sign TI, P₂ two-sign TI, and P₃ special-linear TI. All four problems take explicit three-tensor pairs. The following comparisons have polynomial-time many-one reductions to and from their indicated endpoints.

| Interval | Problems and results |
| --- | --- |
| In each of P₀ ≤ P₁, P₁ ≤ P₂ and P₂ ≤ P₃ | Three width levels log² L, log³ L and log⁴ L for the extra designated determinant on a bounded-order tensor system, with all other designated roles unrestricted. Every forward arrow is proved. Every reverse arrow fails in the bounded-order compiler model that retains all valid transporters on invariant subquotients. [Proof](Width.md) |
| P₁ ≤ P₂ | A source automorphism may correct the first relative sign only when that same automorphism is positive in the second mode. Exactly two correlated one-sign probes implement the verdict. Affine-copy disjunctions cannot reverse either endpoint arrow. [Proof](Switch.md) |
| P₂ ≤ P₃ | A source automorphism may correct the first relative sign only when positive in the first mode, and one relative transporter must also pass the second sign test. Exactly two correlated two-sign probes implement it. Affine-copy disjunctions cannot reverse either endpoint arrow. [Proof](Switch.md) |
| P₀ ≤ P₁ | Even tensor-decorated graph isomorphism requires one graph isomorphism to match the tensor decorations while giving an even permutation. This has a polynomial-time Turing reduction to TI and a single-instance reduction to one-sign TI. [Proof](EvenList.md) |

Two checks remove further candidates from the list. Even matching of independent tensor-orbit lists, including a fixed number of parity tests on overlapping marked sets, is already many-one equivalent to ordinary TI. A polynomial-size monotone formula uses a positive multiset-match test and exact inversion parity on the unique-match branch. Restricting two-sign TI to a source admitting a swap of the tested modes gives a structural characterization of an existing middle rung. A different formulation where the mode swap bypasses an independent sign is equivalent to two independent one-sign tests. [Even list collapse](EvenList.md) · [Mode-swap equivalences](SwapGuard.md)

The width result quantifies the gap for exact transporters beyond the logarithmic exterior-lock threshold. The guarded correction results distinguish two additional tests in a model allowing fixed linear combinations of independent relative and source stabilizer sign profiles. These models are separate. The number of distinct unrestricted polynomial many-one degrees remains open, including for the four endpoints. All proofs in this packet are informal. The parent containment question is [Open Question 1.9 of Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5).

Three-direction correction also lies between two independent one-sign tests and a shared two-sign test. [Proof](ThreeLines.md)
