# What the 234-entry atlas reduces the problem to

Let \(H\) be deterministic polynomial-time many-one reducibility from dense determinant-one three-tensor isomorphism to ordinary tensor isomorphism over \(\mathbb F_3\). The 234-entry atlas supports an exact, smaller formulation of \(H\) and several new sufficient subclasses. The tested combinations supply no contradiction to \(\neg H\). The fixed-field decision question remains open. [Earlier atlas](baseline/ATLAS.md) · [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## The exact missing lemma

Let \(A=\mathbb F_3 1\oplus X\oplus Z\), where \(\dim X\) is even and \(\dim Z\) is odd. The radical product is a symmetric bilinear map \(\beta:X\times X\to Z\) with spanned output and zero common radical. All other products of radical components vanish. Form
\[
  {\cal S}(A)=\{(u,v,w)\longmapsto(0,0,au+bv):a,b\in A\}
                 \ \subseteq\operatorname{End}_{\mathbb F_3}(A^2\oplus A).
\]
Every product of two operators in \({\cal S}(A)\) is zero.

**Lemma still needed.** On pairs \({\cal S}(A),{\cal S}(A')\) promised to be conjugate over \(\mathbb F_3\), compile the existence of a determinant-one conjugator to a single ordinary \(\mathbb F_3\) tensor-isomorphism instance in deterministic polynomial time.

This lemma is equivalent to \(H\). The proof recovers the regular multiplication algebra as the left idealizer. Any conjugator induces an algebra isomorphism \(\phi:A\to A'\). Its quotient block on \(A^2\) has determinant one, and its determinant on the common image \(A\) is exactly \(\det\phi\). Conversely \(\phi^{\oplus3}\) is a conjugator of that sign. Seven weighted cube-zero comparisons recover the three original signs by character separation, and one ordinary conjunction combines them. An ordinary guard removes the ordinary-conjugate promise. In reverse, \(H\) applies to the multiplication tensors of \(A,A'\), since every unit multiplication has determinant one. [Exact compiler and converse](SquareZeroClosure.md)

The same question can be posed for compact subgroups \(1+{\cal S}(A)\), all elementary abelian of exponent three. Their matrices satisfy \((g-I)(h-I)=0\) for every two group elements. The determinant restriction concerns conjugators of the embeddings.

## A test that fails even on this normal form

Take \(X\) of dimension \(n\equiv2\bmod4\), \(Z=\operatorname{Sym}^2X\), and use the free truncated product. Replacing \(\beta\) by \(-\beta\) gives a pair with an explicit odd ordinary conjugator and no even conjugator. Every corresponding tuple of fewer than \(n/2+2\) elements nevertheless has an even simultaneous conjugator. Two coordinate projections and \(n/2\) rows listing pairs of basis elements give a tuple of size exactly \(n/2+2\) with no even conjugator. This proves the sharp threshold on the square-zero family. On the single-copy regular nilpotent spaces the corresponding threshold is \(n\). These statements concern local tests on corresponding tuples. [Square-zero threshold](SquareZeroClosure.md) · [Single-copy proof](CommutingOperators.md)

## Where the strongest combinations stop

| Atlas entries used | What combines | What remains |
| --- | --- | --- |
| 8–14, 21, 77–78, 201–212, 228–234 | Positive ordinary compilers assemble determinant tests, compatible local witnesses and arbitrary-rank independent profiles. The new exact lower carrier reduces the needed input to one sign on very simple matrices. | A variable enabled by a comparison still needs an ordinary comparison for its elementary predicate. Tuple testing falls short by the sharp family above. |
| 22–31, 68–73, 79–118 | Ordered operator modules can remove orientation when every determinant-contributing multiplicity is logarithmic. Compact exponent-nine groups with surjective cube map and those with injective cube map each carry the exact degree question. | An intrinsic ordered-operator choice does not always bound those multiplicities. On the intersection where the cube map is bijective its quotient and center determinants cancel, so that intersection gives a positive special case without transferring either hard carrier. [Algebra combinations](AlgebraClosure.md) |
| 16–18, 60–67, 159–200 | Relative ranks over intrinsic centroid fields give a new one-query positive class, including a nonreduced local centroid with two unbounded odd relative dimensions. | Even closed geometric signed orbits and literally identical connected embedded ordinary stabilizers permit different rational signed answers. Scalar extension alone does not shrink the relative ranks used in the compiler. [Arithmetic combinations](DescentClosure.md) |
| 11–15, 35–59, 119–158 | Ordinary witness sampling, exact counting identities and query decoding give their stated upper bounds. A polynomial intrinsic spanning frame and a small stabilizer base allow a new nonadaptive many-one compilation from pinned ordinary comparisons. | Generic entry-by-entry pinning does not have the exact coset reflection required by the typed-system argument. Membership in the listed complexity classes gives no unconditional equality of their degrees. [Complexity combinations](SearchClosure.md) |

The same absolute finite-field extension reflection still applies: a proof of the general collapse over any fixed finite extension of \(\mathbb F_3\) would close \(H\). The positive local-centroid theorem does not give this assumption for arbitrary tensors.

The reductions, subclass theorems, and counterexamples are written mathematical proofs. The supporting polynomial identities in [TruncatedBridges.lean](TruncatedBridges.lean) were independently checked in Lean. [Verification](Verification.json)
