# Four extensions of determinant-constrained tensor isomorphism over coefficient rings

| Result | Scope |
|---|---|
| [Unbounded-depth coefficient rings by a mixed-characteristic lift](graded-ghosts.md) | One ordinary free-module TI instance tests every principal determinant on positively graded algebras with an explicit free graded lift. The target precision grows by at most the logarithm of the largest grade. This includes full special-linear TI over binary truncated polynomial algebras of arbitrary length. |
| [Unbounded-depth comparison over the original field](higher-jets.md) | Higher-order scaling gives one ordinary TI instance over the coefficient field when every nonconstant grade has a coordinate of bounded \(p\)-divisibility. Radical length may grow without bound, and the compiler detects principal units missed by all ordinary derivations. A free graded mixed-characteristic variant keeps the original base precision. |
| [All joint determinants for ordered matrix systems](ordered-profiles.md) | For any explicitly presented finite local ring with fixed residue characteristic and arbitrary residue degree, compute the entire joint determinant coset of transporters of a labelled quiver representation on free modules. Count transporters with any prescribed determinant tuple in polynomial time. |
| [Full three-mode lifting under a residue \(p\)-group promise](residue-p-groups.md) | Given a coset of a supplied residue \(p\)-subgroup, find and count all lifts that transport the original tensor and satisfy exact prescribed ring determinants. The algorithm is polynomial in bit length, uniformly in the prime and radical depth. |

The four theorems have written proofs. The [Lean source](CoefficientRingAdvances.lean) and [audit](Verification.json) cover prime-power precision amplification, Frobenius scaling, and the additive displacement used for residue \(p\)-groups.
