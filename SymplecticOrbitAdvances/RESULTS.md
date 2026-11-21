# Four extensions of the symplectic tensor orbit-closure threshold

The starting point is the sharp threshold for a single ordered tensor under independent symplectic changes of basis. Throughout, orbit closure means Zariski closure. The complexity theorems use complex orbits and exact rational or Gaussian-rational encodings.

| Result | Theorem |
|---|---|
| [Fixed tensor tuple formats](tuple-threshold.md) | For any fixed tensor tuple signature for a product of symplectic groups, a slot of order at least three gives TOCI-completeness. If every slot has order at most two, orbit-closure intersection is in deterministic polynomial time. Group labels may repeat within a slot and occur across slots. |
| [One symmetric cubic or one alternating three-form](single-cubic.md) | Under a single complex symplectic group, both orbit-closure intersection problems are TOCI-complete by explicit affine reductions. |
| [Exponential separating degree](separator-degree.md) | Explicit closed-orbit pairs of single symmetric cubics and alternating three-forms agree on every invariant below degree \(4(2^m-1)/\gcd(7,2^m-1)\). The same examples work under three independent symplectic actions in the ambient ordered tensor space. |
| [Normality and rational singularities](singularities.md) | Hyperbolic padding preserves and reflects normality and rational singularities of ordinary tensor orbit closures in characteristic zero, including points where mode supports shrink. Its projective incidence model has structure-sheaf pushforward equal to the structure sheaf and vanishing higher direct images. |

The four theorems have written proofs. The [Lean source](SymplecticOrbitAdvances.lean) and [audit](Verification.json) cover the spectral separation, cyclic weights, and degree-counting lemmas.
