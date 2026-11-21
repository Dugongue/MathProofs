# Four extensions of the cubic multiplication-tensor construction

| Proposed placement | Proof | Result |
|---|---|---|
| 2–6 | [Formal cubics in characteristic three](Complexity.md) | Decide equivalence, recover a witness, and count all transporters over $\mathbb F_{3^k}$ in time $q^{\widetilde O(c^{3/2})}\operatorname{poly}(n,\log q)$, with $c$ the polarization contraction rank. |
| 3–7 | [Integral orientation](Orientation.md) | For every fixed degree, encode an integral form so that each leg of every tensor transporter records exactly the determinant of a recovered form transporter. Cubics need at most $3n+19$ entries per side. |
| 4–8 | [Singularities of cubic degenerations](Geometry.md) | Recover the reduced local orbit-closure singularity at every nonzero encoded endpoint, up to a smooth factor. Compute the extra nonsplit boundary at zero. The ordinary tensor statement holds in characteristic different from two or when the algebra dimension is invertible. |
| 6–10 | [Affine polynomial equivalence](AffineJets.md) | Recover the affine chart from an unmarked multiplication tensor over arbitrary commutative rings. Over algebraically closed fields, the construction preserves and reflects directional affine degeneration of single polynomials. |

The placement ranges are editorial estimates for the project’s Grochow research list. The four arguments are written proofs and publication priority remains unverified. The accompanying Python programs check finite instances. Lean independently verified the auxiliary constant-term identity in [MixedConstants.lean](MixedConstants.lean).
