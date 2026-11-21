# Four consequences of the characteristic-three pure-cube fiber

[Priority audit](Priority.md) compares the original worst-case algorithm against the published TI reductions, the average-case characteristic-three result, and the analogous recovery of group power data.

| Proposed placement | Result |
|---|---|
| 2–6 | [Cubic orbit closures and stabilizer schemes](Geometry.md). Nonzero restriction to the polarization radical gives a global affine-space product over the polarization orbit closure. The zero case has a projective Grassmannian incidence model. |
| 3–7 | [One tensor instance over any commutative ring](Tensor.md). Formal cubic equivalence reduces to ordinary three-tensor isomorphism with side lengths $O(n^2)$. The reduction also handles nilpotents and imperfect fields. |
| 4–8 | [Ordered cubic systems](Systems.md). Exact decision, search and counting use single-coordinate orbits of size at most $q^c$, even when an example has $q^{\Omega(c^2)}$ joint states. Query width depends on three intrinsic ranks. |
| 6–10 | [Exact affine and marked cubic transporters](Affine.md). The original $q^{\widetilde O(c^{3/2})}$ exponent extends to exact affine substitution and arbitrary labelled linear marks, including exact lift counts. |

The placements are editorial estimates. The four arguments are written proofs with finite controls and a separately kernel-checked auxiliary identity in [MarkedCube.lean](MarkedCube.lean). The literature review leaves publication priority open.
