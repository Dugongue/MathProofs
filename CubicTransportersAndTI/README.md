# Cubic transporters and special-linear tensor isomorphism

These results address the same-field ordinary comparison in [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

- [Exact cubic orientation](ExactCubicOrientation.md). An \(11n\)-variable cubic for any based \(n\)-dimensional unital associative algebra. It recovers all transporters over commutative rings, gives the exact residual determinant equation, and preserves ternary signs in the unrestricted cube-zero normal form.
- [Frobenius determinant lines](FrobeniusDeterminantLines.md). Pair an intrinsic square-zero ideal with its complementary quotient and record the determinant on the small unpaired space. This gives one ordinary TI instance, including for prescribed determinants of the corresponding cubics.
- [Centroid determinant descent](CentroidDeterminantDescent.md). Read the determinant through small relation kernels or odd-length module strata in symmetric or alternating ternary square-zero comparisons. The primitive-factor assembly allows repeated components of unbounded multiplicity.
- [Adjoint determinant corrections](AdjointDeterminantCorrections.md). Recognize modes whose determinants can be corrected by units of paired adjoint algebras, and construct a TI-complete local-centroid class with all three corrections.

The main theorems are written proofs. The unrestricted forward reduction in Open Question 1.9 remains open. Four supporting lemmas passed independent Lean kernel and axiom checks. Direct arithmetic controls cover three characteristics over nonreduced dual-number bases. [Lean source](ExactCubicOrientation.lean) [Audit](ExactCubicOrientationAudit.json) [Arithmetic controls](CubicRingControls.py)
