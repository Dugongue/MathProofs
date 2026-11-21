# Four extensions of the fixed-Hessian construction

The starting construction gives a common determinant-one normal form for all invertible slices of a tensor family. The results below use actual matrix and algebra structure on this chart to compare spectral data, singular schemes, ranks, and isomorphisms in hidden bases. [Starting proof](https://github.com/Dugongue/MathProofs/blob/main/SymmetricFinalFour/Tensor.md)

| Result | Scope |
| --- | --- |
| [Identical pointwise slice similarity](Tensor.md) | Tensor isomorphism remains complete when all outputs have the same operator similarity class at every matched parameter, including singular slices. One can also prescribe how many marked directions any common simultaneous similarity must handle. The symmetric Frobenius version gives simultaneous metric congruence on these marked subpencils. |
| [The local algebra of the singular scheme recovers TI](Geometry.md) | In characteristic other than two, the abstract projective square-zero scheme determines the input isomorphism class. Its local ring at the unique point of maximal tangent dimension, modulo the cube of its maximal ideal, already suffices. In characteristic other than two and three it is the singular scheme of the cubic. |
| [Quadratic rank intervals at fixed Hessian](RankIntervals.md) | In a single affine family with common unit-slice normal forms, ordinary and symmetric rank and border rank each attain consecutive intervals of quadratic width. Exact ordinary tensor ranks also have such intervals inside a single final-digit class over each fixed finite local ring of residue characteristic other than two and three. |
| [Recovering the hidden field tensor in polynomial time](Algorithms.md) | Over finite fields and explicit prime-power rings the promised decoder recovers the ordered support quotients in arbitrary independent bases. At odd residue characteristic it recognizes the entire orbit saturation. The remaining isomorphism search depends on the extracted support sizes. |

The four results have written proofs and finite controls. [WeightedCube.lean](WeightedCube.lean) checks the weighted-cube expansion used by the low-border-rank degeneration. The notes credit the closest earlier results and scope the additional claims. Publication priority for the exact extensions remains open. Prepared for MathProofs with AI assistance.
