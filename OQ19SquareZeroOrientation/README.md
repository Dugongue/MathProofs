# Ternary square-zero orientation

The unrestricted same-field reduction in Open Question 1.9 remains open. This packet gives four written results on the square-zero normal form over \(\mathbb F_3\). Each same-field reduction below uses one ordinary three-tensor isomorphism comparison on the stated class. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

| Proof | Exact scope |
|---|---|
| [Balanced carriers](BalancedCarriers.md) | Align involutory complements by actual isometries, then read the label sign from thin kernels or small grades. Neutral carriers admit unrestricted permutations of repeated factors. A recognizable scaling criterion also removes the label constraint for some arbitrary-defect overlap arrangements. The construction combines with the overlap and centroid lines on the same transporter. |
| [Full-star and support stripping](StarStripping.md) | Transfer the character through arbitrarily many intrinsic layers. An odd free exponent removes the sign restriction for every transporter of an arbitrary terminal core. |
| [Simple adjoint](SimpleAdjoint.md) | Transfer the exact sign to a smaller multiplicity-space problem. Small defects give one ordinary TI comparison. Multiplicity three admits a deterministic polynomial-time algorithm with arbitrary additive defects. |
| [Overlap trees](OverlapTrees.md) | Read the sign from the incidence exact sequence of a recognizable tree of local labels, including the sign of central-edge reversal. Local label dimensions can be large when the local lines are available. |

The examples include cyclic overlaps of repeated noncommutative factors, scalar adjoints with arbitrarily deep stripping, and genuine sign constraints with quadratic label dimension and codimension. The [square-zero normal form](SquareZeroNormalForm.md) explains how the original combined character reaches the descended label determinant. The four written arguments reuse the [tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4) and keep all determinant records tied to the same congruence.

Lean independently replayed four supporting algebraic identities, with the source hash and transitive axioms recorded in the audit. The proof of the polynomial-time reductions remains written mathematics. [Lean source](SquareZeroIdentities.lean) · [Audit](SquareZeroIdentitiesAudit.json)
