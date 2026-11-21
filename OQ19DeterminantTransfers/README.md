# Four determinant reductions for Open Question 1.9

The unrestricted single-instance reduction from special-linear tensor isomorphism to ordinary tensor isomorphism remains open. The four proofs below give exact reductions or algorithms at the stated scopes. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

| Result | What the proof establishes |
| --- | --- |
| [Centroid-local hard core and determinant counts](CentroidCosets.md) | Over any fixed finite field, arbitrary determinant-vector tests admit a polynomial-time Turing reduction to concise tensors with local centroid. A direct algorithm counts all determinant fibers in polynomial time when each intrinsic summand has a mode of dimension \(O(\sqrt{\log L})\), even with arbitrarily many repeated summands and no globally small mode. |
| [Square-zero pencils](SquareZeroGrades.md) | A binary linear system selects either a small radical grade or its small complement for each intrinsic adjoint grade. If large ambient determinant powers cancel, this gives one ordinary TI instance. Explicit examples with quadratic radical dimension and codimension need only two-dimensional orientation data. |
| [Maximal subfields of pair adjoints](MaximalSubfieldDescent.md) | Determinant-neutral adjoint units move large matrix factors into maximal subfields, and norm lines and the third-mode flag read all three determinants in one ordinary TI instance. The class allows nonzero adjoint radicals and arbitrary matrix and extension degrees. In \(\mathbb F_3\), even-degree matrix factors need no multiplicity bound. |
| [Intrinsic orientation trees](OrientationTrees.md) | Signed multiplication of local volume lines propagates determinants through unordered binary trees. It gives one ordinary TI instance on the stated raw action tensors, even with repeated symmetric branches and unbounded radical length. |

The arguments use the existing [ternary square-zero normal form](https://github.com/Dugongue/MathProofs) as a formulation of the endpoint. The new square-zero theorem applies to the stated intrinsic flag test. The other three results use different structure and keep determinant conditions on a common transporter.

The four main arguments are written proofs. Lean independently replayed five supporting lemmas covering character cosets, determinant-neutral correction, neutral powers, the parity of block exchanges, and the determinant of a triangular support extension. The exact finite enumeration checks the block-swap effect and three ordered matrix tuples. [Lean companion](DeterminantTransfers.lean) · [Axiom audit](DeterminantTransfersAudit.json) · [Finite checks](check_centroid.py)
