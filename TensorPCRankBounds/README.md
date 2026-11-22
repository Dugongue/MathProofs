# Polynomial Calculus degree bounds for structured tensor isomorphism

These proofs address [Question 7.1 of Galesi, Grochow, Pitassi, and She](https://arxiv.org/abs/2305.19320). They use the literal cubic three-tensor action equations and quadratic two-sided inverse equations, with no field equations. The comparisons are geometrically negative, meaning that the tensors are nonisomorphic over an algebraic closure. The algebraically closed working field is used for constant bases and decompositions. Finite coefficient descent preserves the degree bound over the original field.

| Source structure | Ordinary Polynomial Calculus degree |
| --- | --- |
| [Thin associative multiplication](ThinAlgebras.md), including incidence algebras and graph radical-square-zero algebras | $O(b+1)$ in geometric border rank $b$ of the pair. Worst-case linear degree in every fixed characteristic, including zero. |
| [Associative multiplication with thin basic corners](MoritaThin.md), with arbitrary matrix sizes in the semisimple quotient | $O((b+1)^4)$ in every characteristic, improving to $O((b+1)^2)$ in characteristic zero or characteristic larger than the supported side. |
| [Determinantal frames](DeterminantalFrames.md) | $O(b+1)$ from two intrinsic diagonal mode algebras, including unequal-side examples. One intrinsic frame and an invertible slice whose ratios generate the full matrix algebra give $O((b+1)^2\log(b+2))$. |
| [Lovitz–Petrov decompositions](LovitzPetrov.md) | $O((r+1)^3)$ in ordinary rank or geometric border rank $r$, under the subset dimension condition. The proof certifies the alternating pencil recovery against an arbitrary target. |
| [Kruskal and rank-one slice frames](KruskalFrames.md) | $O(r^2)$ under the classical Kruskal inequality for a rank-$r$ decomposition. Independent rank-one slices with the stated minor-space condition give $O(r+1)$. |
| [Arbitrary tensor direct sums](DirectSums.md) | $\max\{D+2,O(n+1)\}$ in supported side $n$, where $D$ is the maximum degree for geometrically negative equal-format indecomposable component pairs. The $O(n+1)$ term is constant in characteristic zero or characteristic larger than $n$. |
| [All matrix pencils](MatrixPencils.md), including rectangular and singular pencils and repeated eigenvalues | $O(b+1)$ in geometric border rank of the pair. Worst-case linear degree in each fixed positive characteristic, even at equal full support dimensions. |

The upper bounds also hold in ordinary rank when expressed in border rank. Except for the pencil and direct-sum statements, the structure assumptions apply to one tensor and the target is arbitrary. The proofs have no Dirichlet GRH hypothesis.

The Laurent-binomial arguments use the Steinitz rearrangement lemma to keep intermediate degrees bounded even when a lattice relation has large integer coefficients. The direct-sum and pencil proofs instead extract small inverse problems from intrinsic endomorphism algebras.

The degree bounds are written proofs. [Lean 4.33.0 checked the multiplicativity of the unital isotope correction](Isotope.lean), using the axiom `propext`. Publication priority is provisional. These cases extend the [earlier bounds for sums of matrix multiplication tensors](https://github.com/Dugongue/MathProofs/blob/fa1001c4a32d65711c2864f4bdfa1257a44e333b/DeterminantalTensorCrossovers/SemisimpleAdjointPC.md). The unrestricted polynomial degree question remains open.
