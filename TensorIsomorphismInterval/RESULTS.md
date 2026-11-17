# Twenty candidate classes between TI and SL-TI

Fix $\mathbb F_3$. Each name below denotes the deterministic polynomial-time many-one downward closure of the indicated complete decision problem. All complete problems take ordinary explicit dense data. A restricted language rejects an input outside its designated, polynomial-time recognizable family. The endpoints are ordinary 3-tensor isomorphism and 3-tensor isomorphism with determinant one in each mode. For all twenty candidates we prove both inclusions
$$
  \mathsf{TI}\ \subseteq\ \mathcal C\ \subseteq\ \mathsf{TI}_{\mathrm{SL}} .
$$
The names denote twenty proposed definitions. The proofs do not give twenty pairwise distinct complexity classes or strictness at either endpoint. The same many-one reductions also imply the inclusions for polynomial-time Turing closures.

## Six constrained determinant problems

Here $d_i\in\{1,-1\}$ denotes the determinant of one common ordinary transporter in mode $i$. Each complete problem searches for such a transporter obeying its indicated condition.

| # | Proposed class | Condition |
| --- | --- | --- |
| 1 | One-mode orientation TI | $d_1=1$. |
| 2 | Two-mode product orientation TI | $d_1d_2=1$. |
| 3 | Total orientation TI | $d_1d_2d_3=1$. |
| 4 | Two fixed orientations TI | $d_2=d_3=1$. |
| 5 | Anchored paired orientation TI | $d_1=d_2$ and $d_3=1$. |
| 6 | Common orientation TI | $d_1=d_2=d_3$. |

These are the six proper sign-subgroup types up to mode permutation. The padding theorem realizes every sign subgroup $H\le\mathbb F_2^3$ and gives $P_K\le_m^p P_H$ whenever $H\subseteq K$. Its auxiliary blocks do not mix with the data blocks. This produces an exact partial order of certified reductions, with possible identifications. [Determinant proof](DeterminantGroups.md)

## Eight restrictions to recognizable concise tensors

Each complete problem asks for full determinant-one isomorphism on the specified family. The maximum matrix-contraction rank in one direction is called max-rank here. A geometric condition is taken over the algebraic closure.

| # | Proposed class | Input family |
| --- | --- | --- |
| 7 | Balanced concise SL-TI | All three sides have the same length. |
| 8 | Absolutely indecomposable SL-TI | The tensor has one geometric direct summand. |
| 9 | Scalar-centroid SL-TI | The geometric centroid consists of common scalar triples. |
| 10 | Scalar-adjoint low-max-rank SL-TI | Recognizable alternating suspensions with scalar fixed-label pair adjoints in all three views and square-pencil max-rank $O(\sqrt n)$. |
| 11 | All-mode square-root SL-TI | Recognizable alternating-arm tensors at geometric $O(\sqrt n)$ max-rank in all three modes. |
| 12 | Scalar-centroid square-root SL-TI | The recognizable mixed alternating/symmetric arm family at the same max-rank scale, with scalar geometric centroid. |
| 13 | Unequal-format two-summand SL-TI | Exactly two geometric indecomposable summands with different ordered formats. |
| 14 | Equal-format two-summand SL-TI | Exactly two geometric indecomposable summands with identical ordered formats. |

The lower reductions here produce concise inputs with actual determinant-one witnesses on every ordinary yes pair. They use the internal cross-factor determinant or the addition of a common radical direction to the underlying alternating matrix space. The exact raw recognition tests are part of the proofs. Candidate 12 uses odd characteristic. [Structural proof](Structural.md)

## Six extension-field norm problems

These classes still use $\mathrm{TI}_{\mathbb F_3}$ and $\mathrm{SL\text{-}TI}_{\mathbb F_3}$ as endpoints. An input block over $\mathbb F_{3^r}$ is concise with local centroid of residue $\mathbb F_{3^r}$. Allow a common Frobenius exponent $k$ in its three modes. For a semilinear map $g_i=A_i\sigma^k$, set $d_i=\det_{\mathbb F_3}g_i$. In extension coordinates this is $(-1)^{(r-1)kn_i}N(\det_{\mathbb F_{3^r}}A_i)$.

| # | Proposed class | Constraint |
| --- | --- | --- |
| 15 | Cubic-extension one-mode norm TI | $r=3$ and $d_1=1$. |
| 16 | Cubic-extension two-mode norm TI | $r=3$ and $d_1=d_2=1$. |
| 17 | Cubic-extension three-mode norm TI | $r=3$ and $d_1=d_2=d_3=1$. |
| 18 | Cubic-extension product norm TI | $r=3$ and $d_1d_2d_3=1$. |
| 19 | Quadratic-extension norm TI | $r=2$ and $d_1=d_2=d_3=1$, including the quadratic Frobenius signs. |
| 20 | Mixed quadratic–cubic block norm TI | Both field degrees occur in a block list. Allow compatible permutations and independent within-block Frobenius choices. Each full base-field determinant, including its block-permutation sign, is one. |

Trace to the base field preserves the exact transporter action and the norm constraints. The lower reductions first pin base-field witnesses by cubic powers and then compile to scalar-centroid suspensions with determinant-one witnesses. [Norm proof](TraceNorms.md)

## Consequence for the endpoint question

The first three candidates are enough for the endpoint comparison over $\mathbb F_3$. A nonempty transporter determinant set is an affine subspace of $\mathbb F_2^3$. It contains zero precisely when every hyperplane through zero intersects it. Testing the seven hyperplanes gives a constant conjunction, with only three types up to permuting modes. If candidates 1, 2 and 3 all reduce to ordinary TI by many-one reductions, their conjunction combines into one ordinary TI instance by the fixed-signature compiler, giving $\mathrm{SL\text{-}TI}\le_m^p\mathrm{TI}$. The endpoint comparison is the question posed by Chen, Grochow, Qiao, Tang and Zhang. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

The supplementary determinant proof gives explicit square-format balancing and additional subgroup families over other fields. Over $\mathbb F_4$ it certifies 22 further subgroup descriptions beyond the two endpoints, with some descriptions related by mode permutation. This supplement is separate from the twenty-base-field table above. [Square-format and other-field proof](Characters.md)

These are informal proofs. Exact controls checked 8,448 subgroup padding formulas, 2,048 character-conjunction formulas, and all 94 one-field-line norm and Frobenius combinations over $\mathbb F_9$ and $\mathbb F_{27}$. The claims are about interval containment. Publication priority and strictness remain unverified.
