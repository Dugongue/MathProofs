# Which of the twenty TI interval problems collapse?

Fix $\mathbb F_3$, use the same twenty definitions as in the preceding interval packet, and distinguish deterministic polynomial-time many-one reductions from polynomial-time Turing reductions. The numbers refer to those definitions, rather than to changed promises. The new proofs give these many-one equivalences.

| Group | Equivalent problems | What the group tests |
| --- | --- | --- |
| TI | Ordinary TI | No determinant equations. |
| $A$ | **1, 2, 3, 10, 15, 18** | One determinant character. |
| $B$ | **4, 5, 6, 16** | Two independent determinant characters on one common transporter. |
| SL-TI | **7, 8, 9, 11, 12, 13, 14, 17, 20**, and unrestricted SL-TI | All three determinant equations. |
| $Q$ | **19** | Quadratic-extension semilinear norm TI. |

The directed comparisons proved among these groups are
$$
       \mathrm{TI}\le_m^p A\le_m^p B\le_m^p\mathrm{SL\!-\!TI},
       \qquad
       \mathrm{TI}\le_m^p Q\le_m^p\mathrm{SL\!-\!TI}.
$$
Each group is a proved equivalence class among the listed problems. The diagram has at most five many-one degrees. It leaves equality between different rows unresolved. In particular $Q$ has no further unconditional comparison established here with either $A$ or $B$. [All 22-by-22 comparisons](Pairwise.md)

## Why the collapses hold

* [Castling and independent sign queries](CastlingAndConjunction.md) gives a short exact equivalence of 1–3. Calibrated annihilator bases transform their determinant characters, and padding adjusts the relevant dimensions while preserving the tested character.
* [Structural comparison](StructuralComparison.md) realizes every invertible linear change of the three sign bits inside the recognizable square-root max-rank family. Its aligned alternating matrix spaces and marked stars carry the individual signs. A mixed symmetric–alternating version forces scalar centroid. This proves the collapse of 4–6, the square-root equivalences to unrestricted SL-TI, and the one-character equivalence for 10. [Independent two-character proof](SignComparison.md)
* [Scalar-centroid embedding](ScalarCentroidGlue.md) gives a shorter independent route for 7, 8, 9, 13 and 14. The attached regular Jordan pencil and its evaluation factors are determinant-neutral. On equal-format pairs, even side lengths make a block exchange neutral and allow the two cross maps to compose. This covers equal formats even when the attached block happens to be isomorphic to the other summand.
* [Cubic norm encoding](CubicNormEncoding.md) implements a characteristic-three Frobenius lock on two truncated symmetric algebras. Rectangular blocks read the branch determinants, and the regular block reads the total. The exact output norm-sign triple is $(d_Ud_Vd_W,d_V,d_U)$. This gives all five cubic or mixed-field comparisons. [Independent norm comparisons and quadratic parity analysis](NormComparison.md)

## Turing closure and the unresolved many-one comparisons

Under polynomial-time Turing reductions, $A$, $B$, and SL-TI all collapse. This places twenty of the twenty-two listed problems in one Turing degree. Indeed a nonempty sign set is an affine coset of $\mathbb F_2^3$, and membership of zero is the conjunction of the seven hyperplane tests. Each of those is now many-one equivalent to $A$. Ordinary TI and the quadratic class may also coincide with this degree or each other.

There is a stronger way to state the remaining problem between the sign tiers. Let $A^{\wedge k}$ ask that all $k$ independently encoded $A$-instances answer yes. The reductions give
$$
 A^{\wedge2}\le_m^p B\le_m^p A^{\wedge3},\qquad
 A^{\wedge3}\le_m^p\mathrm{SL\!-\!TI}\le_m^p A^{\wedge7}.
$$
The lower bound for $B$ packs two independent sign tests into two distinct axes of a transporter determinant triple. The upper bound uses the three planes containing its allowed line. If $A\equiv_m^p B$, then $A^{\wedge2}\le_m^p A$; iterating that reduction handles every fixed conjunction and gives $A\equiv_m^p\mathrm{SL\!-\!TI}$. Conversely an equality of the outside tiers implies equality of the inside tiers. Thus $A$ and $B$ can collapse only together with SL-TI. This does not establish either outcome. The comparison with ordinary TI still includes [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

The odd-degree norm construction does not transfer unchanged to candidate 19, since both $1$ and $-1$ in the base field have quadratic norm $1$. This is a limitation of that construction and leaves the mathematical comparison open.

These proofs are informal. Exact finite controls enumerated all 168 invertible sign transformations, 512 castling checks on sign cosets, and 128 cubic branch determinant-parity checks. Publication priority, human review, and strictness remain unresolved.
