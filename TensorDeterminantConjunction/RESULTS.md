# Ordinary conjunctions in the determinant tensor-isomorphism degrees

All tensors are explicit and over the fixed field $\mathbb F_3$. Write $O$, $A$, $B$, and $S$ for ordinary, one-sign, two-sign, and special-linear three-tensor isomorphism. The last three require determinant one in the first mode, the first two modes, and all three modes, respectively. All unqualified reductions are deterministic polynomial-time many-one reductions. These proofs are informal.

## A common closure theorem for all thirty comparisons

For every candidate $X$ in the thirty-comparison catalogue, let $X\land O^{\wedge *}$ ask for the original verdict together with every answer in an explicit, polynomial-length list of ordinary TI comparisons. Then

$$
 X\land O^{\wedge *}\equiv_m^p X.
$$

This holds for comparisons constructed jointly from the input as long as they are written down in polynomial time. There is one output instance of $X$. The reverse just selects an empty list or a fixed ordinary yes instance.

| Catalogue entries | Forward construction |
| --- | --- |
| L1–L4, L6, L8–L10 | L1–L4 are equivalent to $A$ and the other four to $O$. Use determinant-neutral tagged blocks or ordinary conjunction packing, respectively. |
| L5 and L7 | These share one degree $C_{\mathrm F}$. Attach the ordinary comparison by a connected sum with a graded Gorenstein carrier, choosing its socle degree and grade dimensions so its contribution to the determinant is identically one. |
| M1, M2, M6–M10 | Apply neutral conjunction to the $A$ or $B$ comparison, or to one arm of the independent conjunction $A\land A$, using the established equivalences. |
| M3–M5 | Attach ordinary conditions to chosen arms of a common-source star for M3. For M4 and M5 attach them to the independent $A$ comparison in their equivalent presentation $A\land F$, where $F$ tests for an odd first-mode automorphism. |
| U1, U3–U10 | Add each ordinary comparison with zero sign projection in one balance slot. It contributes only a yes prerequisite, leaving the slot profile unchanged when it holds. |
| U2 | Attach with zero sign projection to the input comparison. When the resulting profile is nonempty, its direction is the relevant source stabilizer sign subgroup and it equals the old direction. When the attached comparison fails, the profile is empty. |

The use of distinct tags and a common polynomial size bound gives polynomial output for entire lists. The [prior lower equivalences](PriorLower.md), [middle equivalences](PriorMiddle.md), and [neutral-block construction](NeutralConjunction.md) supply the reductions used in the table. The new [Frobenius conjunction proof](FrobeniusConjunction.md) explains why arbitrary output isomorphisms preserve the original determinant despite possible mixing between the two algebra factors. [Connected sums of Gorenstein local rings](https://arxiv.org/abs/1005.1304)

## Further comparisons

- **A new ordinary-TI reduction for a Frobenius subfamily.** If the associated graded algebra recovered from an active L5 input is a complete intersection, its determinant reduces to determinant characters on the tangent space and first Koszul homology. Their combined dimension is at most twice the logarithm of the algebra dimension. One ordinary TI instance checks the result. Recognition is polynomial time and the given multiplication table can be ungraded. [Proof](Lower.md)
- **The corrected-sign problem U2 needs at most two two-sign tests.** There are reductions $U2\le_m^p B^{\wedge 2}$ and $U2\le_m^p A^{\wedge 5}$. The five-test bound is sharp for conjunctions of fixed affine one-sign probes under the stated model. The reverse direction from $S$ uses three U2 tests, also sharp in the specified affine model. [Proof](Upper.md)
- **A shared-source comparison with its own odd-automorphism gate.** The gated one-arm problem and the gated two-arm star both have degree $O\land F$. The reduction uses the same source and the same tested mode for the gate and the actual comparison. [Proof](Middle.md)

These results identify the degree of each original candidate with its ordinary-conjunction variant, and give the additional restricted and multiple-query reductions above. The general reverse comparisons in $O\le_m^p A\le_m^p B\le_m^p S$ remain unresolved. The constructions here establish no new equivalence between two distinct original catalogue rows. [Chen, Grochow, Qiao, Tang and Zhang, open questions](https://arxiv.org/html/2306.03135v2#S1.SS5)
