# Binary positive semidefinite completion at rank two

**Theorem.** Given a partial real symmetric matrix with all specified entries in {0,1}, deciding whether it has a positive semidefinite completion of rank at most two is complete for the existential theory of the reals. Hardness holds when every diagonal entry is unspecified and the specified positions lie only between two disjoint sets of indices. Each unspecified entry is independent, apart from the required matrix symmetry.

This is an informal corollary of the [ordinary rank-two completion theorem](RankTwoCompletion.md). The exact restrictions are part of the result: prior hardness for general rank-constrained positive semidefinite optimization is not claimed as new.

## Reduction and proof

Take a partial m by n matrix M from the ordinary completion theorem. On m+n indices make the symmetric partial matrix

\[
G=\begin{pmatrix} * & M\\ M^{\mathsf T}&*\end{pmatrix},
\]

where both diagonal square blocks are entirely unspecified. A specified entry of M fixes the two transposed positions of G to the same value. Thus the observed positions form a bipartite graph, all diagonals are free, and all specified numbers remain 0 or 1.

If M has a real completion of rank at most two, write it as UV, with U an m by 2 matrix and V a 2 by n matrix, padding a smaller factorization with zeros if necessary. Stack U and V transpose into an (m+n) by 2 matrix B. Then BB transpose is positive semidefinite of rank at most two, and its upper-right block is UV. It is the required completion of G.

Conversely, a real positive semidefinite matrix G of rank at most two has a real Gram factorization BB transpose with two columns. Splitting its rows into the two prescribed index sets shows that the cross block has rank at most two and completes M. The original reduction's specified identity cross block forces rank at least two, so all accepting instances actually have rank two.

The reduction is polynomial. Membership in the existential theory of the reals follows by quantifying two coordinates for each Gram vector and imposing their specified pairwise inner products. This proves both directions and the completeness claim.

## Symmetric completion without a positivity promise

For ordinary symmetric rank-at-most-two completion, add a disjoint fully specified two by two identity principal block, leaving all its cross entries unspecified. Any real symmetric completion of rank at most two then has at least two positive eigenvalues and no other nonzero eigenvalues, hence is positive semidefinite. Conversely, choose two orthonormal anchor vectors in the same two-dimensional Gram space. The same construction proves existential-real completeness of ordinary symmetric binary completion with rank cap two.

## Why the diagonal restriction matters

If instead all diagonals are fixed to one and all specified off-diagonal entries are 0 or 1, the positive semidefinite rank-two problem is polynomial-time decidable. Merge vertices joined by specified ones, since unit vectors with inner product one coincide. A specified zero within a merged class makes the instance infeasible. On the remaining classes, prescribed zeros demand orthogonality. Their graph must be bipartite: following orthogonality along a path in a real plane alternates between a line and its perpendicular, and an odd cycle is impossible. Bipartiteness is sufficient by assigning the two standard unit vectors to the two classes of each component. This also covers isolated vertices and the rank-at-most-one possibilities.

Our hardness result allows unknown vector lengths through free diagonal entries; it does not assert hardness of this fully unit-diagonal binary case.

## Attribution and status

The existential-real hardness comes from the accompanying new rank-two completion construction. The Gram-factorization passage is standard linear algebra. Rank-constrained positive semidefinite optimization already has hardness results, as recorded in [Compendium A23](https://arxiv.org/abs/2407.18006); [Laurent and Varvitsiotis](https://arxiv.org/abs/1203.6602) study rank-constrained positive semidefinite completion. The claim here is the exact binary, bipartite-observation, free-diagonal restriction. No comprehensive publication-priority certification or Lean verification is claimed.
