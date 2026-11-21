# Sharp recovery from fractional graph transporters

## GP-0921

Suppose $A,B$ are adjacency matrices of simple graphs of the same order and $X$ is a rational doubly stochastic matrix satisfying $AX=XB$. If every row of $X$ has an entry strictly greater than $1/2$, rounding these entries gives an isomorphism. The same result holds when at most one row has no such entry. The threshold $1/2$ is optimal uniformly. This is a polynomial-time recovery criterion and does not require uniqueness.

If a computable graph-isomorphism relaxation contains the permutation matrix of every genuine isomorphism and has a unique feasible matrix, there is also an exact uniqueness criterion. Its sole matrix represents an isomorphism if and only if it is a permutation matrix and preserves adjacency. Indeed the presence of an actual isomorphism forces its matrix to be that unique feasible point. In the fractional relaxation the adjacency condition is already part of feasibility.

### Recovery and threshold

A row of $X$ has at most one entry greater than $1/2$, and by the column-sum condition two rows cannot place such entries in the same column. Let $\pi(i)$ be the indicated matching. If $A_{ij}=1$ and $B_{\pi(i)\pi(j)}=0$ for two matched rows, then
$$
(AX)_{i,\pi(j)}\ \ge X_{j,\pi(j)}>\tfrac12,\qquad
(XB)_{i,\pi(j)}\ \le 1-X_{i,\pi(i)}<\tfrac12,
$$
a contradiction. If $A_{ij}=0$ and $B_{\pi(i)\pi(j)}=1$, the inequalities reverse and give the same contradiction. Thus the match preserves all adjacencies among matched rows.

If one row is unmatched, match it to the unique unused column. To check its incidences, note that any positive entry $X_{i,a}$ links equal degrees. With degree vectors $d_A,d_B$, the intertwining and stochasticity give $d_A=Xd_B$ and $d_B=X^{\mathsf T}d_A$. Consequently
$$
\sum_{i,a}X_{ia}\bigl(d_A(i)-d_B(a)\bigr)^2
=\|d_A\|^2+\|d_B\|^2-2d_A^{\mathsf T}Xd_B=0.
$$
All matched rows therefore have the same degree as their images. Since their internal incidences already agree, their incidence with the one remaining vertex is the same on each side. This proves the extension. Checking the exact rational equations and executing the rounding take polynomial time.

For sharpness, for each $m\ge3$ take $C_{2m}$ and $C_m\sqcup C_m$. Both admit a partition into $m$ two-element fibers over $C_m$ such that every pair of neighboring fibers is joined by a perfect matching, with no other edges. The first is the connected two-lift and the second the disconnected two-lift. The matrix with one $J_2/2$ block on each matching fiber pair and zero elsewhere commutes across their adjacency matrices. Indeed the adjacency block between neighboring fibers is a permutation matrix on each side, and left or right multiplication by a $2\times2$ permutation fixes $J_2/2$. This supplies two nonisomorphic graphs having a fractional transporter with row maxima exactly $1/2$. Any bound using a smaller uniform maximum threshold would accept this transporter.

The result concerns the ordinary doubly stochastic intertwiner. Any stronger relaxation whose vertex projection remains such an intertwiner inherits the sufficient condition. It complements exact transporter recovery on structured algebraic inputs by giving a single-matrix numerical certificate with a sharp uniform cutoff. [Algebraic graph-isomorphism relaxations](https://arxiv.org/abs/1502.05912) · [Graph transporter proofs in the earlier catalogue](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GrochowCatalogueProofsII/GraphRecoveryLemmas.lean)
