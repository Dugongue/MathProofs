# Uniform sparsity lifting to every ROABP order

## GP-0611

For every field and every nonzero $n$-variable polynomial $f$ of sparsity $s$, one explicit monomial substitution into $2n$ variables makes every variable order of a read-once oblivious algebraic branching program for the image require width at least $s$ at its middle layer. The substitution depends only on $n$. It uses exponents $O(n)$ in its individual substitution monomials and multiplies the total degree by $O(n^2)$. It can be constructed in deterministic polynomial time. A sparse input list remains a sparse list with the same number of terms, and a circuit description incurs only polynomial overhead.

Let $p$ be a prime between $2n$ and $4n$ and choose $2n$ distinct residues $t_j$ modulo $p$. Let $A_{ij}$ be the least nonnegative integer representing $t_j^{i-1}$ modulo $p$, for $1\le i\le n$. Set
$$
x_i\longmapsto\prod_{j=1}^{2n}z_j^{A_{ij}}.
$$
Every $n$ columns of $A$ have a nonzero Vandermonde determinant modulo $p$, so the corresponding integer submatrix is nonsingular over the rationals. This argument is about **exponents**. The coefficient field of $f$ may have any characteristic, including $p$.

Take an arbitrary split $L\sqcup R=[2n]$ into sets of size $n$. If $\alpha,\beta$ are distinct input exponent vectors, their output exponent restrictions $\alpha A_L,\beta A_L$ differ, and so do $\alpha A_R,\beta A_R$. The coefficient matrix across this cut therefore has one nonzero entry for each support element, in distinct rows and in distinct columns. Its rank is exactly $s$. Cutting an ROABP at this split in its variable order writes its output as $\sum_{i=1}^w P_i(z_L)Q_i(z_R)$ for the width $w$ there. This gives coefficient-matrix rank at most $w$, proving the claim.

For the matching width upper bound, use one independent path per monomial and place its univariate factors along the chosen order. Thus the minimum middle width is exactly $s$ in every order. The same substitution proves a stronger statement at a noncentral cut whose larger side has at least $n$ coordinates. At such a cut the larger-side exponents are distinct, so the rank is exactly the number of distinct exponent vectors visible on the smaller side.

The primes in the recipe can be found by trial division across the indicated interval. Each row has total exponent below $8n^2$. The case $n=0$ is the constant case. The formula applies to binary-encoded input exponents too. A compact output encoding needs only $O(\log n)$ additional bits per exponent, and a circuit computes each power by repeated squaring.

The substitution retains the coefficient-support structure used in the previous catalogue's sparse TI proof, but now forces the opposite rank behavior in the branching program model. The sparse polynomial can still be computed by a circuit with polynomial overhead. The result does not assert a lower bound on that general circuit model. [Source context for ROABPs](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.9/LIPIcs.ITCS.2026.9.html#S6)
