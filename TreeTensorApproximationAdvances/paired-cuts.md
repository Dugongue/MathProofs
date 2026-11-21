# Repeated two-cut improvements for tree tensor approximation

Fix a tree with $m\ge3$ nodes and positive bond caps, and a postorder on its $m-1$ oriented edge cuts. Pair consecutive cuts in that order, keeping a final singleton if needed. For each pair let $r$ be the cap of its first cut. If $E$ is the optimum squared Frobenius error, a deterministic approximation with the original caps achieves
$$
\|A-X\|_F^2 \le
\left(m-1-\sum_{\text{pairs}}\frac{1}{r+3}\right)E
$$
with exact singular-vector projections. There is a deterministic polynomial-bit-time version for dense rational input with rational cores, in which the summands are $1/[2(r+3)]$. In particular for caps bounded by $R$ the exact-projection factor improves on $m-1$ by at least $\lfloor(m-1)/2\rfloor/(R+3)$. This amplifies the earlier single-swap result and improves its per-swap constant. The third section proves the numerical margin needed in the rational algorithm. [Simons Workshop Problem 6.1](https://arxiv.org/html/2602.05394v3#S6.SS1) · [Earlier single-swap proof](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/tree-tensor.md)

## 1. A two-cut estimate from the optimum's row space

Consider a tensor in the current coordinates immediately before two consecutive cuts. Their left axis sets are either disjoint or the first is contained in the second. Let $Y$ be a best approximation under just the two upcoming cut ranks. Existence follows from closedness of the two rank bounds and compactness on a sufficiently large ball. Use $A,Y$ as matrices in the first cut, and put $W=(A-Y)(A-Y)^{\mathsf T}$ and $E_2=\operatorname{tr}W$.

Any linear map on the first left space preserves both rank bounds. In the second cut it acts on one side. With the row space of $Y$ fixed, any matrix with rows in that space has the form $MY$ for a linear map $M$ on the first left space. The least-squares fit among them is $A$ times the orthogonal projector onto that row space. Consequently $Y$ is that fit, and $(A-Y)Y^{\mathsf T}=0$. In particular
$$
S=AA^{\mathsf T}=YY^{\mathsf T}+W.
$$
Write $\lambda_i$ for the decreasing eigenvalues of $S$, including zeros. Cap $r$ at the left dimension. When $r$ is at least the rank of $A$, a first projector containing its column space has zero loss and the second loss is at most $E_2$. This covers the case of a missing direction $r+1$, and also allows the implementation to use a known upper bound on the input cut rank.

Otherwise use the main first projection $P_*$ onto the top $r$ eigenvectors and the $r$ trials $P_i$ that replace direction $i$ by direction $r+1$. Set
$$
t=\sum_{i>r}\lambda_i,\quad s=E_2-t,\quad \lambda_0=\lambda_{r+1},\quad
\Delta_i=\lambda_i-\lambda_0,\quad w_i=W_{ii},\quad U=\sum_{i>r}w_i.
$$
We have $s\ge0$ and $\lambda_0\le E_2$. In this eigenbasis express $YY^{\mathsf T}=S^{1/2}ZS^{1/2}$ by inverting $S^{1/2}$ on its support and putting zero on the kernel. Here $0\le Z\le I$ and $\operatorname{tr}Z\le r$, because its rank is at most $r$. Thus $w_i=\lambda_i(1-Z_{ii})$, and
$$
s=\sum_{i\le r}\lambda_i-\operatorname{tr}(YY^{\mathsf T})
\ge \sum_{i\le r}\Delta_i(1-Z_{ii})
=\sum_{i\le r}w_i\frac{\Delta_i}{\lambda_i}.
$$
The inequality uses $\sum_{i>r}Z_{ii}\le\sum_{i\le r}(1-Z_{ii})$ and $\lambda_i\le\lambda_0$ on the tail.

For each trial greedily perform the second rank truncation. Applying the first projection to $Y$ is feasible for that second rank, so the total pair loss of $P$ is at most its first loss plus $\operatorname{tr}(PW)$. Relative to $2E_2$, $P_*$ saves at least $s+U$. The swap at $i$ saves at least $s+U-w_{r+1}+w_i-\Delta_i$. With $z=\max(0,\max_{i\le r}(w_i-\Delta_i))$, the best saving is therefore at least $\max(U,s+z)$.

Assume $E_2>0$. Since $\lambda_i=\lambda_0+\Delta_i\le E_2+\Delta_i$ and $\Delta_i\ge(w_i-z)_+$, one has
$$
\frac{\Delta_i}{\lambda_i}\ \ge\ \frac{w_i-z}{E_2+w_i}.
$$
The right side is nonpositive if $w_i<z$. In the other case this follows from monotonicity of $x/(E_2+x)$ on nonnegative numbers and its value at $w_i-z$. As $\sum_{i\le r}w_i/(E_2+w_i)\le1$, it follows by Cauchy–Schwarz that
$$
s+z\ \ge\ \sum_{i\le r}\frac{w_i^2}{E_2+w_i}
\ \ge\ \frac{(E_2-U)^2}{(r+1)E_2-U}.
$$
Set $u=U/E_2$. If $u\ge 1/(r+3)$ the baseline already suffices. In the opposite case, the normalized lower bound $(1-u)^2/(r+1-u)$ is at least $1/(r+3)$: after multiplying the denominators, the difference of the numerators is $2-(2r+5)u+(r+3)u^2$, which is positive on $[0,1/(r+3)]$. For example $2-(2r+5)u\ge1/(r+3)$. Thus the best pair loses at most $(2-1/(r+3))E_2$. If $E_2=0$, the ordinary top projection and second truncation give zero loss directly. The choice uses evaluated losses and needs no knowledge of an optimum.

## 2. Amortizing across the tree

Root the tree and use the recorded orthonormal bases to compress from children to parents. After each projection, the residual tensor in packed coordinates is the previous tensor mapped by the adjoint of the recorded isometry. Its norm cannot increase. Every unprocessed cut sees the earlier maps as products of separate maps on its two sides. Thus compressing a globally optimum comparison produces a feasible reference for each new pair, and its error is at most $E$. The optimum $E_2$ for a pair is at most that reference error. The final singleton, if present, loses at most $E$. The squared output error is the sum of the losses by repeated orthogonal decomposition. At each pair the algorithm keeps only the least-loss trial and commits both bases, so the total number of trials is at most the sum of the individual numbers of first-cut trials. The resulting tree tensor has the original caps and the stated exact-projection bound.

## 3. Rational implementation

Use exact rational orthogonal rotations to approximate the eigenbasis at each unfolding, with the Jacobi implementation and square-root estimate of the earlier proof. Here are the stability details needed for the pair argument. Let $N$ be the dense input length, $R$ the largest relevant cap, and $B\ge1$ a rational upper bound on $\|A\|_F$. Exact feasibility is detected by rational cut ranks. Otherwise take a positive rational $E_0\le E$ of polynomial bit length, using a nonzero minor of a violated cut as in the earlier proof. Choose $\xi\le \min(1,E_0/[200m(R+3)B])$. At each unfolding obtain an exactly orthogonal rational basis in which the off-diagonal Frobenius norm of the Gram matrix is at most $\xi^2/N$, and sort its diagonal. The left-basis surrogate then differs by at most $\xi$ in Frobenius norm.

For a pair it is legitimate to optimize for the surrogate. If column padding is needed to realize the Gram surrogate, append a zero-padded dummy axis outside the first left cut and put it on either one side of the second cut. This makes both cuts actual tensor cuts in the enlarged ambient space. Extension by zeros preserves the two-cut optimum exactly, since slicing at the original dummy coordinate contracts errors and cannot increase ranks. The rational basis is an exact singular-vector basis for the enlarged surrogate. For each fixed trial of the first projection, the optimal total pair loss is the squared distance to tensors supported in its first left range and satisfying the second rank bound. That feasible set contains zero and admits the same extension and restriction across the dummy axis. Distances, including the two-cut optimum before prescribing a branch, are 1-Lipschitz in the input Frobenius norm. Their squares change by at most $(2B+\xi)\xi\le3B\xi$ between the original and surrogate. Applying the exact pair theorem to the surrogate and comparing both squared distances gives additive cost at most $9B\xi$ for the best rational first trial with an exact second truncation. An approximate second truncation costs at most $6B\xi$ more by two applications of the same distance comparison. The final singleton needs at most $6B\xi$ extra. Choosing the minimum actual rational loss over trials therefore adds at most $15mB\xi$ in all.

For at least one pair, the exact saving coefficient is at least $1/(R+3)$, and this additive budget is at most $E/[2(R+3)]$. It therefore consumes at most half of the total claimed exact saving. A tree with at most one cut can instead use exact feasibility or an arbitrarily accurate rational matrix approximation. The fixed-precision rational rotations have polynomial bit length. Between cuts, the stored rational tensor denominator grows additively in bit length by the denominator of each basis change, and the logarithm of the accuracy requirement above is polynomial. This yields the claimed deterministic bit-time result for trees with at least two cuts.

## 4. A factor depending only on the originally violated cuts

Test all original cut ranks. Call a cut active if its rank in the original tensor exceeds its prescribed cap, and write $b$ for the number of active cuts. Pair only the active cuts in postorder. Every intervening inactive cut is processed in its usual position. The exact factor is
$$
 b-\sum_{\text{active pairs}}\frac{1}{r+3}.
$$
For $b\ge2$ the rational factor is $b-\sum_{\text{active pairs}}1/[2(r+3)]$, for the same accuracy budget as before. For $b=0$ the original tensor is returned exactly. For $b=1$ the optimum equals the best squared matrix truncation error across the sole active cut. It is attained by the exact-projection algorithm, and rational cores achieve factor $1+\varepsilon$ in time polynomial in the binary data length and $\log(1/\varepsilon)$.

Indeed, before any cut, earlier compressions act on separate sides of it and cannot increase its rank, regardless of the earlier branch choices. Thus an inactive cut admits a projection losing zero. In a pair of active cuts temporarily consider the second cut in the coordinates immediately after projecting at the first, before processing the intervening inactive cuts. Its rank constraint is the same flattening constraint on the surviving coordinate axes. The two-cut proof bounds the sum of the first loss and this hypothetical second loss. Now actually process the intervening cuts. They all lose zero with exact projections. Their compression maps act separately on the sides of the upcoming second cut, so their images of any best second-cut comparator still have the required rank. By contraction the actual second loss is at most the hypothetical one. Consequently the pair bound still holds. The two-cut reference coming from the global optimum is valid at the beginning of each such block, and no inactive cut adds to the exact loss. For one active cut, all earlier compressions have zero loss and act as separate isometric embeddings after re-expansion on its two sides. The surviving unfolding therefore has the same nonzero singular values as the original unfolding. All later cuts again lose zero. The total loss equals the original matrix tail, which is also a lower bound on every feasible approximation.

In rational arithmetic an inactive cut can lose at most $6B\xi$, using the same single-cut surrogate comparison against a true zero-loss projector. The map applied there remains contractive and still preserves the rank of the hypothetical second-cut comparator. Thus all extra numerical costs remain bounded by $15mB\xi$. If $b\ge2$ the previous half-margin argument applies to the active pairs. If $b=1$ choose instead $\xi\le\min(1,\varepsilon E_0/[100mB])$. No new branching is needed.

For a concrete example, take a two-leaf tree with first and second leaf dimensions two and middle dimension three. The nonzero coefficients have weights $3,3,4$ and lie respectively at $(0,0,0),(0,1,1),(1,2,1)$, with axes written first leaf, middle, second leaf. Both edge caps are one. The leading first direction is the first coordinate, and greedy truncation retains squared norm $9$. The swap retains squared norm $16$, which is optimal: distinct middle coordinates make the retained squared norm a convex combination of the squared weights and zeros for fixed unit vectors in both leaves.

## Verification

The main algorithm has a paper proof. A Lean companion checks the final scalar lower bound used in Section 1.
