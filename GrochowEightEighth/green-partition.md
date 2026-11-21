# Optimal longitudinal partitioning for separable Green operators

Consider \(N\) longitudinal layers, each with \(m\) transverse unknowns. Let \(T\) be an \(N\times N\) tridiagonal matrix with strictly negative entries on both off-diagonals and a positive diagonal symmetrization that is positive definite. Let \(D\) be a nonnegative diagonal matrix and let \(S\) be a real symmetric positive semidefinite transverse matrix. The discretized operator and its Green matrix are
\[
A=T\otimes I_m+D\otimes S,\qquad G=A^{-1}.
\]
This model allows longitudinally varying coefficients and longitudinal drift when the tridiagonal part has the stated symmetrization. For example it covers tensor-product finite differences for the separable reaction–diffusion operator with longitudinal diffusion and a longitudinally varying multiplier of transverse diffusion.

Fix a prescribed set of admissible contiguous binary interval splits, dense leaves of prescribed admissible lengths, a common rank cap \(k\) on each sibling off-diagonal block, and an optional upper bound \(B\) on the number of leaves. Given an orthogonal eigendecomposition of \(S\), there is an exact-arithmetic algorithm which returns an optimal partition and a representation of its best blockwise Frobenius approximation to \(G\). Its approximation factor in the specified partition class is \(1\). It works without assembling the dense Green matrix. With \(J\) admissible splits, the unbudgeted search uses \(O(Nm+J(m-k)_++J+N^2)\) operations. With a leaf budget, it uses \(O(Nm+J(m-k)_++JB^2+N^2B)\). The cost of finding the transverse eigendecomposition, if needed, is separate. This gives a structured PDE case of Workshop Problem 4.5, including the exact comparison to the best allowable partition. [Workshop Problem 4.5](https://arxiv.org/html/2602.05394v3#S4.SS1.SSSS4)

## All cut costs from Green factors

Let \(0\le\mu_1\le\cdots\le\mu_m\) be the eigenvalues of \(S\). Transforming the transverse coordinates independently in every layer and then grouping by modes makes \(A\) the direct sum of \(T_j=T+\mu_jD\). Each \(T_j\) is tridiagonal, with the same positive diagonal symmetrizer as \(T\). A symmetric positive definite matrix with nonpositive off-diagonal entries has entrywise nonnegative inverse. For a direct proof write it as \(bI-C\) with \(C\ge0\) entrywise, choosing \(b\) larger than the top eigenvalue and every diagonal entry. Then \(\|C\|_2<b\) by positive definiteness and the geometric series for its inverse is entrywise nonnegative. The tridiagonal connectivity makes its inverse strictly positive. Positive diagonal similarity preserves this sign. Differentiation gives
\[
\frac{\mathrm d}{\mathrm d\mu}(T+\mu D)^{-1}=-(T+\mu D)^{-1}D(T+\mu D)^{-1},
\]
so the inverse is entrywise nonincreasing in \(\mu\).

For a single mode write the magnitudes of the upper and lower off-diagonal entries as \(u_i,l_i>0\), respectively. Let \(L_i\) be the leading principal determinant through row \(i\), and \(R_i\) the trailing principal determinant from row \(i\). Use \(L_0=R_{N+1}=1\). All are positive by diagonal similarity, and each sequence is found in one pass by expansion along the last or first row. By the tridiagonal cofactor formula the inverse entry, for \(a\le b\), is
\[
(T_j^{-1})_{ab}
=\frac{L_{a-1}R_{b+1}}{L_N}\prod_{i=a}^{b-1}u_i.
\]
For the reverse entry the same formula uses the \(l_i\). This follows by expanding the cofactor along the unique tridiagonal chain connecting the two indices, leaving its two endpoint principal minors. With \(U_h=\prod_{i=1}^{h}u_i\), the upper crossing entry is the product \(L_{a-1}/U_{a-1}\) times \(R_{b+1}U_{b-1}/L_N\). For the lower crossing use prefix products of \(l_i\) and transpose the resulting block. Thus each mode's crossing block in either direction has rank one. Its sole singular value is a product of two Euclidean norms, obtainable from prefix sums of the squared factor entries. The construction uses \(O(Nm)\) preprocessing. [Usmani's tridiagonal inverse formula](https://doi.org/10.1016/0898-1221%2894%2990066-3)

For a split \([a,b]=[a,s]\cup[s+1,b]\), the full crossing block is, after orthogonal transformations of its rows and columns, a direct sum of these rank-one mode blocks. Its nonzero singular values are the mode Frobenius norms just computed. Nonnegative entrywise monotonicity makes them nonincreasing in mode order, in each direction. Thus the exact optimal squared loss from rank \(k\) is the sum of the squared norms of modes \(j>k\), evaluated in \(O((m-k)_++1)\) operations. This eliminates any dense block singular-value calculation during the search.

## Partition optimization and perturbation guarantee

A tree's off-diagonal sibling rectangles and dense diagonal leaf squares are disjoint and partition all entries. The globally best squared Frobenius error for that tree is therefore the sum of its individual split losses. Let \(F(a,b,\ell)\) denote the minimum such sum on interval \([a,b]\) with exactly \(\ell\) leaves. Set the one-leaf cost to zero when that leaf is allowed and all other infeasible entries to infinity. Otherwise minimize the split loss plus \(F(a,s,j)+F(s+1,b,\ell-j)\) over the admissible splits and numbers \(j\) of left leaves. Increasing interval length gives a dynamic program, and storing predecessors returns the optimum tree. Dropping the leaf-index coordinate gives the unbudgeted version. The reported runtimes include \(O(JB^2)\) comparisons for the convolution over leaf counts when a budget is present.

The retained mode factors are a representation of the optimal off-diagonal blocks. A dense leaf can be represented by its unrestricted same-layer and crossing Green entries in modal coordinates, using the diagonal case and both directions of the cofactor formula. This specifies the whole approximation without evaluating a transverse dense block for every pair of indices.

The selected tree has a deterministic robustness guarantee. If \(G'=A'^{-1}\) is another solution operator and \(\|G'-G\|_F\le e\), the best approximation errors for any fixed tree differ by at most \(e\), by the triangle inequality for distance to its block-rank class. If \(d\) is the optimum model error, the selected tree has error at most \(d+e\) on \(G'\), and the optimal error on \(G'\) is at least \(d-e\). For \(d>e\) this gives relative factor \((d+e)/(d-e)\). The error \(e\) may be bounded by \(\|A'^{-1}\|_2\|A^{-1}\|_2\|A'-A\|_F\) by the resolvent identity. These results use exact arithmetic and the specified admissible longitudinal partitions.
