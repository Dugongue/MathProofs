# Two Nyström follow-up questions

Matthew J. Colbrook asks for a signed-graph classification and for quantitative guarantees under strictly diagonally dominant positive definite shifts in the [conclusion of his Nyström preprint](https://arxiv.org/html/2607.19282). The following theorems answer those two questions. They concern a real symmetric positive definite matrix A. Set F(J) = tr(A[J,J]⁻¹) and F(∅) = 0. The Nyström error at selected indices S is F(V∖S), by the inverse block formula applied to the covariance A⁻¹.

## 1. Exact classification by signed support

**Theorem.** Every positive definite realization of a signed support graph has supermodular F if and only if the graph is antibalanced, meaning that every simple cycle of length l has sign product (−1)^l. If the condition fails, then for every η > 0 there is a positive definite realization with unit diagonal and max absolute off-diagonal row sum below η whose F fails supermodularity.

**Sufficiency.** A sign switch using a spanning forest turns every edge negative. The forest paths prove the claim for each nonforest edge by applying the cycle sign condition. Conjugation by the diagonal sign matrix preserves every F(J). Write the switched principal matrix as D_J^(1/2)(I−W_J)D_J^(1/2), where D is the diagonal and W is symmetric, nonnegative, and has zero diagonal. Positive definiteness implies λ_max(W_J) < 1. The Rayleigh quotient of the entrywise absolute value of a vector shows that the absolute magnitude of every eigenvalue is at most λ_max(W_J). The Neumann sum therefore expresses F(J) as a sum of nonnegative weights of closed walks all of whose vertices belong to J. Each fixed-vertex-set containment indicator is supermodular. Finite partial sums and their pointwise limit preserve the supermodular inequality.

**Necessity.** Choose a simple cycle violating the sign condition. Switch signs on it so that the path obtained by deleting one edge has negative edges and the closing edge ij is positive. First use only this cycle, put 1 on the diagonal, and use weights −ε along the path. Let R contain the internal path vertices and let Q = A[R,R]⁻¹. The path is connected and the Neumann expansion gives strictly positive entries of Q, including for singleton R. Set the closing weight to t₀ = A[i,R] Q A[R,j] > 0. Since the operator norm of the internal path adjacency is at most 2ε, t₀ ≤ ε²/(1−2ε). At t₀ the off-diagonal entry of the Schur complement on {i,j} is zero. For B = A⁻¹ this gives B_ij = 0 and the inverse block formulas give B_Ri = −Q A_Ri B_ii > 0 and B_Rj = −Q A_Rj B_jj > 0 entrywise. Thus the full columns b_i and b_j of B have positive inner product. All these inverses exist for small ε by strict diagonal dominance. Increase the closing weight slightly. The Schur complement now has positive off-diagonal, so c = B_ij < 0. Continuity keeps b_iᵀb_j > 0.

Write a = B_ii, b = B_jj, s_i = ‖b_i‖²/a, and s_j = ‖b_j‖²/b. With J the cycle vertices, deleting a block T from A[J,J] subtracts tr(B[:,T] B[T,T]⁻¹ B[T,:]) from F(J), by the inverse block formula. The pairwise contrast is therefore
$$
F(J)-F(J-i)-F(J-j)+F(J-\{i,j\})
=\frac{2c\,b_i^\mathsf{T}b_j-c^2(s_i+s_j)}{ab-c^2}<0.
$$
The denominator is positive by positive definiteness. Choose ε and the increase of t₀ small enough to keep every off-diagonal row sum strictly below min(η,1). Restore every required chord and every other graph edge with sufficiently small weight of the required sign. Continuity preserves the strict violation on the cycle vertex set and the strict row bound. Finally undo the sign switch.

## 2. Explicit submodularity ratio under diagonal dominance

**Theorem.** Let ρ = max_i Σ_{j≠i}|A_ij|/A_ii < 1. For any selected set S and any nonempty block T disjoint from it, the sum of the individual Nyström error decreases from adding elements of T at S is at least 1 − ρ times the decrease from adding T jointly. In particular greedy selection of k columns attains at least 1 − exp(−(1−ρ)) of the maximal decrease from the empty selection.

**Proof.** Let J be the complement of S and B = A[J,J]⁻¹. Write A[J,J] = D^(1/2)(I+Z)D^(1/2) with D its diagonal. The normalized Z is symmetric and similar to a matrix whose absolute row sums are at most ρ, hence its spectrum lies in [−ρ,ρ]. Also Z_ii = 0. Spectral calculus gives B ⪰ (1+ρ)⁻¹ D⁻¹. The chord bound
$$
(1+x)^{-1}\le (1-x)/(1-\rho^2) \qquad (-\rho\le x\le\rho)
$$
gives B_ii ≤ (1−ρ²)⁻¹ D_ii⁻¹. Combining them on T gives B[T,T] ⪰ (1−ρ) diag(B[T,T]). Inverting both sides reverses the order. With P = B[T,:]B[:,T] positive semidefinite, the block inverse formula gives joint gain tr(P B[T,T]⁻¹) and summed singleton gain tr(P diag(B[T,T])⁻¹). The desired inequality follows by taking the trace against P.

The gain increases with the selected set because each deleted block subtracts a positive semidefinite correction from the embedded inverse. If an optimal k-set is compared with the current greedy set, their union achieves at least its gain. The submodularity ratio guarantees a singleton closing at least (1−ρ)/k of the remaining gap to optimum. Iterating this inequality k times proves the guarantee.
