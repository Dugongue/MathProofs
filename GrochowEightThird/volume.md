# A spectral tightness bound for volume sampling

This answers [Simons Workshop Problem 4.7](https://arxiv.org/html/2602.05394v3) with a bound valid at every rank, equality cases, and a family showing the sharp order of the gap near a scalar spectrum.

Let x_k and y_k have the definitions in the problem. Write m=n−k and let μ_i=1/λ_i be the eigenvalues of the precision matrix A=K⁻¹. Put a=min μ_i, b=max μ_i and M=(Σ μ_i)/n. For 0≤k<n,
$$
\frac{m}{M}\le x_k\le y_k\le\frac{m(a+b-M)}{ab},\qquad
\frac{4ab}{(a+b)^2}\le\frac{ab}{M(a+b-M)}\le\frac{x_k}{y_k}\le1.
$$
The relative gap can have quadratic order in (b−a)/(b+a), even for n=4 and k=2.

## Universal bound

For the unselected set J of size m, the error is tr(A[J,J]⁻¹) by Schur complementation. All size-k sampled sets have positive probability under volume sampling, so their minimum is at most their mean y_k. By Schur–Horn there is an admissible orientation of A with diagonal M everywhere. All its size-m principal blocks then have trace mM and spectrum in [a,b]. For each such block, convexity gives lower bound m/M for its inverse trace. The chord inequality u⁻¹≤(a+b−u)/(ab) gives upper bound m(a+b−M)/(ab) for the same inverse trace. Take the minimum and the volume-sampling average, respectively. The last coarser bound comes from M(a+b−M)≤(a+b)²/4.

## Equality at the upper end

If A has at most one exceptional eigenvalue, orient it as a scalar matrix plus a multiple of vvᵀ with v=(1,…,1)/√n. Every block of a given size has identical inverse trace, hence x_k=y_k for every k. For k=1 and arbitrary spectrum, set c=tr(K²)/tr(K). The trace-zero matrix K²−cK has a constant zero diagonal in some orthonormal basis by Schur–Horn. In that basis the captured trace for every singleton i is (K²)_ii/K_ii=c. The singleton errors are equal and x₁=y₁.

## The quadratic order is sharp

Set n=4, k=2, and A=I+tH, where 0<t<1 and H ranges over real symmetric matrices with eigenvalues 1,1,−1,−1. Then a=1−t and b=1+t. The complement J of the selected set is distributed proportionally to det A[J,J], by Jacobi's complementary minors identity. For blocks of size two, the product of the inverse trace and the determinant equals the trace. Summing the six traces gives 12, and the sum of the determinants is e₂(1+t,1+t,1−t,1−t)=6−2t². Hence y₂=2+2t²/3+O(t⁴).

Suppose there were a sequence t→0 with y₂−x₂=o(t²). For each member take a maximizing H, which exists by compactness and continuity. Each two-set has probability uniformly bounded below as t→0. Since all six errors are at least x₂ and their mean is y₂, all six equal y₂+o(t²). For each pair J the uniform inverse expansion gives
$$
\operatorname{tr}(A[J,J]^{-1})
=2-t\operatorname{tr}H[J,J]+t^2\operatorname{tr}(H[J,J]^2)+O(t^3).
$$
All pairwise sums of diagonal entries of H are O(t), so the diagonal tends to zero. Pass to a convergent subsequence with limit H₀. Adding the expansions of a pair and its complement cancels the linear term exactly. It gives (H₀)_ij²+(H₀)_kl²=2/3 for complementary pairs ij,kl. Since H₀ is an involution with zero diagonal, all row sums of squared off-diagonal entries are 1. Adding the two rows in each complementary pair shows (H₀)_ij²=(H₀)_kl². Thus all off-diagonal squares equal 1/3.

Conjugate by diagonal signs so that the three off-diagonal entries of the first row are positive. Orthogonality of the first row to each of the other three rows forces the three remaining off-diagonal signs to be pairwise opposite. This is impossible. Compactness therefore gives y₂−x₂=Ω(t²), while the universal bound gives y₂−x₂=O(t²). The relative gap has the same order.
