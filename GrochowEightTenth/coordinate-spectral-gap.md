# Deterministic diagonal gap separation and a bidiagonal singular-value counterpart

The first theorem gives a deterministic coordinate algorithm for diagonal perturbation of arbitrary Hermitian matrices. The second concerns the singular spectrum when the perturbation must stay in the real bidiagonal pattern. The known fast fixed-direction tridiagonal algorithm of Zhu and Nie gives a gap of order \(\delta^2 n^{-12}\). The Hermitian construction here uses a larger polynomial operation count and gives a gap linear in \(\delta\), with no restriction on sparsity. [Workshop Problems 3.2 and 3.8](https://arxiv.org/html/2602.05394v3#S3) · [Zhu–Nie, Theorem 4.1](https://arxiv.org/abs/2611.21055)

## Linear-budget diagonal shattering of every Hermitian matrix

**Theorem.** For every \(n\times n\) Hermitian \(A\), \(n\ge2\), and \(\delta>0\), one can deterministically find a real diagonal perturbation \(D\) of norm at most \(\delta\) such that
\[
 \min_{j<n}\big(\lambda_{j+1}(A+D)-\lambda_j(A+D)\big)>
 \frac{\delta}{4n^3}.
\]
The algorithm uses \(O(n^6)\) evaluations of a weighted eigenvalue sum to additive precision of order \(\delta/n^3\). For rational input and budget it runs in polynomial bit time and returns a rational perturbation with entries on an explicit grid. This is a polynomial-time linear-budget result for the spectral separation question in Workshop Problem 3.2. The bound on the evaluation count is above the near-linear or near-cubic targets in that problem.

### A bounded coordinate search

Let \(x\) be a vector of \(m\) perturbation coordinates, and allow \(-\alpha\le x_i\le\alpha\). Suppose \(F(x)\) is \(L\)-Lipschitz in each coordinate. Fix \(0<b\le L\), let \(M=\lceil8L/b\rceil\), set \(h=\alpha/M\), and use the grid with step \(h\). Penalize the quadratic coordinate norm via
\[
 J(x)=F(x)-(L/\alpha)\|x\|_2^2.
\]
Start at \(0\). Estimate \(J\) to error at most \(hb/128\), using exact arithmetic for the penalty. Take any allowed one-coordinate step \(+h\) or \(-h\) whose estimated gain is at least \(hb/16\). Stop when there is none. A taken step increases the true objective by at least \(hb/32\), whereas \(J(x)\le F(0)+mL\alpha\). Thus the number of steps is at most \(32mL\alpha/(hb)\). The grid and fixed choice order make the procedure deterministic.

A boundary coordinate always has a certified inward step, because its true gain is at least
\[
 -Lh+(L/\alpha)(2\alpha h-h^2)=Lh(1-h/\alpha)\ge Lh/2.
\]
Consequently the stopping point is interior on the grid. At an interior point, if some coordinate \(i\) has
\[
 F(x+he_i)+F(x-he_i)-2F(x)\ge hb/2,
\]
then the analogous second difference of \(J\) is at least \(hb/4\), since its penalty contribution is \(2(L/\alpha)h^2\le hb/4\). At least one of the two true gains is at least \(hb/8\), above the threshold after evaluation error. Such an \(x\) cannot be a stopping point.

### The spectral witness for a small gap

For a Hermitian \(H\), let \(F(H)=\sum_{j=1}^n j\lambda_j(H)\) with ascending eigenvalues. It is the maximum of \(\operatorname{tr}(GH)\) over Hermitian \(G\) unitarily similar to \(\operatorname{diag}(1,\ldots,n)\), by the trace variational principle. Thus \(F\) is \(n\)-Lipschitz in every real diagonal coordinate. Choose orthonormal eigenvectors \(u,v\) for adjacent eigenvalues \(\lambda_j,\lambda_{j+1}\) realizing a gap \(g\). Some coordinate \(i\) satisfies \(|u_i|^2+|v_i|^2\ge2/n\). On the two-dimensional span of \(u,v\), the coordinate projector \(e_i e_i^*\) has compression of rank at most one and eigenvalue spread \(s=|u_i|^2+|v_i|^2\).

Keep the other maximizing eigenvectors fixed. On this two-dimensional span, form two trial matrices \(G_+,G_-\) from the orthonormal basis diagonalizing the compressed projector, assigning the weights \(j,j+1\) first in the order giving the larger trace with the projector and then in reverse order. Their differences in trace with the projector equal \(s\). Their sum on the pair is \((2j+1)I\). Compared to twice the maximizing base value, the sum of their traces against \(H\) loses exactly \(g\), since \(2(j\lambda_j+(j+1)\lambda_{j+1})-(2j+1)(\lambda_j+\lambda_{j+1})=g\). Evaluating \(F(H+h e_i e_i^*)\) with \(G_+\) and \(F(H-h e_i e_i^*)\) with \(G_-\) therefore gives
\[
 F(H+h e_i e_i^*)+F(H-h e_i e_i^*)-2F(H)\ge hs-g .
\]
This holds also when the eigenvalues coincide, using any two orthonormal eigenvectors in that eigenspace. With \(m=n,\alpha=\delta,L=n,b=2/n\), the coordinate search halts at a point with \(g>hb/2=\delta/(4n^3)\). Its step count is \(O(n^5)\), and testing all neighbors uses \(O(n^6)\) approximate weighted-sum evaluations.

For rational input, eigenvalues can be enclosed to the required absolute accuracy by bisection and exact rational inertia tests. A rational complex Hermitian matrix can be treated via its realification, where each eigenvalue is doubled. Use fraction-free elimination for inertia and handle zero pivots using symmetric pivoting or the characteristic polynomial with exact root isolation. Polynomially many bisection steps suffice from a rational norm bound to absolute precision of order \(hb/n^2\). This suffices for the weighted-sum error, and the grid entries have polynomial bit length.

## Bidiagonal singular-value gaps above a threshold

**Theorem.** Let \(B\) be a real upper bidiagonal \(n\times n\) matrix with \(\|B\|_2\le1\), and let \(0<\delta,\tau\le1\). A deterministic coordinate algorithm produces an upper bidiagonal \(E\) with \(\|E\|_2\le\delta\) such that every adjacent singular-value pair of \(B+E\) whose smaller value is at least \(\tau\) has gap greater than
\[
 \frac{\delta\tau^2}{136n^3}.
\]
It uses \(O(n^6/\tau^2)\) evaluations of a weighted singular-value sum to additive precision of order \(\delta\tau^2/n^3\). The theorem allows arbitrary singular values below \(\tau\). This gives a structure-preserving gap guarantee for the upper singular band of the bidiagonal SVD in Workshop Problem 3.8.

Allow all bidiagonal coordinates to move within \([-\delta/2,\delta/2]\). There are \(m=2n-1\) coordinates, and every resulting perturbation has norm at most \(\delta\) from its maximum row and column sums. For ascending singular values put \(F(B')=\sum_j j\sigma_j(B')\). The variational principle is the maximum of \(\sum_j j u_j^{\mathsf T}B'v_j\) over two orthonormal bases. This shows \(n\)-Lipschitz continuity in each single entry.

For any adjacent pair \(\sigma_j,\sigma_{j+1}\ge\tau\) take two left and right singular vector pairs. Write the two rows of their coordinate evaluations as
\[
 a_i=\big((u_j)_i,(u_{j+1})_i\big)^{\mathsf T},\qquad
 c_\ell=\big((v_j)_\ell,(v_{j+1})_\ell\big)^{\mathsf T}.
\]
Under equal two-dimensional rotations of both bases within the selected pair, the coordinate increment \(e_i e_\ell^{\mathsf T}\) has trial quadratic form with matrix \((a_i c_\ell^{\mathsf T}+c_\ell a_i^{\mathsf T})/2\). Its eigenvalue spread is \(\|a_i\|\|c_\ell\|\), by the two-by-two discriminant identity. Since
\[
 2\tau\le\sigma_j+\sigma_{j+1}
 =\sum_{(i,\ell)\ {\rm bidiagonal}} B'_{i\ell}\,a_i^{\mathsf T}c_\ell
 \le \max_{(i,\ell)\ {\rm bidiagonal}}\|a_i\|\|c_\ell\|
        \sum_{(i,\ell)\ {\rm bidiagonal}}|B'_{i\ell}|,
\]
and the last sum is at most \(m(1+\delta)\le4n\), some allowed coordinate has spread at least \(b=\tau/(2n)\). The same two trial assignments of adjacent weights lose exactly \(g=\sigma_{j+1}-\sigma_j\) at the base point, because jointly rotating the two singular vector pairs conjugates the base two-by-two diagonal bilinear form. Thus the centered difference is at least \(hb-g\) at the selected coordinate. Apply the bounded search with \(L=n,\alpha=\delta/2\). Since \(M=\lceil16n^2/\tau\rceil\le17n^2/\tau\), the guaranteed gap is \(hb/2\ge\delta\tau^2/(136n^3)\), as asserted. Weighted sums of singular values can be computed to the required absolute accuracy using the Hermitian dilation, whose nonnegative half of the sorted spectrum gives the singular values with zeros included.

### Why a lower band threshold is required

For any positive integer \(L_0\), build a real upper bidiagonal matrix on two disjoint coordinate windows of length \(2L_0+1\), with a buffer coordinate between them. Its entries have magnitude at most \(1/2\), hence its norm is at most one. In each window with center \(c\), put diagonal and superdiagonal entries \((1/2,0)\) at rows \(c-L_0,\ldots,c-1\), and \((0,1/2)\) at rows \(c,\ldots,c+L_0-1\). The other entries may be zero. Let \(B'\) result from any upper bidiagonal perturbation of norm at most \(\delta\le1/8\). Write \(d_i,e_i\) for its diagonal and superdiagonal.

In each window start a vector with value one at its center. Recursively solve \(d_i v_i+e_i v_{i+1}=0\) to the left using \(v_i=-e_i v_{i+1}/d_i\), and to the right using \(v_{i+1}=-d_i v_i/e_i\). Outside the window set it to zero. The denominators have magnitude at least \(1/2-\delta\), while the numerators have coefficient magnitude at most \(\delta\). The two endpoint magnitudes are thus at most \((\delta/(1/2-\delta))^{L_0}\). Only the first row just outside the left edge and the last row in the window can have nonzero image, and their coefficients have magnitude at most \(1+\delta\). After normalizing the vector, the residual norm is at most \(\sqrt 2(1+\delta)(\delta/(1/2-\delta))^{L_0}\).

The two window vectors are orthonormal and their residual supports are disjoint by the buffer. On their entire two-dimensional span the operator has norm at most this residual bound. The singular min–max principle gives the same upper bound for the second-smallest singular value of \(B'\). In particular, at fixed \(\delta\le1/8\), the gap between the two smallest singular values stays exponentially small in dimension for every perturbation in the bidiagonal pattern. The high-band theorem is a sufficient uniform guarantee and the bottom of the spectrum exhibits a distinct behavior under the same coordinate constraint.
