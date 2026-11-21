# Sharp Ritz-value guarantees with arbitrary buffer spaces

[Simons Workshop Problem 3.4](https://arxiv.org/html/2602.05394v3#S3.SS3) asks when adding an arbitrary buffer to an approximate invariant subspace preserves accurate Ritz values. Let V be a reducing d-dimensional subspace of a matrix A, with normal restriction B=A|_V. Fix a buffer dimension r. Let Q be an orthonormal basis for a (d+r)-space containing a d-space within largest principal-angle sine η of V. For all sufficiently small η, the compression Q*AQ has at least the multiplicity of each distinct eigenvalue λ of B in a disk of radius C_r ‖A‖₂ η^{2/(r+1)} around λ. The smallness threshold may depend on the relative separation of distinct eigenvalues of B. The bound is uniform over buffer orientations and ambient dimensions and the exponent is sharp for normal A.

Scale to ‖A‖₂=1, the zero case being immediate. The principal-angle sines between V and the whole Q-space are at most η. Take principal vectors v_i in V and q_i in the Q-space, with q_i=c_i v_i+s_i z_i, where c_i≥√(1−η²), 0≤s_i≤η, and the z_i with s_i>0 are orthonormal in V-perpendicular. The complement W of the q_i inside the Q-space lies in V-perpendicular, since each v_i projects onto c_i q_i. In the resulting orthonormal basis the compression is
$$
\begin{pmatrix}B+E&F\\G&C\end{pmatrix},\qquad
\|E\|\le3\eta^2,\quad\|F\|,\|G\|\le\eta,\quad\|C\|\le1.
$$
The top block is diag(c_i) B diag(c_i) plus an orthogonal-complement contribution of norm at most η². Each contribution from replacing diag(c_i) by I costs at most η², and the off-diagonal blocks involve one s_i factor because V reduces A.

Fix λ∈spec B and set R=L_r η^{2/(r+1)}. Assume 2R<1 and 2R is below half the separation to other distinct eigenvalues of B. Select t∈[R,2R] at distance at least R/(4(r+1)) from each of the r numbers |λ−ν| for ν∈spec C. The deleted intervals have total length less than R. On |z−λ|=t normality gives ‖(zI−B)⁻¹‖≤1/R. If r≥1, the smallest singular value of zI−C is at least its determinant modulus divided by 3^{r−1}, since its other singular values are at most 3. Its determinant modulus is at least (R/(4(r+1)))^r. Thus ‖(zI−C)⁻¹‖≤3^{r−1}(4(r+1)/R)^r.

Interpolate from B⊕C to the compression by multiplying E,F,G by a∈[0,1]. On the selected circle, the upper Schur complement is zI−B−aE−a²F(zI−C)⁻¹G. After multiplying the correction by (zI−B)⁻¹ its norm is at most 3η²/R+C'_r η²/R^{r+1}<1 for large enough L_r. For r=0 omit the second term. Hence no eigenvalue crosses the circle; initially it contains at least the multiplicity of λ in B, so finally it still does. For small η the disks for distinct eigenvalues are disjoint. Rescaling gives the stated bound.

For sharpness with r≥1, use A=0⊕S with S the cyclic unitary shift on e₁,…,e_(r+1). Take V=span(e₀), approximate it with q₀=√(1−η²)e₀+ηe_(r+1), and add the buffer span(e₁,…,e_r). In the compression all cycle weights are 1 except the two entering and leaving q₀, both η. Its characteristic polynomial is z^(r+1)−η². Every Ritz value is at distance η^{2/(r+1)} from the isolated eigenvalue 0. For r=0, compress diag(0,1) to span(q₀) using e₁ in q₀. The error is then exactly η².

## A nonreducing invariant subspace

If V is invariant and the restriction B is diagonalizable, the same conclusion holds uniformly over buffers with error C_(r,κ_B)‖A‖₂ η^{1/(r+1)}, where κ_B bounds the condition number of an eigenbasis of B. This exponent is sharp even if A has an eigenbasis of bounded condition number.

In the principal-vector block construction, invariance still gives ‖G‖≤η. The upper coupling may have norm one and the top error is at most η+3η² because of the additional cross term from A(V-perpendicular) to V. The resolvent bound of B on the chosen circle becomes κ_B/R. Apply the same Schur argument with R=L_(r,κ_B)η^{1/(r+1)}. The norm to control is at most κ_B[(η+3η²)/R+C'_rη/R^{r+1}], and tends below one for the chosen L and small η.

For r≥1, modify the cyclic-shift example by adding e₀ to A e_r. The compressed characteristic polynomial becomes z^(r+1)−η(√(1−η²)+η), because the two end weights are η and √(1−η²)+η. The strict rate follows by taking roots. In the full space A is block upper triangular with diagonal blocks 0 and a unitary, invertible shift; the extra row above the shift is removed by a shear whose off-diagonal norm is one. Thus A has a uniformly well-conditioned eigenbasis. For r=0 the analogous example is Ae₀=0 and Ae₁=e₀+e₁, whose one-dimensional Ritz value is η(√(1−η²)+η).
