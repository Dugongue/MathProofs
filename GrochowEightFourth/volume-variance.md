# The variance of volume-sampled Nyström error

The [Simons Workshop report, Section 4.2](https://arxiv.org/html/2602.05394v3#S4.SS2) asks about variance and higher-order statistics of volume-sampling trace error. For a positive definite matrix K of order n and a budget 1≤k<n, the following gives a spectral upper envelope for every convex statistic, characterizes exactly when it is attained, and bounds the variance deficit using the off-diagonal entries of K.

Write K=U diag(λ) U* with positive eigenvalues λ₁,…,λₙ. Use size-k sets I for spectral indices and S for coordinates. Define λ_I=∏_(i∈I)λ_i, p_I=λ_I/e_k(λ), h_I=Σ_(j∉I)λ_j, and W_(S,I)=det U[S,I]. The Nyström trace error on S is
$$
F(S)=\operatorname{tr}\big(K-K[:,S]K[S,S]^{-1}K[S,:]\big).
$$
Sample I with probability p_I and then S with probability |W_(S,I)|². The marginal law of S is volume sampling, and the key identity is
$$
F(S)=\mathbb E[h_I\mid S].
$$
Thus for every convex function φ on the range of these errors,
$$
\mathbb E\phi(F(S))\le\mathbb E\phi(h_I).
$$
A diagonal orientation of the spectrum attains equality, including for every convex moment. For strictly convex φ, equality holds exactly when K is diagonal in the coordinate basis.

## Conditional expectation identity

The matrix W is the exterior power of U, hence unitary; its squared entries in each column sum to one. Cauchy–Binet gives ∑_I λ_I|W_(S,I)|²=det K[S,S], which proves the marginal law. Schur complementation gives
$$
\det K[S,S]\,F(S)=\sum_{j\notin S}\det K[S\cup\{j\},S\cup\{j\}].
$$
For a fixed spectral (k+1)-set J, apply Cauchy–Binet to the determinants on the right, then sum their squared minors over j. Expanding each determinant of U[S+j,J] along its appended row makes it the inner product of that row of U[:,J] with a cofactor vector, up to conventions for complex conjugation and row order. Because these columns are orthonormal, the sum of squared moduli over all rows is the squared norm of the cofactor vector. Rows already in S contribute zero. The result is
$$
\sum_{j\notin S}|\det U[S+j,J]|^2
=\sum_{\substack{I\subset J\\ |I|=k}}|W_{S,I}|^2.
$$
Substituting this identity and exchanging sums yields ∑_I λ_I|W_(S,I)|²h_I. Divide by the principal determinant to obtain the conditional mean formula. Conditional Jensen proves the convex comparison.

## Sharp variance and equality

Write p_min=min_I p_I and p_max=max_I p_I. The variance gap obeys
$$
p_{\min}\binom{n-2}{k-1}\sum_{i\ne j}|K_{ij}|^2
\ \le\ \operatorname{Var}(h_I)-\operatorname{Var}(F(S))
\ \le\
p_{\max}\binom{n-2}{k-1}\sum_{i\ne j}|K_{ij}|^2 .
$$
Indeed the law of total variance writes the gap as
$$
\sum_S\min_{c\in\mathbb R}\sum_I p_I |W_{S,I}|^2(h_I-c)^2 .
$$
Pull p_min or p_max outside each minimum to bound the gap from below or above. Upon removing p_I, the inner linear weights sum to one. For D=diag(h), the sum of the unweighted minima is
$$
\operatorname{tr}(D^2)-\sum_S (WDW^*)_{SS}^2
=\sum_{S\ne T}|(WDW^*)_{ST}|^2.
$$
On the k-th exterior power, WDW*=(tr K)I−K^[k], where the additive compound K^[k] applies K to one factor at a time and sums. Its off-diagonal entry from T to S is zero unless S and T differ by one element, in which case it equals the associated entry K_ij up to sign. Each ordered pair i≠j appears in exactly binom(n−2,k−1) such entries. This proves the comparison.

For a strictly convex φ, equality in conditional Jensen for each S is equivalent to the conditional variance vanishing, because all spectral weights are positive and the distributions are finite. The lower deficit bound therefore forces K to be diagonal. Diagonal K makes h_I equal to the corresponding coordinate error and attains the bound.

In particular the exact maximum variance over all coordinate orientations with spectrum λ is
$$
\sum_i\lambda_i^2 q_i+2\sum_{i<j}\lambda_i\lambda_j q_{ij}
-\left((k+1)\frac{e_{k+1}(\lambda)}{e_k(\lambda)}\right)^2 ,
$$
where q_i=e_k(λ omitting i)/e_k(λ) and q_ij=e_k(λ omitting i,j)/e_k(λ). These are the one- and two-index exclusion probabilities for I. The same coupling furnishes a spectral bound for absolute centered moments and exponential moments.
