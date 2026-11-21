# Random Ritz conditioning and exact laws for normal matrices

The results answer two scoped questions about random Ritz values for normal matrices. The first gives both conditioning and expected-area bounds at Krylov dimension two and allows arbitrarily clustered input eigenvalues. The second gives the full joint law of the unordered Ritz values when the Krylov dimension is one less than the number of distinct eigenvalues. [Simons Workshop, Problems 3.5 and 3.6](https://arxiv.org/html/2602.05394v3#S3.SS3)

## Polynomial conditioning for two-step random Ritz compressions

Let \(A\) be a nonscalar normal \(n\times n\) matrix, \(b\) a standard isotropic complex Gaussian, and \(H=Q^*AQ\) for an orthonormal basis of \(\operatorname{span}\{b,Ab\}\). Let \(\kappa_V\) be the best spectral-norm condition number of an eigenvector basis. There is an absolute \(C\) such that for \(K\ge2\),
\[
 \Pr\{\kappa_V(H)>K\}\le C nK^{-1/2}.
\]
For real normal \(A\) and a standard real Gaussian, the bound is \(C n^{1/2}K^{-1/4}\). In particular \(O(n^2\eta^{-2})\) and \(O(n^2\eta^{-4})\), respectively, suffice at failure probability \(\eta\). Write \(D>0\) for the spectral diameter. For \(0<\varepsilon\le D\) the two corresponding expected planar areas of the spectral-norm \(\varepsilon\)-pseudospectrum are bounded by
\[
 C n D^{3/4}\varepsilon^{5/4},\qquad
 C n^{1/2}D^{7/8}\varepsilon^{9/8}.
\]
These statements cover two-step compressions of the cyclic shift and other normal matrices, regardless of their minimum spectral separation. The real and complex starting distributions are specified separately.

### The discriminant as a polynomial in Gaussian data

Translate and rescale the eigenvalues \(\lambda_i\) to have diameter one and modulus at most two. In the complex case use an eigenvalue as the origin. In the real case use the least real part of the spectrum as the origin. Each imaginary part then has magnitude at most \(1/2\) by conjugate symmetry. Both transformations preserve eigenvectors and the Arnoldi space.

In an orthonormal eigenbasis put \(w_i=|b_i|^2\). In the nonorthogonal Krylov basis \(B=[b,Ab]\) one has
\[
 \det(zI-H)=\frac{\det(B^*(zI-A)B)}{\det(B^*B)}.
\]
Indeed the basis change from \(B\) to \(Q\) disappears in the determinant quotient. Cauchy–Binet gives the numerator as
\[
 \sum_{i<j}w_iw_j|\lambda_i-\lambda_j|^2(z-\lambda_i)(z-\lambda_j).
\]
Put \(V=\sum_{i<j}w_iw_j|\lambda_i-\lambda_j|^2\), and let \(S,P\) be the same sum with the extra factors \(\lambda_i+\lambda_j,\lambda_i\lambda_j\), respectively. The discriminant is \(F/V^2\), where \(F=S^2-4PV\) is homogeneous of degree four in \(w\). Almost surely \(V>0\), because each spectral weight is positive almost surely and the spectrum has at least two distinct points. Write \(W=\sum_iw_i=\|b\|^2\), so \(V\le W^2\).

For complex Gaussian \(b\), the variables \(w_i\) are independent mean-one exponential variables. A diameter pair \(a,b\) has \(|\lambda_a-\lambda_b|=1\). The coefficient of \(w_a^2w_b^2\) in \(F\) has modulus one by restriction to these two weights. The same coefficient is bounded below in modulus by \(1/\sqrt2\) in one of the real or imaginary parts \(f\) of \(F\). The \(L^2\)-norm of this real polynomial under the product exponential law is bounded below by an absolute constant. To see this, test it against the product of the two degree-two orthonormal Laguerre polynomials in \(w_a,w_b\). One such polynomial is \((x^2-4x+2)/2\). Orthogonality to degrees zero and one implies that this product picks out exactly the specified coefficient, multiplied by \(4\), since \(f\) has total degree four.

For real normal matrices, use a real orthogonal block decomposition. Each real eigenvalue on a one-dimensional block has the square of a standard normal coordinate as its weight. A conjugate pair on a two-dimensional rotation block has the same weight in each complex eigenvector, equal to half the squared length of the two real coordinates. Consequently \(F\) is real and is a homogeneous polynomial of degree eight in independent real Gaussian coordinates. We give a lower bound for its \(L^2\)-norm independent of the input matrix.

Choose a sufficiently small absolute \(\gamma>0\). If there is a block with imaginary part of magnitude at least \(\gamma\), choose a unit real coordinate vector in that block as the only nonzero start. Then only the conjugate pair contributes, each weight is \(1/2\), and \(|F|\ge(2\gamma)^6/16\). Otherwise the two extremal real parts are separated by at least \(1/2\), because the spectral diameter is one and all imaginary parts have magnitude at most \(\gamma\). Give one real coordinate in each of the extremal blocks value one and set all other coordinates to zero. With the imaginary parts set to zero the value of \(F\) is the sixth power of the distance between the two real parts, at least \(1/64\). The formula for \(F\) on those two blocks is a polynomial continuous in their imaginary parts and in the real part difference in the compact interval \([1/2,1]\). The same formula applies to a one-dimensional real block by treating its mass as two equal half-masses at a repeated eigenvalue. For a universal sufficiently small \(\gamma\), the actual value of \(|F|\) is at least \(1/128\). This proves in both cases that the degree-eight polynomial takes a value bounded below at a vector supported on at most two real coordinates of value one. Some degree-eight monomial in those coordinates must have coefficient bounded below, since there are at most nine such monomials. In the product Hermite basis this top-degree coefficient bounds \(\|F\|_{L^2}\) below. Lower-degree Hermite terms cannot affect the coefficient.

For either polynomial, the fixed-degree Carbery–Wright small-ball inequality bounds \(\Pr\{|f|\le t\}\) by \(C t^{1/4}\) for the complex-start quartic and by \(C t^{1/8}\) for the real-start polynomial. The measures here are log-concave product measures, and the \(L^2\)-norm lower bounds just proved make the constants uniform. [Carbery–Wright, Theorem 8](https://doi.org/10.4310/MRL.2001.v8.n3.a1)

### From the discriminant to the two bounds

In a unitary Schur basis the off-diagonal entry of \(H\) is at most two in magnitude. If its distinct eigenvalues are at distance \(g\), choose normalized eigenvector columns of the triangular matrix. Their condition number is at most \(1+4/g\). In detail, for an off-diagonal entry \(c\) the two eigenvector directions are \((1,0)\) and \((u,1)\) with \(|u|=|c|/g\). Their normalized Gram matrix gives condition number \(\sqrt{1+|u|^2}+|u|\le1+2|u|\). The gap satisfies \(g^2=|F|/V^2\). The zero-discriminant event has probability zero by the small-ball estimate. Thus \(\kappa_V(H)>K\) implies \(|F|\le C K^{-2}V^2\).

The event \(\kappa_V(H)>K\) depends only on the start direction, which is independent of \(W\) for either Gaussian law. Also \(\Pr(W\le2n)\ge1/2\) by Markov. Intersect with this event to obtain
\[
 \Pr\{\kappa_V(H)>K\}\le2\Pr\{|F|\le C n^4K^{-2}\}.
\]
In the complex case the event on the right forces the corresponding bound on \(|f|\). Applying the two small-ball estimates proves the stated tails.

In the normalized problem, for \(0<\varepsilon\le1\), the area is at most \(C\varepsilon\) deterministically. Indeed \(\sigma_{\min}(H-zI)<\varepsilon\) implies \(|z|\le3\) and hence \(|\det(H-zI)|\le5\varepsilon\), by the product of singular values. At least one of the two distances from \(z\) to a Ritz value is then at most \(\sqrt{5\varepsilon}\). Also the eigenbasis resolvent bound gives area at most \(2\pi\kappa_V(H)^2\varepsilon^2\). Combine the two bounds and put \(R=\varepsilon^{-1/2}\). For a tail bound \(C N K^{-a}\), integration gives
\[
 \mathbb E\min(\kappa_V(H)^2,R^2)
   =\int_0^R 2t\,\Pr(\kappa_V(H)>t)\,\mathrm dt
   \le C N R^{2-a}.
\]
Here \(N=n,a=1/2\) or \(N=n^{1/2},a=1/4\). The normalized area is at most \(C N\varepsilon^{1+a/2}\) in expectation. Scaling the original diameter back to \(D\) multiplies normalized area by \(D^2\) and replaces \(\varepsilon\) by \(\varepsilon/D\), giving the stated formulas.

## Exact Gaussian Ritz law with one missing spectral dimension

Let \(A\) be complex normal with \(m\ge2\) distinct eigenvalues \(\lambda_1,\ldots,\lambda_m\) of multiplicities \(r_i\), and put \(n=\sum_i r_i\). Start from an isotropic standard complex Gaussian and use Krylov dimension \(m-1\). For \(1\le i\le m\) define
\[
 f_i(z)=\prod_{j\ne i}(z-\lambda_j),\qquad
 c_i=\prod_{\substack{j<\ell\\j,\ell\ne i}}|\lambda_j-\lambda_\ell|^2>0.
\]
The monic Ritz polynomial is \(\sum_i a_i f_i(z)\). On the interior of the simplex \(\sum_i a_i=1\), the exact density with respect to \(\mathrm da_1\cdots\mathrm da_{m-1}\) is
\[
 \frac{\Gamma(n)\prod_i c_i^{r_i}}{\prod_i\Gamma(r_i)}
 \frac{\prod_i a_i^{-r_i-1}}{\big(\sum_i c_i/a_i\big)^n}.
\]
The unordered Ritz values are obtained by taking the roots of this polynomial. Thus the formula specifies their joint law, for arbitrary locations of the distinct eigenvalues and arbitrary multiplicities. This gives an explicit distributional case of Workshop Problem 3.6. Deterministic normal Ritz feasibility via Cauchy matrices is studied by Bujanović. [Workshop Problem 3.6](https://arxiv.org/html/2602.05394v3#S3.SS3) · [Bujanović, normal-matrix Ritz feasibility](https://doi.org/10.1016/j.laa.2013.02.014)

To derive the law, write \(W_i=\|P_i b\|^2\), where \(P_i\) projects to the \(\lambda_i\)-eigenspace. The orbit of one vector under powers of \(A\) stays in the orthogonal span of these \(m\) projections. In the orthonormal coordinates given by their normalized vectors, the Krylov matrix has row \(\sqrt{W_i}(1,\lambda_i,\ldots,\lambda_i^{m-2})\). Cauchy–Binet in the determinant quotient assigns to the subset omitting \(i\) a coefficient proportional to \(c_i\prod_{j\ne i}W_j\). Thus \(a_i=(c_i/W_i)/\sum_j(c_j/W_j)\). This also shows that every strictly positive simplex vector occurs by picking \(W_i\) proportional to \(c_i/a_i\). Deterministic starts with exactly \(m-1\) active eigenvalues give the vertices, and the closure of the attainable polynomials is the full simplex of combinations. These coefficients are unique since \(a_i=f(\lambda_i)/f_i(\lambda_i)\) for the monic Ritz polynomial \(f\).

The Gaussian weights \(W_i\) are independent gamma variables with shape \(r_i\) and unit rate. The independent variables \(Y_i=c_i/W_i\) therefore have densities \(c_i^{r_i}y^{-r_i-1}e^{-c_i/y}/\Gamma(r_i)\). Transform \(Y_i=s a_i\) with \(s>0\). The Jacobian in the simplex coordinates is \(s^{m-1}\). Integrating the product of the densities over \(s\), the remaining integral is
\[
 \int_0^\infty s^{-n-1}e^{-(\sum_i c_i/a_i)/s}\,\mathrm ds
 =\Gamma(n)(\sum_i c_i/a_i)^{-n},
\]
giving the claim.

For comparison, the companion law for compression onto a Haar hyperplane of the full space is a monic polynomial
\[
 \prod_i(z-\lambda_i)^{r_i-1}\sum_i A_i f_i(z),
\]
where \(A_i\) has the Dirichlet distribution with parameters \((r_1,\ldots,r_m)\). In an orthonormal basis completed by the unit normal, the determinant of the hyperplane compression of \(zI-A\) is its last principal cofactor. Dividing by \(\det(zI-A)\) gives the resolvent quadratic form of the unit normal, with coefficients \(A_i\) equal to its squared spectral projections. The Dirichlet claim is the normalized gamma formula. In the simple-spectrum case \(n=m\) the dimensions of the two compressions coincide. For \(m\ge3\), the Krylov density above tends to zero as one coefficient tends to zero with all the others bounded away from zero, whereas the Haar density is constant. At \(m=2=n\) both are uniform.
