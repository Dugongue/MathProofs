# Exact transport for rank-one spectral blocks of growing dimension

## GP-0302

For real or complex three-tensors with rational or Gaussian-rational entries, suppose the marginal Gram operators have rational eigenvalues, and every nonzero tensor block in their three-way orthogonal spectral decomposition has tensor rank one. Then product-orthogonal or product-unitary equivalence to an arbitrary second input is decidable in deterministic polynomial bit time. Spectral block dimensions and the connected components of the block support are unrestricted. The same algorithm works when exact rational spectral decompositions are supplied and checked. The rational-spectrum and rank-one-block predicates are directly recognizable. [Spectral tensor-isomorphism context](https://arxiv.org/html/2603.27128v1)

### Reduction to multiplicative equations

The marginal Gram operators transform by local conjugation. Compare their characteristic polynomials, then compute the spectral projectors over the input coefficient field by factoring the characteristic polynomials over $\mathbb Q$ and by Lagrange interpolation at the distinct eigenvalues. Reject unequal block supports. One can test and factor a nonzero rank-one block by matrix flattenings and pivot entries. Factoring the projected blocks in the original rational coordinate spaces gives source and target vectors $v_\ell,w_\ell$ for each occurrence $\ell$ of a mode in a supported triple. The choice of arbitrary exact factorization has no effect on the test below.

An equivalence must send $v_\ell$ to $z_\ell w_\ell$ for some nonzero scalars. Conversely this suffices when the products of the three scalars in each supported triple equal one and the maps on each spectral space can be chosen to be isometries. For the latter condition, compare the within-block Gram matrices of the two lists. Their zero patterns must agree. Set
$$
 m_\ell=\|v_\ell\|^2/\|w_\ell\|^2>0,\qquad
 R_{\ell j}=\langle v_\ell,v_j\rangle/\langle w_\ell,w_j\rangle
$$
when the entry is nonzero, with the first argument of the inner product conjugate linear. The required equations are $|z_\ell|^2=m_\ell$ and $\overline{z_\ell}z_j=R_{\ell j}$. Gram equality suffices because it makes the linear map on the span well-defined and isometric. For example, a relation among the source vectors has norm zero, so the corresponding relation among the scaled target vectors is zero by positive definiteness. Extend the isometry by arbitrary orthonormal bases of the complements.

On the graph of nonzero Gram links in each block, the equation gives $z_j=(R_{\ell j}/m_\ell)z_\ell$. Select a spanning tree of each component $c$ and express every scalar as $z_\ell=r_\ell z_c$ with $r_\ell$ rational or Gaussian rational and $m_c$ the squared norm ratio at the root. Check $|r_\ell|^2m_c=m_\ell$ and $\overline{r_\ell}r_jm_c=R_{\ell j}$ on all required links, thereby checking every cycle. The tensor equations now have the form $\prod_c z_c^{A_{ec}}=b_e$ for an integer incidence matrix $A$, with specified nonzero rational or Gaussian-rational $b_e$. Check $\prod_c m_c^{A_{ec}}=|b_e|^2$. Writing $z_c=\sqrt{m_c}\,u_c$ leaves a system
$$
 \prod_c u_c^{A_{ec}}=h_e,\qquad h_e=b_e/|b_e|.
$$

### Exact phase tests

Over $\mathbb R$ the $h_e,u_c$ are signs, so binary linear algebra decides solvability. Over $\mathbb C$ the $u_c$ range over the circle. Integer Smith normal form shows that the system is solvable exactly when $\prod_e h_e^{\lambda_e}=1$ for each basis vector $\lambda$ of the integral left kernel of $A$. Indeed row and column unimodular transformations act by invertible monomial maps, and every nonzero power map on the circle is onto.

The phase checks admit deterministic polynomial bit implementation, even when the exponents from Smith form are large. First test the exact squared identity
$$
 \prod_e (b_e/\overline{b_e})^{\lambda_e}=1 .
$$
Gaussian rational power-product equality reduces to Gaussian integer gcd computations without prime factorization. Clear the individual denominators and refine the list of nonunit Gaussian integer bases to pairwise coprime bases. When two distinct nonassociate current bases share a nonunit gcd, replace them by the gcd and their nonunit quotients, merging associates and tracking units. Each replacement decreases the sum of logarithms of norms of the normalized current bases. The algorithm stores each original base as a product of current basis powers and a unit. Pairwise coprimality makes equality equivalent to zero total exponent for each nonunit basis and equality of the product of the units. This uses polynomially many Euclidean gcd steps and polynomial-sized exponent encodings.

After the exact squared test the desired phase product is $1$ or $-1$. Distinguish them by approximating the factors $b_e/|b_e|$ with certified error and using repeated squaring. Polynomially many bits suffice: the logarithm of $1+\sum_e|\lambda_e|$ is polynomial, and approximating each operation to adequately many more bits bounds the output error by less than $1/2$. More explicitly, normalized complex approximations of unit numbers have multiplication error at most twice the sum of input errors plus the rounding error when the existing errors are at most one. Propagating this estimate over the polynomial number of squarings and multiplications needs only polynomial precision. Positive rational square roots can be approximated by interval bisection. Thus the algorithm decides the phase equations exactly. All matrices and lists are polynomial in the displayed tensor sizes, so the test has polynomial bit complexity independent of the sizes of the support components.
