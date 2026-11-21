# Intrinsic cube kernels and both scalar centroids over the ternary field

Let \(F=\mathbb F_3\). Let \(\beta:U\times U\to W\) be a symmetric bimap with spanning image, in specified bases, and set \(K=\ker(\operatorname{Sym}^2U\to W)\). Define its relation bimap as the symmetric bimap \(U^*\times U^*\to K^*\) evaluating all quadrics in \(K\) by polarization. The normalization uses \(v^2(\lambda,\mu)=\lambda(v)\mu(v)\). A transporter \((p,h)\) of \(\beta\) acts by \(p\) on \(U\) and by \(h\) on \(W\). Its auxiliary action on \(K\) is \(\operatorname{Sym}^2p|_K\). The target character is the product of the two raw determinants.

**Theorem.** The following tests give a deterministic polynomial-time many-one reduction of a prescribed combined determinant to one ordinary three-tensor isomorphism instance over \(F\). They are intrinsic and do not assume that a compatible decomposition of the input has been supplied.

1. Compute \(Q_3=\operatorname{Sym}^3 U/(U K)\) and the kernel \(X\) of the linear map \(U\to Q_3,\ u\mapsto u^3\). Require \(n=\dim X\) and \(r=\dim U/X\) both odd.
2. Set \(K_0=K\cap\operatorname{Sym}^2 X\). Require the natural projection \(K/K_0\to\operatorname{Sym}^2(U/X)\) to be an isomorphism.
3. For \(m_0:X\otimes K_0\to\operatorname{Sym}^3 X\), given by multiplication, let \(S=\ker m_0,\ C=\operatorname{coker}m_0\). Require \(\dim K_0+\binom{n+2}{2}\) even and \(\dim S,\dim C\le c\log_2(2+L)\), for fixed \(c>0\) and dense input length \(L\).

When \(m_0\) is an isomorphism, the sign imposes just a scalar comparison computable from the raw inputs. The stated class includes bimaps with **both** centroids scalar, zero common radicals for both bimaps, even ambient and odd label dimensions, and arbitrarily large odd \(r\). An explicit sampling construction of such instances is given below. There are normally isomorphic pairs in the class with no combined determinant-one transporter.

## 1. Determinant descent on the actual transporter

Cubing is \(F\)-linear in a commutative algebra in characteristic three. This explains the linear kernel construction in Test 1. Every transporter induces the symmetric powers of \(p\), preserves the relations \(K\) and their cubic products, and commutes with cubing. Thus it preserves the indicated kernel \(X\), and induces the map \(p_0\) on \(X\) and \(p_L\) on \(U/X\). Write \(p_K\) and \(p_{K_0}\) for its induced maps on the two relation spaces in chosen frames.

At endpoint \(A\), choose a frame of \(K_0\), a frame of \(U/X\), and lifts to \(K\) of the monomial frame of \(\operatorname{Sym}^2(U/X)\). Use the frame of \(K_0\) followed by these lifts as the frame of \(K\). The quotient action is exactly \(\operatorname{Sym}^2 p_L\) in the prescribed monomial frames. Its determinant is \((\det p_L)^{r+1}=1\) over \(F\), since \(r\) is odd. Hence \(\det p_K=\det p_{K_0}\).

In the raw monomial frame of \(\operatorname{Sym}^2 U\), let \(d_A\) be the determinant of the frame obtained by concatenating the chosen frame of \(K\) with lifts of the written \(W\) basis. Use \(d_B\) at the other endpoint. Comparing the determinant of \(\operatorname{Sym}^2p\) with this block triangular matrix gives
\[
 \det p\,\det h
   =\frac{d_A}{d_B}(\det p)^{\dim U+2}(\det p_K)^{-1}
   =\frac{d_A}{d_B}\det p_{K_0}.
\tag{1}
\]
Here \(\dim U=n+r\) is even and signs in \(F\) are their own inverses.

It remains to read the determinant of \(p_{K_0}\) through \(m_0\). Put \(k_0=\dim K_0\) and \(b_3=\binom{n+2}{2}\). Choose common image frames in each endpoint, and choose kernel and cokernel frames. Let \(a_A\) be the determinant of the frame of \(X\otimes K_0\) obtained by concatenating the kernel and lifted image frames. Let \(b_A\) be the determinant of the frame of \(\operatorname{Sym}^3X\) obtained by concatenating the image and lifted cokernel frames. Both are adapted-to-raw in the corresponding standard tensor or monomial frames. Make the analogous choices at \(B\). The image determinant cancels, giving
\[
 (\det p_0)^{k_0-b_3}(\det p_{K_0})^n
  =\frac{a_B/b_B}{a_A/b_A}\,\frac{\det p_S}{\det p_C}.
\]
The exponent \(b_3\) comes from the determinant of \(\operatorname{Sym}^3p_0\), whose diagonal monomials assign this exponent to each diagonal entry of a triangularization of \(p_0\). By the odd \(n\) and even \(k_0+b_3\) conditions, (1) becomes
\[
 \det p\,\det h=\frac{\eta_B}{\eta_A}\det p_S\det p_C,\qquad
 \eta_A=\frac{a_A}{b_A d_A}.
\tag{2}
\]
This is an equality on every actual transporter, in its specified raw coordinates. If \(m_0\) is invertible, \(k_0+b_3=4k_0\) and the two defect determinants are one. [Earlier first-syzygy formula](FirstSyzygyOrientationSeed.md)

For a positive instance of the three raw tests, retain the original bimap and the inclusion of \(X\). Use the truncated symmetric algebra of \(X\) through degree three to force the same \(p_0\) in degrees two and three. Add the inclusion of \(K_0\), a bilinear map realizing \(X\otimes K_0\), the map \(m_0\), the kernel inclusion and cokernel quotient. Thus these are induced maps on the same original witness. The exterior algebras of \(S,C\) with their degree-one and top-line inclusions force the two determinant multipliers. Their dimensions are polynomial by the logarithmic bounds. Multiply the two top-line multipliers using a bilinear line record scaled by \(\eta_A,\eta_B\) at the endpoints, then pin the resulting product to the desired sign. Zero-dimensional contributions use neutral pinned lines. Every such typed matching has the original combined character, and every original transporter of that character extends. The constantly many records of order at most three compile to one ordinary same-field instance. When \(m_0\) is invertible, just compare the required scalar ratio and use one ordinary symmetric-bimap comparison by the same compiler. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

These procedures use only linear algebra on spaces of degree at most three and the stated small exterior algebras. The raw tests are isomorphism invariant. They may be supplemented with a check of the two common radicals and both scalar-centroid conditions by linear equations. Moreover \(\dim W=\binom{n+1}{2}-k_0+nr\) is odd by Test 3, since \(\binom{n+1}{2}\equiv b_3\bmod2\) for odd \(n\). Thus \(F1\oplus U\oplus W\), with the cube-zero multiplication defined by \(\beta\) on positive-degree generators, has even dimension. Its algebra-isomorphism determinant is exactly the combined determinant on its two radical grades. The even-dimensional ternary rectangular multiplication cubic transfers this sign unchanged. [Exact cubic orientation](ExactCubicOrientationSeed.md)

## 2. Both scalar centroids and arbitrary odd complement

Start with odd-dimensional \(X\) and \(K_0\subset\operatorname{Sym}^2X\) with \(m_0\) invertible, and assume the only balanced operators of its relation bimap are scalars. Write \(Z_0=\operatorname{Sym}^2X/K_0\) and let \(\beta_0\) be the quotient bimap. It has zero common radical, since a radical vector \(x\ne0\) would give \(xX\subset K_0\) and the nonzero syzygy \(z\otimes xy-y\otimes xz\) for independent \(y,z\). Also \(K_0\) has full contraction support: containment in \(\operatorname{Sym}^2X'\) for proper \(X'\) would leave \(\operatorname{Sym}^3(X/X')\ne0\) outside its product image.

Choose any odd \(r\le\dim Z_0\), quadrics \(q_1,\ldots,q_r\) independent modulo \(K_0\), and \(E=\langle e_1,\ldots,e_r\rangle\). On \(U=X\oplus E\) take \(K\) generated as a quadratic subspace by \(K_0\) and
\[
 e_i e_j\ (i<j),\qquad e_i^2+q_i\ (1\le i\le r).
\tag{3}
\]
The projection of the new relations to \(\operatorname{Sym}^2 E\) is bijective, and \(W=Z_0\oplus(X\otimes E)\) in quotient coordinates.

The old graded quotient \(B_0=\operatorname{Sym}(X)/(K_0)\) has no cubic piece. First impose the monic relations \(e_i^2=-q_i\) over \(B_0\), giving an independent square-free monomial basis over \(B_0\). Then impose \(e_i e_j=0\). In degree three, multiplying each mixed monomial \(e_i e_j\) by the degree-one generators kills the mixed square-free cubic terms and imposes \(e_iq_j=0\) for \(j\ne i\), with no other relations on \(e_i Z_0\). Hence
\[
 Q_3=\bigoplus_i e_i\bigl(Z_0/\langle q_j+K_0:j\ne i\rangle\bigr).
\]
The cubes \(e_i^3=-e_i(q_i+K_0)\) survive independently, while cubes of \(X\) vanish. This identifies the raw cube kernel with \(X\).

In the quotient bimap the cross product is \(x\otimes e\); products of two \(E\)-vectors land in \(Z_0\). The common radical is zero by contracting against \(E\) and \(X\). Write a balanced input operator in blocks \(P:X\to X,\ B:E\to X,\ C:X\to E,\ D:E\to E\). Balancing on \(X\times X\) gives \(y\otimes Cx=x\otimes Cy\), so \(C=0\). Balancing on \(X\times E\) then gives \(\beta_0(x,Be)=0\) and \(Px\otimes e=x\otimes De\). Thus \(B=0\) and \(P,D\) are the same scalar. Surjectivity forces the same scalar on the output of a centroid pair.

In the relation bimap on \(X^*\oplus E^*\), a balanced \(A\) satisfies \(QA=A^{\mathsf T}Q\) for every symmetric relation matrix \(Q\). The \(K_0\) forms supported on \(X^*\) force the off-diagonal block from \(E^*\) to \(X^*\) to vanish by full support. The lower blocks of (3) span all symmetric forms on \(E^*\), so the other off-diagonal block vanishes as well. The \(X^*\) block is scalar by the assumption on \(K_0\), and the \(E^*\) block is scalar by testing coordinate squares and mixed forms. Denote these scalars by \(a,b\). A centroid operator must also preserve the relation space under \(Q\mapsto QA\), dual to the label action. Applying this to \(e_i^2+q_i\) gives \((a-b)q_i\in K_0\), forcing equality. The relation bimap has zero common radical by full support of its two diagonal projections.

The perfect \(m_0\) gives combined determinant one for every automorphism by (2). Reflecting one target label basis vector gives an ordinarily isomorphic pair with every transporter of negative combined determinant, so the constraint does not disappear by correction.


## 3. Polynomial expected generation over the fixed field

For every \(n\ge7\) with \(n\equiv1,5\pmod6\), let \(k_0=(n+1)(n+2)/6\). Sample \(k_0\) independent uniform quadrics in \(\operatorname{Sym}^2F^n\). The previous rank-count argument for first syzygies gives the following bound. For completeness, a rank-\(s\) syzygy coefficient matrix imposes \(\binom{n+2}{3}-\binom{n-s+2}{3}\) independent scalar equations on the sampled list, since its linear coefficients span an \(s\)-space. There are at most \(2\cdot3^{s(n+k_0-s)}\) rank-\(s\) matrices, and projectivizing divides by \(2\). At full rank the bound without the factor \(2\) gives at most \(1/2\) failure probability, and at lower positive ranks the exponent saving is \(s(n-s)(2n-s-3)/6\ge(n-1)(n-2)/6\). Thus the perfect multiplication map fails with probability at most
\[
 \frac12+(n-1)3^{-(n-1)(n-2)/6}.
\]
Perfection forces the list to be independent.

It remains to estimate the probability of a nonscalar balanced operator for these sampled relations. For fixed nonscalar \(A\) on \(F^n\), the linear map \(Q\mapsto QA-A^{\mathsf T}Q\) from symmetric to skew matrices has rank at least \(n-1\). Under the trace pairings its dual, up to the harmless sign convention, is \(B\mapsto AB-BA^{\mathsf T}\) from skew to symmetric matrices. These trace pairings are nondegenerate because the characteristic is odd. Choose \(v\) with \(v,Av\) independent, which exists for a nonscalar \(A\). At \(B=vw^{\mathsf T}-wv^{\mathsf T}\), the dual value is the symmetrized product of \(Av,w\) minus that of \(v,Aw\). Project the corresponding symmetric tensor modulo the line of \(v\). The second term vanishes, and the first term is multiplication by the nonzero linear form \(\overline{Av}\) on \(F^n/Fv\). That image has dimension \(n-1\), proving the bound. So the probability any nonscalar \(A\) balances all sampled quadrics is at most \(3^{n^2-k_0(n-1)}\), by a union bound over matrices. Its exponent is at most \(-23\) for \(n\ge7\).

The two good properties therefore hold simultaneously with probability above \(0.47\). They are both verified by Gaussian elimination, on the cubic products and on the balanced operator equations, respectively. After acceptance choose the \(q_i\) by extending a basis of \(K_0\) in the quadratic space. This gives a polynomial expected generation algorithm using exact tests over \(F\), for all the displayed \(n,r\). Here \(\dim Z_0=(n^2-1)/3\), so the allowed odd complement dimensions themselves grow without bound. [First-syzygy rank counting](FirstSyzygyOrientationSeed.md)

The raw tests use the cube kernel and the second and third homogeneous degrees. They do not use a split relation centroid to recover the complement. These are written proofs without Lean kernel verification.
