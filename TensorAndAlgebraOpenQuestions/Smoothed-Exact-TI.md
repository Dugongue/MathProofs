# Exact tensor isomorphism under arbitrarily small rational perturbations

**Informal theorem.** Given a rational or Gaussian-rational \(n\times n\times n\) tensor \(A\), a rational radius \(\varepsilon>0\), and \(0<\delta<1\), one can sample an explicit independent-coordinate rational perturbation \(E\) with \(\|E\|_F\le\varepsilon\) such that, with probability at least \(1-\delta\), exact orthogonal or unitary isomorphism of \(A+E\) to every comparison tensor \(B\) is decidable in deterministic polynomial bit time. The success event depends only on \(A+E\). The algorithm returns FAIL outside its tested promise. The sampler uses polynomially many bits in the input lengths and \(\log(1/\delta)\).

This addresses the exact-decision form of the small-perturbation question in [Chizewer–Everett–Mithal–Qiao, Open Problem 2](https://arxiv.org/html/2603.27128v1#S1.SS5). The source also studies orbit distance and eigenvalue gap estimates. Here the perturbation distribution is an explicit rational grid.

## A polynomial defining the success event

Write \(G_i(T)=T_{(i)}T_{(i)}^*\) and \(p_i(z)=\det(zI-G_i(T))\). On the simple-spectrum locus choose ordered orthonormal eigenvectors of each \(G_i\) and let \(S(T)\) be the coordinate array in their tensor-product basis. Whether a coordinate vanishes is independent of eigenvector phases.

Treat the real and imaginary tensor coordinates as real polynomial variables \(a\). Let
\[
H(t_1,t_2,t_3)=\big\langle T,\,[\operatorname{adj}(t_1I-G_1)
 \otimes\operatorname{adj}(t_2I-G_2)\otimes\operatorname{adj}(t_3I-G_3)]T\big\rangle .
\]
At a triple of simple eigenvalues \((\lambda_1,\lambda_2,\lambda_3)\), this is \(|S(T)_{ijk}|^2\prod_\ell p'_\ell(\lambda_\ell)\). The product of \(H\) over all eigenvalue triples is a polynomial in \(a\): it is the determinant of multiplication by \(H\) in the rank \(n^3\) free algebra defined by the three monic \(p_i(t_i)\). Assign weight 1 to every coordinate of \(a\) and weight 2 to each \(t_i\). The weighted degree of \(H\) is \(6n-4\). In each determinant term the weights of the domain and range basis monomials cancel, so the product has degree at most \(n^3(6n-4)\). Multiply by the three discriminants. Each discriminant has degree \(2n(n-1)\). The resulting polynomial \(P\) has degree at most \(D=n^3(6n-4)+6n(n-1)\).

To see \(P\ne0\), take the real diagonal tensor \(T_0=\sum_i a_i e_i^{\otimes3}\), with positive \(a_i\) and distinct \(\lambda_i=a_i^2\). In a real neighborhood its three eigensystems admit analytic normalized eigenvectors agreeing with the standard bases at \(T_0\). Diagonal core coordinates are nonzero there. The derivative of a core coordinate with three distinct indices in the corresponding coordinate direction is 1. Each moving-basis contribution vanishes because it changes only one index of a diagonal tensor. For a coordinate \((i,j,j)\) with \(i\ne j\), the perturbation in that coordinate changes the \((j,i)\) entry of the first Gram matrix by \(a_j\) at first order. The derivative of the core coordinate is
\[
1+\frac{a_j^2}{\lambda_i-\lambda_j}=\frac{\lambda_i}{\lambda_i-\lambda_j}\ne0.
\]
The same argument applies when the unequal index is in either other mode. Thus each initially zero coordinate has a nonzero differential. A direction outside the finitely many differential kernels makes every core coordinate nonzero for sufficiently small nonzero displacement. This proves the real specialization and therefore the complex-coordinate polynomial are both nonzero.

Choose a power of two \(M>D/\delta\) and sample every real coordinate of \(E\) independently and uniformly from \(\{\varepsilon j/(2n^2M):0\le j<M\}\). In the complex case sample imaginary coordinates independently on the same grid. The Frobenius bound follows from the at most \(2n^3\) real coordinates. Translation and nonzero scaling preserve nonzeroness of \(P\), so the Schwartz–Zippel bound gives failure probability at most \(D/M\). The proof also applies when the radius is exponentially small in \(n\), provided its binary representation is charged.

## The exact decision algorithm

Check the two sets of three characteristic polynomials for equality. An isomorphism preserves them. If the source Gram spectra are simple, diagonalize both arrays with matched ordered eigenvalues. Check the source core for full support and return FAIL if the promise fails. If the source has full support and the target does not, return NO. Otherwise form the core coordinate ratios \(r_{ijk}=S(B)_{ijk}/S(A)_{ijk}\). Check unit modulus everywhere and check
\[
r_{ijk}r_{111}^{2}=r_{i11}r_{1j1}r_{11k}
\quad\text{for all }i,j,k.
\]
The equalities are necessary for factorization into three arrays of phases, and sufficient by taking the three arrays to be \(r_{i11}\), \(r_{1j1}/r_{111}\), and \(r_{11k}/r_{111}\). In the real case these entries are signs. An isomorphism must preserve matched eigenlines, which proves completeness. The constructed phases give an isomorphism, which proves soundness.

For the bit bound, use an adjugate column at each eigenvalue and normalize it by the positive square root of its squared norm. Characteristic polynomials, isolation data, and each eigenvector are polynomial-bit descriptions. Each zero, modulus, or displayed cross-product test involves a constant number of selected eigenvalues and square roots. All calculations for that test take place in a compositum of degree \(n^{O(1)}\) and polynomial coefficient bit size. Standard exact algebraic-number arithmetic, using polynomial factorization and root isolation, suffices. One can also construct a polynomial-size system for the constant number of selected algebraic numbers with their isolating intervals and use fixed-dimensional real algebraic decision. No test requires the common field of all eigenvalues.

**Scope.** This supplies a polynomial-bit exact algorithm under the stated independent rational-grid perturbations. Quantitative gap estimates and robust orbit-distance approximation under infinitesimal or prescribed noise are separate questions. The spectral reduction itself is from the cited paper. The full-support condition and bounded-field tests are the additional construction here. Publication priority has not been established.
