# Orthogonal tensor isomorphism over finite fields with nonsplit spectra

**Informal theorem.** For every finite field \(\mathbb F_q\), orthogonal isomorphism of two cubic tensors is exactly decidable in expected polynomial bit time whenever all three source Gram characteristic polynomials are squarefree. Orthogonality is for the standard symmetric bilinear form \(x^Ty\), including in characteristic two. With uniformly independent source entries and fixed \(q\), the promised sources have an explicit positive limiting fraction. Nonfailure answers are correct for every comparison tensor. The algorithm supplies witnesses on YES inputs.

This answers an average-case orthogonal version of [Chizewer–Everett–Mithal–Qiao, Open Problem 4](https://arxiv.org/html/2603.27128v1#S1.SS5). Distinct eigenvalues may lie outside the input field.

## Exact transporters over the input field

Let \(G_i(A)=A_{(i)}A_{(i)}^T\), and likewise for \(B\). An orthogonal isomorphism conjugates each of these Gram matrices, so reject unequal characteristic polynomials. Suppose the common polynomials \(f_i\) are squarefree. The space of each Gram operator is the regular module of \(E_i=\mathbb F_q[t]/f_i\). In fact, for each irreducible \(h\mid f_i\), its primary space is one-dimensional over \(E_h=\mathbb F_q[t]/h\). These spaces are mutually orthogonal: their idempotent projectors are polynomials in the self-adjoint Gram operator. The restricted forms are nondegenerate.

Choose a nonzero vector in each primary space to identify it with \(E_h\), both for \(A\) and \(B\). On each copy, self-adjointness of the action gives a form \(\operatorname{Tr}_{E_h/\mathbb F_q}(\beta uv)\) with unique \(\beta\ne0\), by nondegeneracy of the field trace pairing. Compute the two \(\beta\)'s by linear algebra. An intertwining isometry is multiplication by \(a\in E_h^\times\) with \(a^2=\beta_A/\beta_B\). Reject if any equation has no root. Fix one root per block to transport \(A\) into the Gram block system of \(B\). In odd characteristic all remaining choices are independent signs, one per irreducible block. In characteristic two each choice is unique.

The tensor product of the three direct-sum decompositions gives a direct sum of block triples. Compare the transported source and target blocks. In odd characteristic each pair of nonzero blocks must agree up to a sign, and that sign is the product of the three mode signs. These are linear equations over \(\mathbb F_2\), with matching zero blocks imposing no constraint. Solve and combine the resulting signs with the reference transporters. In characteristic two simply test equality. Factoring the \(f_i\)'s and the quadratic equations uses ordinary Las Vegas finite-field polynomial factoring. All extension degrees are at most \(n\), and tensor computations use the original vector-space coordinates. This proves the algorithm and its witness claim.

## Joint Gram law

All three Gram traces agree. Write \(H\) for the linear space of symmetric matrix triples with equal trace. Its dimension is \(D=3n(n+1)/2-2\). The distribution of the three Gram matrices is exponentially close in total variation to uniform on \(H\), for every fixed \(q\). Here is a bound uniform in the choice of nontrivial character of \(H\).

In odd characteristic, represent linear functionals on matrix triples by \((S_1,S_2,S_3)\) using trace pairings with symmetric matrices. Evaluating the character on the random Gram triple gives the additive character of a quadratic form in the \(n^3\) tensor entries. Its polar matrix, up to a nonzero scalar, is
\[
L=S_1\otimes I\otimes I+I\otimes S_2\otimes I+I\otimes I\otimes S_3.
\]
The squared modulus of the Fourier coefficient is at most \(q^{-\operatorname{rank}L}\). This follows by squaring the sum and changing variables to a difference; averaging the resulting linear character vanishes unless the difference lies in the polar kernel.

In characteristic two, represent dual coordinates by diagonal weights and off-diagonal weights separately. The polar matrix is the same expression for the three symmetric zero-diagonal matrices \(S_i\) of off-diagonal weights. The square terms from diagonal weights only affect the linear-character part of the bound. If all \(S_i=0\), the Fourier coefficient vanishes unless the sum of the three diagonal weights at every tensor index is zero, because squaring is a bijection of \(\mathbb F_q\). The exceptional weights are the three constant arrays with constants summing to zero, and give the trivial character of \(H\).

For each \(i\), triangularizing the other two matrices over an algebraic closure gives a block triangular matrix with \(n^2\) diagonal blocks \(S_i-\lambda I\), with \(\lambda\) depending on the block. Its rank is at least the sum of the diagonal-block ranks, by projecting to the last block and inducting on the upper-left block. Thus
\[
\operatorname{rank} L\ \ge\ n^2\min_{\lambda\in\overline{\mathbb F}_q}
                    \operatorname{rank}(S_i-\lambda I).
\]
If some minimum is at least 2, the sum of squared Fourier coefficients in this class is at most \(q^D q^{-2n^2}\). Otherwise each \(S_i\) is a scalar plus a matrix of rank at most one. For \(n>2\) that scalar is unique, since two different scalars would give \(n\le2\) by rank subadditivity. Frobenius therefore puts the scalar in \(\mathbb F_q\). There are at most \(q^{6n+3}\) such triples, and in characteristic two at most \(q^{3n}\) further choices of diagonal weights. Unless all three \(S_i\) are scalar, some \(S_i\) takes a vector outside its own line. Restricting \(L\) to that line tensored with the other two spaces and projecting away the line gives rank at least \(n^2\). When all three are scalar in odd characteristic, \(L\) is scalar and has full rank except for the trivial character. This bounds the second class by \(q^{9n+3-n^2}\). Fourier Plancherel and Cauchy–Schwarz give the claimed total variation bound
\[
\tfrac12\big(q^{D-2n^2}+q^{9n+3-n^2}\big)^{1/2}.
\]

## Counting the promised fraction

For a fixed squarefree monic \(f\) with \(r\) irreducible factors, a symmetric matrix of characteristic polynomial \(f\) is multiplication by \(t\) in \(\mathbb F_q[t]/f\), endowed with a trace form as above. Its orthogonal conjugacy classes correspond to coefficient square classes that give the standard form. In odd characteristic each component has two square classes and its norm maps the nonsquare class to a nonsquare. Hence exactly \(2^{r-1}\) coefficient classes give the standard discriminant. Every orthogonal centralizer has order \(2^r\). The number of matrices per \(f\) is \(|O(I_n)|/2\). In characteristic two each component has one square class, and the trace form is nonalternating because squaring is onto and the associated trace functional is nonzero. The nonalternating symmetric form in each dimension is unique over the finite field. The number per \(f\) is \(|O(I_n)|\), since the centralizer is trivial.

For odd \(q\), the standard orthogonal group orders give
\[
|O(I_n)|/(2q^{n(n-1)/2})\ \longrightarrow\ \prod_{j\ge1}(1-q^{-2j}).
\]
In characteristic two, the vector \(s=(1,\ldots,1)\) is fixed by every isometry because \(x^Tx=(s^Tx)^2\). In odd dimension its orthogonal complement is symplectic and the group is its symplectic group. In even dimension choose \(t\) with \(s^Tt=1\). There are \(q^{n-1}\) choices for the image of \(t\), all giving the same Gram matrix on \(\langle s,t\rangle\); the orthogonal complement is symplectic of dimension \(n-2\). Thus the group order is \(q^{n-1}|\operatorname{Sp}(n-2,q)|\), and \(|O(I_n)|/q^{n(n-1)/2}\) has the same limit. The nonalternating-form assertion follows by splitting off norm-one lines and absorbing any alternating planes into a norm-one line. For example, in a line with vector \(e\) and a symplectic plane with basis \(a,b\), the vectors \(e+a,e+b,e+a+b\) give an orthonormal basis. See also [Wall's treatment of classical groups and forms](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1C32E66782CEE040AC137340C96DEFF7/S1446788700027622a.pdf).

For each prescribed trace \(u\), there are \(q^{n-1}(1-1/q)+O(q^{n/2})\) monic squarefree polynomials of degree \(n\). Use the polynomial Möbius identity \(\mathbf 1_{\rm sf}(f)=\sum_{h^2\mid f}\mu(h)\). For \(\deg h=j\) with \(n-2j\ge1\), the required next coefficient of the monic quotient \(g\) in \(f=h^2g\) is fixed by \(u\) and \(h\). This gives \(q^{n-2j-1}\) possibilities per \(h\). The degree sums of \(\mu(h)\) are \(1,-q,0,0,\ldots\), from the inverse of the generating series of all monic polynomials. For \(n\ge3\) the omitted degree-zero quotient term contributes at most \(q^{n/2}\). The estimate is uniform in \(u\).

Under uniform measure on \(H\), conditional on the common trace, the three matrices are independent uniform symmetric matrices of that trace. There are \(q^{n(n+1)/2-1}\) matrices per trace. The preceding counts and the total variation estimate therefore give the promised limiting success fraction
\[
\left((1-q^{-1})\prod_{j\ge1}(1-q^{-2j})\right)^3.
\]
This is positive for every fixed \(q\), including \(q=2\). For fixed \(q\) and \(n>q\), squarefree spectra cannot split entirely over the base field, so the algorithm covers cases where splitting-based approaches cannot be applied.

**Scope.** The theorem gives a positive fraction for the orthogonal problem with a uniformly random first tensor. Arbitrary repeated spectra and the finite-unitary problem are outside the statement. The three-marginal estimate is an informal proof. Publication priority has not been established.
