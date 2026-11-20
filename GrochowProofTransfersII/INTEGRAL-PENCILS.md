# Principal ideals as unmarked integral tensor isomorphism in every degree

Let \(K\) be a number field of degree \(n\ge3\), and let \(O\subset K\) be an order given by an integral basis in a number-field presentation. The ideals below are nonzero full fractional \(O\)-ideals given by lattice bases. All three GL factors of an integral tensor are allowed to act. In particular the two slices may be mixed.

## Results

**A dimension-preserving reduction.** In deterministic polynomial time, construct a single integral generator \(\xi\in O\) of \(K\) whose conjugate root set has trivial projective stabilizer under \(\mathrm{GL}_2(\mathbb Z)\). For each ideal \(I\), take
\[
T_I=(1_n,M_I(\xi))\in\mathbb Z^2\otimes\mathbb Z^n\otimes\mathbb Z^n,
\]
where \(M_I(\xi)\) represents multiplication by \(\xi\) on the supplied basis of \(I\). Then \(T_I\) and \(T_J\) are isomorphic exactly when \(J=uI\) for some \(u\in K^\times\). Setting \(J=O\) gives a many-one reduction from principality to unmarked tensor isomorphism over the integers at the literal format \(2\times n\times n\), for every \(n\ge3\). The reduction works for nonmaximal orders and arbitrary full ideals.

**Witnesses and orientation.** For these tensors the possible slice matrices are precisely \(1_2\) and \(-1_2\) whenever the ideals are equivalent. All remaining transformations are determined by the scalar \(u\) and the chosen slice sign. For determinant-one tensor isomorphism with positively oriented lattice bases, the scalar is required to have positive norm. For odd \(n\) this yields the same decision problem because \(-u\) changes the sign and takes \(I\) to the same \(J\). Thus the same many-one reduction works with all three factors restricted to \(\mathrm{SL}\) in every odd degree \(n\ge3\).

**A two-lattice criterion.** More generally, integral square pencils with irreducible determinant of degree \(n\ge3\) have at most \(2n\) candidate integral slice changes, computable before any lattice-equivalence tests. For each slice change, the remaining question is simultaneous multiplication of two explicitly constructed fractional lattices by a single element of a number field. If the four lattices are presented as invertible ideals of a common order, this is a single principality test after an ideal equality check. This gives an upper reduction to principality on that family.

## Finding a generator with no affine symmetry

Take an integral basis \(e_0,\dots,e_{n-1}\) of \(O\) and trial elements \(\theta_t=\sum_{i=0}^{n-1} t^i e_i\) for consecutive nonnegative integers \(t\). The generator must avoid two kinds of exceptional subspaces.

For distinct embeddings of \(K\) into an algebraic closure of \(\mathbb Q\), their difference is a nonzero linear map on \(K\). Its value on \(\theta_t\) is a nonzero polynomial of degree at most \(n-1\). Avoiding its roots for all pairs ensures all \(n\) conjugates are distinct, hence that \(\theta_t\) generates \(K\). This excludes at most \((n-1)\binom{n}{2}\) trial values.

An affine rational symmetry of a finite set of at least two roots must be the identity or a reflection. A nonidentity such symmetry has finite order, which forces its rational slope to be \(-1\). A reflection of the roots of a primitive \(\theta\) sends \(\theta\) to \(b-\theta\in K\) and induces a nonidentity field involution \(\gamma\). It requires \(\theta+\gamma(\theta)\in\mathbb Q\). The map \(1+\gamma\) is onto the fixed subfield, of degree \(n/2\) over \(\mathbb Q\). In even degree \(n\ge4\), its inverse image of \(\mathbb Q\) is a proper linear subspace. Each such subspace excludes at most \(n-1\) values of \(t\), since the basis spans \(K\). There is no involution in odd degree, and there are fewer than \(n\) nonidentity automorphisms in any degree. Hence it suffices to try \(1+(n-1)(\binom n2+n-1)\) values.

Both tests are exact over \(\mathbb Q\). Find the degree via linear dependencies among powers of \(\theta_t\). For a primitive element with minimal polynomial \(f\), the only possible reflection is \(x\mapsto 2\operatorname{Tr}(\theta_t)/n-x\), by averaging over its roots. Compare coefficients to test whether it preserves \(f\) up to leading sign.

## Removing the remaining projective symmetries

Write \(\theta\) for the accepted generator and \(f\) for its minimal polynomial. A rational fractional-linear map preserving the root set of \(f\) sends \(\theta\) to a root \(\eta\in K\). Find all these roots by factoring \(f\) over \(K\). For each, solve the rational linear equation
\[
a\theta+b=\eta(c\theta+d)
\]
for \(a,b,c,d\). A nonzero solution has nonzero denominator and determinant. A zero denominator would force \(c=d=0\) and then \(a=b=0\). A zero determinant with a nonzero denominator would give a rational value for \(\eta\).

There is at most one projective solution per root. An invertible rational fractional-linear transformation fixing \(\theta\) gives a polynomial of degree at most two vanishing at \(\theta\) after cross multiplication. Since its minimal polynomial has degree at least three, the transformation is scalar. Comparing two candidate maps by composing one with the inverse of the other proves uniqueness. Every solution induces a rational field automorphism by sending \(\theta\) to \(\eta\), and hence preserves all the conjugate roots. Clear denominators to give an integral representative for each solution. Each nonidentity solution has \(c\ne0\) because affine symmetries were removed.

Let \(M=1+\prod |c|\) using these nonidentity representatives, with the empty product equal to one. Then \(M\ge2\) and each \(c\) is coprime to \(M\). Set \(\xi=M\theta\). Dilation conjugates each rational projective matrix to one represented by
\[
\begin{pmatrix}Ma&M^2b\\c&Md\end{pmatrix}.
\]
If \(U\) were a proportional integral matrix with lower-left entry \(u\), its first-row entries \(v,w\) would satisfy \(cv=Mau,\ cw=M^2bu\). Coprimality forces both \(v,w\) to be divisible by \(M\), so \(\det U\) is divisible by \(M\). Thus no nonidentity symmetry of the rescaled roots has a unimodular representative. This argument uses no prime search and assumes no bound on the discriminant of the field.

## Recovering each ideal witness

Write a tensor isomorphism as
\[
(1_n,M_J)=
\bigl(P(a1_n+bM_I)Q^{-1},\ P(c1_n+dM_I)Q^{-1}\bigr)
\]
with \(P,Q\in\mathrm{GL}_n(\mathbb Z)\) and \(\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb Z)\). From the first slice, \(a1_n+bM_I\) is invertible over the integers. The second slice shows that \(M_J\) is conjugate by \(Q\) to \((c1_n+dM_I)(a1_n+bM_I)^{-1}\). Their eigenvalues are the conjugate root set of \(\xi\) and its fractional-linear image, so the slice matrix induces a projective symmetry. The only such projective element is the identity, and its unimodular representatives are \(1_2,-1_2\).

Consequently \(Q\) intertwines the two multiplication-by-\(\xi\) maps. Under the lattice bases it extends to a rational linear map on \(K\). Commuting with \(\xi\) makes this a \(K\)-linear map on a one-dimensional \(K\)-space, hence multiplication by \(u\in K^\times\). Unimodularity is exactly \(uI=J\). Conversely every such scalar produces \(Q\), and choosing slice sign \(\epsilon\) determines \(P=\epsilon Q\). This proves all witness claims. In positively oriented bases the sign of \(\det Q\) is the sign of the norm of \(u\). A positive-norm scalar gives a determinant-one witness using the positive slice sign.

## Arbitrary irreducible pencils

Let \((A,B)\) be the source and \((C,D)\) the target, with irreducible binary determinants of degree \(n\ge3\). Put \(X=A^{-1}B\), \(Y=C^{-1}D\). Both characteristic polynomials are irreducible of degree \(n\). Identify their rational column spaces with the fields \(K_s=\mathbb Q(\theta),K_t=\mathbb Q(\eta)\), so \(X,Y\) act as multiplication by \(\theta,\eta\). In these coordinates let \(I_s,J_s\) be the images of \(\mathbb Z^n,A^{-1}\mathbb Z^n\), and \(I_t,J_t\) the images of \(\mathbb Z^n,C^{-1}\mathbb Z^n\).

For slice matrix \(H=(a,b;c,d)\) put \(s=a+b\theta\), \(\theta_H=(c+d\theta)/s\). The first mixed slice \(A_H=A(a1_n+bX)\) replaces \(J_s\) by \(s^{-1}J_s\). The normalized second slice is multiplication by \(\theta_H\).

Factor the characteristic polynomial of \(Y\) over \(K_s\) to list its possible values at \(\theta_H\). Each root gives at most one projective \(H\) by the same linear equation and degree argument. The primitive integral representative gives two signed candidates if it is unimodular, and none otherwise. For each of the at most \(2n\) candidates, transport the source lattices to \(K_t\) by the isomorphism sending \(\theta_H\) to \(\eta\). A witness exists exactly when a common scalar takes \(I_s,s^{-1}J_s\) to \(I_t,J_t\). Indeed the normalized intertwiner \(Q\) must match the domain lattices. Then \(P=CQA_H^{-1}\) is integral unimodular precisely when the second lattice equality holds. This also reconstructs every witness.

For invertible ideals of a common order, the scalar exists precisely when \(I_tI_s^{-1}\) and \(J_t(s^{-1}J_s)^{-1}\), taken after transport to the common field, are equal and principal. Ordinary rational and integer linear algebra handles the other operations in polynomial bit complexity. The dilation adds only the sum of the bit lengths of the lower-left entries. The lower reduction computes no class group and makes no principality call.

## Relation to prior work and verification

[Grochow, Qiao, Stange and Sun, Theorem 1.7](https://arxiv.org/html/2611.00735v1) give polynomial-time equivalence between binary cubes and real-quadratic principality. Latimer–MacDuffee identifies integral similarity with ideal classes, and [Wood](https://arxiv.org/abs/1008.4781) gives an arithmetic parametrization for pairs with a fixed binary form. Here the effective rigid generator forces the full integral slice action to preserve a chosen field element, giving a uniform unmarked reduction in every degree at least three. The upper criterion uses the field representation to list the residual slice changes. Factoring uses [Lenstra's number-field algorithm](https://ir.cwi.nl/pub/2541/2541D.pdf).

The pinned [Davis–Astra denominator proof](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/pham-denominator-degree/PROOF.md) uses cross multiplication and a degree cutoff to force a rational identity from finite data. The same step here kills a degree-two identity using one element of degree at least three. The dilation then distinguishes rational symmetries from unimodular symmetries. These results have written proofs. The Lean companion checks that the dilation divisibility certificate excludes a unit determinant.

## Concrete controls

In the cyclic cubic field with \(f(x)=x^3+x^2-2x-1\), the original root set has nontrivial integral slice symmetries. Its other two roots are obtained by iterating \(x\mapsto x^2-2\). Scaling by two gives nonidentity primitive matrix determinants of absolute value four. In the biquadratic field \(\mathbb Q(\sqrt2,\sqrt3)\), the example \(\sqrt2+\sqrt3\) has an affine reflection. The generator \(\sqrt2+\sqrt3+\sqrt6\) has no affine reflection, and scaling yields no nonidentity unimodular symmetry. The replay checks both fields with rational arithmetic.

A negative principality instance uses \(O=\mathbb Z[\theta]\) with \(\theta^3=7\), an irreducible cubic by Eisenstein. The kernel of \(O\to\mathbb F_2,\ \theta\mapsto1\) has basis \(2,\theta-1,\theta^2-1\) and index two. If principal, a generator must have absolute norm two. For \(a+b\theta+c\theta^2\) the norm is \(a^3\) modulo seven, since multiplication in \(O/7O\) is upper or lower triangular with constant diagonal \(a\) in the power basis. Cubes modulo seven exclude both two and minus two. Thus the ideal is nonprincipal. The two tensors from this ideal and \(O\) are inequivalent in format \(2\times3\times3\), for the ordinary and determinant-one actions.
