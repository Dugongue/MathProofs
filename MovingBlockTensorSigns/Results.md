# The third determinant in tensor isomorphism over F₃

**Status.** Informal proofs and a research audit for the finite-field part of Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9. The unrestricted polynomial-time many-one reduction from SL-TI to one two-sign TI instance remains open in this work. The two exact representations below retain the same transporter in all three tests. Both change the target comparison problem.

## 1. One moving complement, on the same transporter

Let \(T,S\) be explicit three-tensors over \(F=\mathbb F_3\). A transporter is a triple \((g_1,g_2,g_3)\) of invertible mode maps taking \(T\) to \(S\). Two-sign TI requires \(\det g_1=\det g_2=1\). SL-TI also requires \(\det g_3=1\).

**Proposition.** In polynomial time one can add a single subspace complement condition to the two-sign comparison. The resulting comparison is exactly SL-TI, on arbitrary raw pairs. The condition is
\[
 D(g_3)i(F^m)\oplus\ker p=E,
 \qquad D(g_3)=I_m\oplus g_3^{\oplus r},
\]
where \(E,p,i,m,r\) are explicit in the input format. Both sign tests and the complement condition refer to the same transporter.

To construct it, first form a polynomial-size affine matrix pencil \(P(X)\) with determinant \(1+\det X\). Here is a size argument. For a matrix with upper-left entry \(a\), first row and column tails \(R,C\), and trailing principal block \(M\), the characteristic polynomial satisfies
\[
 \chi_X(t)=\chi_M(t)\bigl(t-a-R(tI-M)^{-1}C\bigr).
\]
Expanding the inverse at infinity gives transition coefficients \(1,-a,-RM^jC\) between the successive vectors of characteristic-polynomial coefficients. For a coefficient indexed by distance from the leading term, the contribution of \(-RM^jC\) comes from the coefficient \(j+2\) positions earlier in the shorter vector. Each \(RM^jC\) is a path sum of a layered graph with one layer per matrix multiplication, width at most the matrix dimension, and affine edge labels. Only \(j<n\) is needed for \(n\times n\) matrices. Layer the successive coefficient vectors, replacing each transition by its path-sum graph. The total graph has polynomial size. Use the constant coefficient times \((-1)^n\), and add the constant path of weight one. This yields an acyclic affine-labelled graph with path sum \(1+\det X\) from \(s\) to \(t\). If \(A(X)\) is its weighted adjacency matrix in topological order, then \(I-A(X)\) is unit triangular and
\[
 P(X)=
 \begin{pmatrix}
 I-A(X)&e_t\\
 -e_s^{\mathsf T}&0
 \end{pmatrix}
\]
has the required determinant by the Schur-complement formula. In dimension zero the determinant is one.

Write \(P(X)=C_0+\sum_{a,b}X_{ab}B_{ab}\). Use one direct-sum copy of \(F^n\) for each nonzero coefficient \((B_{ab})_{uv}\). On that copy, \(i\) sends a vector \(z\) to \(z_v e_b\), and \(p\) sends a vector \(w\) to \((B_{ab})_{uv}w_a e_u\). The constant summand uses \(C_0\) in \(i\) and the identity in \(p\). Thus \(pD(X)i=P(X)\). Since \(P(I)\) is invertible, \(i\) is injective and \(p\) is surjective. For any invertible \(g_3\) the displayed complement condition says exactly that \(pD(g_3)i\) is invertible. Over \(F\) this is equivalent to \(\det g_3=1\), since \(1+\det g_3\) is \(2\) or \(0\).

The ordinary comparison one would need is the existence of a compatible map taking a moving subspace to *some* complement. A fixed tensor mark typically asks the map to take one marked subspace to one specified subspace.

## 2. An exact succinct polynomial comparator for concise tensors

Write \(T\in U\otimes V\otimes W\), and suppose the flattening \(i_T:W^*\to U\otimes V\) is injective. If \(z\) ranges over \((U\otimes V)^*\), its coordinate slice forms \(f_i(z)=z(i_T e_i^*)\) are linearly independent. Use independent ambient variables \(z\), not an evaluation only on decomposable points. Define
\[
 M_T(z)=\det\bigl[f_i(z)^{3^j}\bigr]_{0\le j<\dim W,\;1\le i\le\dim W}.
\]
This polynomial has a polynomial-size arithmetic circuit. Compute powers by repeated cubing and the determinant, for example by the characteristic-polynomial construction above. Its degree may be exponential.

For indeterminates \(y_1,\ldots,y_n\), the Moore determinant is a nonzero scalar times one linear form from each projective ray in the \(F\)-span of the \(y_i\). Indeed, modulo any nonzero linear form with coefficients in \(F\), the columns are dependent by the Frobenius identity. The forms are distinct up to units, and their total degree \((3^n-1)/2\) is the determinant's degree. The determinant is nonzero because the permutation expansion has distinct monomials. After substitution of the independent \(f_i\), all the factors remain nonzero distinct rays. Unique factorization therefore recovers the span of the \(f_i\) from \(M_T\).

For a transporter \((a,b,h)\), the flattening of \(S\) is \((a\otimes b)i_T h^{\mathsf T}\). Consequently
\[
 M_S(z)=\det(h)\,M_T((a\otimes b)^*z).
\]
Conversely, if \(M_S(z)=M_T((a\otimes b)^*z)\), the recovered spans agree under \(a\otimes b\), so there is a unique \(h\) satisfying the flattening equation. Nonvanishing and the covariance identity give \(\det h=1\). Thus in the concise third mode the two signed maps \(a,b\) and equality of these two polynomials on their shared change of variables suffice. A rank mismatch rejects directly. A deficient third mode has a free determinant correction on the complement after any transporter, so ordinary two-sign TI already suffices in that branch.

This gives an exact comparison of succinct polynomials under a constrained substitution. The missing compilation is from that succinct comparison to one explicit two-sign three-tensor comparison while preserving the same \(a,b\). Equality of polynomials is weaker than isomorphism of chosen arithmetic circuits for them.

### Read-once branching programs

Even when the slice forms are the coordinate variables \(z_1,\ldots,z_n\), a read-once oblivious algebraic branching program for \(M(z)=\det[z_i^{3^j}]\) needs width at least \(\binom{n}{k}\) after the first \(k\) variables, in any order. Here a program multiplies matrices of univariate polynomials, with each variable confined to its own layer. Cutting at width \(w\) expresses its polynomial as a sum of \(w\) products of a prefix polynomial and a suffix polynomial, so the prefix–suffix coefficient matrix has rank at most \(w\).

For the Moore determinant, expand along the prefix's \(k\) columns. The term for a row set \(J\) is, up to sign, a product of two subdeterminants. Its prefix monomials use exactly the exponent set \(\{3^j:j\in J\}\), and its suffix monomials use the complementary exponent set. On each side, different row sets have disjoint monomial supports and each subdeterminant is nonzero by the permutation expansion. The two coefficient-vector families are therefore linearly independent, and the coefficient matrix has rank \(\binom{n}{k}\). A read-once oblivious branching program cannot provide a uniformly small canonical comparator for this route. This bound leaves general arithmetic circuits available.

## 3. Checks on proposed compilations

**Affine induced actions.** For \(n\ge2\), let \(\Phi\) be any affine matrix-valued map and suppose \(\Phi(I)=I\) and \(\Phi(gh)=\Phi(g)\Phi(h)\) on \(\mathrm{SL}_n(F)\). Write \(\Phi(I+X)=I+L(X)\). Then \(L(XY)=L(X)L(Y)\) for \(X=g-I,Y=h-I\). These differences span \(\operatorname{Mat}_n(F)\). Elementary transvections give \(E_{ij}\) for \(i\ne j\), and subtracting the two off-diagonal terms from \((I+E_{ij})(I+E_{ji})-I\) gives \(E_{ii}\). Bilinearity extends the identity to all \(X,Y\). It follows that \(\Phi\) is multiplicative on all matrices and \(\Phi(g)\) is invertible for every invertible \(g\). An affine pencil for \(1+\det g\) therefore cannot act as a fixed invariant quotient on all positive maps, even without a dimension bound. A moving corner is outside that assumption.

**Quotient shears.** Let \(K\subset E\) be a fixed kernel and let a lift induce \(g\) on \(E/K\). Any lift taking a marked subspace \(L\) to \(L'\) must take the entire image of \(L\) in \(E/K\) to the entire image of \(L'\). Shears acting trivially on the quotient cannot change that image. If all kernel maps and all shears are allowed, this quotient-image equality together with \(\dim(L\cap K)=\dim(L'\cap K)\) is sufficient, by choosing matching kernel bases and then adjusting the lifts of a quotient basis. Thus such shears solve an equality of subspaces, rather than the complement condition from Section 1. The same issue arises when an affine pencil is attached as a whole tensor. A variable substitution may preserve its determinant while lacking compatible constant row and column gauges on the whole pencil.

**Linear corners of unit groups.** A nonmultiplicative linear readout can still obey restrictions. Let \(A\) be a finite-dimensional unital \(F\)-algebra with radical \(J\), and let \(f:A\to\operatorname{Mat}_n(F)\) be linear. Suppose \(n\ge2\) and \(f(A^\times)=\mathrm{SL}_n(F)\), so all positive matrices are recovered and there is no leakage in this mode. Then \(f(J)=0\), and \(A/J\) must have at least three simple factors.

For the first claim, addition of an element of \(J\) sends units to units. Thus \(f(J)\) acts by translations preserving \(\mathrm{SL}_n(F)\). Any nonzero translation \(D\) fails: take \(v\) with \(Dv\ne0\), and choose \(g\in\mathrm{SL}_n(F)\) with \(gv=-Dv\). Such a \(g\) is obtained by completing \(v,-Dv\) to bases and calibrating on a second basis vector. Then \(g+D\) is singular. For the second claim, \(f\) is surjective because \(\mathrm{SL}_n(F)\) spans the whole matrix space. All fibers have the same size, so the unit density in \(A\) is at most
\[
 \frac{|\mathrm{SL}_n(F)|}{3^{n^2}}
 =\frac12\prod_{j=1}^n(1-3^{-j})\le \frac{8}{27}.
\]
Reduction modulo \(J\) preserves unit density because each element above a quotient unit is a unit. In a simple factor of \(A/J\), a full matrix algebra over a finite extension of \(F\), the unit density is \(\prod_{j=1}^m(1-3^{-ej})\) for extension degree \(e\) and matrix size \(m\). This is at least \((2/3)(1-\sum_{j\ge2}3^{-j})=5/9\). At most two such factors would give density at least \(25/81>8/27\), a contradiction. This applies to the stated linear readout from the whole unit group. Signed subgroups and pair-dependent selection of only some witnesses need separate arguments.

**Changing frames by elementary moves.** The top exterior orientation can be described by products of small extension classes or by a sequence of pairwise area-preserving moves. Ordinary isomorphism of displayed extension sequences pins the individual covector lines. Allowing changes of the intermediate objects gives a different comparison. In an algebra presentation for frame moves, replacing the varying evaluation homomorphism by a fixed quotient requires proving that the relevant evaluation kernels are in one automorphism orbit. Overlapping local relations can distinguish those kernels through their intrinsic intersection lines. A compact certificate for an elementary move is therefore insufficient to justify a single fixed tensor comparison.

**A fixed quotient for overlapping moves.** A stronger check uses the schedule \((12),(23),(12)\) on an ordered three-column frame. Name the successive frames \((a,b,c),(d,e,c),(d,f,h),(i,j,h)\). In the exterior square of the nine-dimensional tangent space on these symbols, mark the relation span
\[
 R=\left\langle a\wedge b-d\wedge e,\quad e\wedge c-f\wedge h,\quad d\wedge f-i\wedge j\right\rangle.
\]
Any evaluation into a three-dimensional space preserving these wedge equalities and taking the starting frame to a basis describes legal area-preserving moves. A proposed fixed-quotient implementation would obtain all useful evaluations by precomposing the reference evaluation for the zero-move path with automorphisms preserving \(R\), and by changing the output basis.

In \(R\) the only projective lines of rank four are the three displayed generators. Each generator is two independent wedges. A combination of two generators has rank six: their supports share one line, and the two terms incident to that line combine into one nonzero wedge, disjoint from the other two wedges. For a combination with all coefficients nonzero, \(a\wedge b\) and \(i\wedge j\) are disjoint from the remaining five symbols. On those five, the restriction to the coordinates \(c,e,f,h\) has rank four from the two disjoint wedges \(e\wedge c,f\wedge h\), and the rank on five symbols is at most four. The full rank is eight. Hence automorphisms preserving \(R\) permute the three rank-four supports, and so permute their pairwise intersection lines \(\langle d\rangle,\langle e\rangle,\langle f\rangle\).

The images of those three lines under the zero-move reference evaluation include a repeat, since \(d=a,e=b,f=b\) there. That repeat persists throughout its evaluation orbit even after changing the output basis. In a legal evaluation, \(d,e\) are a basis of \(\langle a,b\rangle\), while \(f\in\langle e,c\rangle\) is nonzero. Thus a repeat requires \(f\parallel e\), and the last pair \(i,j\) then spans \(\langle a,b\rangle\). The legal path with only the middle shear yields endpoint \((a,b+c,c)\), whose first two columns span a different plane. No evaluation producing this endpoint is in the reference orbit. This disproves that fixed-quotient implementation even when the initial basis can vary.

**Arithmetic of the base field.** For \(4\mid d\), the multiplication tensor of \(A=F[t]/(t^d)\) has eight distinct sign classes in its ordinary orbit over \(F\), and those classes merge over the algebraic closure. To see this, any multiplication isotopy \((p,q,r)\) has the form \((L_u\phi,R_v\phi,L_uR_v\phi)\). Evaluating at the unit gives \(u=p(1), v=q(1)\) as units and \(\phi=L_{u^{-1}}R_{v^{-1}}r\) as a unital algebra automorphism. In the ordered power basis, the multiplier determinants are \(x=u_0^d,y=v_0^d\), and the automorphism determinant is \(z=a_1^{d(d-1)/2}\), where \(\phi(t)=a_1t+\cdots\). The three covariant determinants are \((x^{-1}z^{-1},y^{-1}z^{-1},xyz)\). Over \(F\) all are one because the exponents are even. Over the algebraic closure the three powers can be chosen independently and the displayed change of coordinates is invertible on the multiplicative group. Thus an ordinary geometric orbit test or an everywhere nonzero algebraic determinant semi-invariant cannot provide a universal finite-field sign lock.

## 4. Relation to earlier work

The existing retained-sign compiler already carries two designated physical signs through an explicit bounded-order tensor system. The missing operation is an ordinary constraint for the moving complement of Section 1, or an alternative comparison such as the polynomial equality of Section 2. The earlier exponential exact-lifting bound applies when all valid source maps must lift and can be recovered on invariant subquotients. The present checks leave arbitrary pair-dependent decision reductions open, including constructions that retain only some witnesses.

- [Earlier sign projections and conjunction criterion](../TensorSignProjections/SignProjections.md)
- [Retained physical signs](../TensorSignChain/RetainedSigns.md)
- [Exact-lifting bounds](../TensorSignChain/ExactLifts.md)
- [Earlier projection selector results](../TensorProjectionSelectors/Results.md)
- [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/abs/2306.03135)
