# Fixed-parameter recognition of cubic elementary-symmetric projections

These are informal proofs. The source asks in Section 4 how to recognize degree-three polynomials in \(\Sigma^{[k]}\mathrm{Sym}\), the sums of at most \(k\) scalar multiples of \(e_3\) applied to lists of homogeneous linear forms. The results below concern running time as \(k\) varies and take a dense coefficient vector as input. [Primary source, Corollary 3.4 and Section 4](https://arxiv.org/html/2509.05009#S4)

## 1. Fixed-parameter tractability over \(\mathbb F_4\)

**Theorem.** Over \(\mathbb F_4\), cubic membership in \(\Sigma^{[k]}\mathrm{Sym}\) is deterministically decidable in \(g(k)n^{O(1)}\) field operations for some function \(g\), where \(n\) is the number of variables and the exponent is absolute. The algorithm also finds the subspace certificate used for the exterior part of the test. Over \(\mathbb F_2\), the one-summand recognition problem is deterministically decidable in polynomial time.

**Reduction to an exterior three-form over \(\mathbb F_4\).** Write \(W\) for the span over \(\mathbb F_4\) of the nonsquarefree cubic monomials. Let \(W_0\subseteq W\) be the span over \(\mathbb F_2\) of all cubes of linear forms over \(\mathbb F_4\). We use the following facts.

1. Over any field of characteristic two, one can prescribe the first two elementary symmetric coefficients of a list of linear forms. For the second coefficient with first coefficient zero, use the formal identity
   \[
   \frac{1+t(a+b)}{(1+ta)(1+tb)}\equiv 1+ab\,t^2\pmod {t^3}
   \]
   for linear forms \(a,b\). Inverses can be replaced by third powers modulo \(t^4\) because \((1+tL)^4=1\bmod t^4\). A sum of quadratic monomials, with coefficients absorbed in one factor each, is obtained by concatenating lists. After selecting a single initial factor for the desired first coefficient, the same correction makes the second coefficient any prescribed quadratic.
2. Newton's identity in characteristic two gives \(E_3=E_1E_2+E_1^3+\sum_i L_i^3\). In \(\mathbb F_4\), the identity
   \[
    (1+tL)(1+t\omega L)(1+t\omega^2L)=1+t^3L^3
   \]
   for a primitive cube root \(\omega\) freely adds any cube of an existing form to \(E_3\) while leaving the first two coefficients unchanged. Consequently a single projected cubic is exactly a polynomial \(\ell Q+w\) with \(w\in W_0\), where \(\ell,Q\) range over all linear and quadratic forms.
3. The span of the cubes over \(\mathbb F_4\) is \(W\). For different \(i,j\), the cubes of \(x_i+a x_j\) with \(a=1,\omega\), after subtracting their diagonal terms, have the independent mixed coefficient vectors \((1,1)\) and \((\omega,\omega^2)\) on \(x_i^2x_j,x_ix_j^2\). The diagonal monomials are themselves cubes. Hence \(W=W_0+\omega W_0\).

For \(k\ge2\), the decision is therefore equivalent to whether the squarefree quotient \(\phi\) of the input cubic has an expression \(\sum_{i=1}^k\ell_i\wedge q_i\) in the exterior algebra, with \(q_i\) exterior two-forms. The necessary direction follows by quotienting by the squares of the variables. Conversely lift any such expression to a sum \(f_0=\sum_i\ell_i Q_i\) of ordinary products. The discrepancy \(f-f_0\) is in \(W\). Choose outer weights \(1,\omega\) for the first two summands and absorb their inverses in the quadratic factors, padding with zero products as needed. By \(W=W_0+\omega W_0\), both weighted summands can absorb the discrepancy using the single-projection description. This uses at most \(k\) summands.

Equivalently, \(\phi\) is an alternating three-form admitting a subspace \(H\) of codimension at most \(k\) on which it vanishes. One direction restricts all arguments to the common kernel of the linear factors. For the converse, choose a basis of the dual space whose first \(\operatorname{codim}H\) forms span the annihilator of \(H\). Every exterior monomial of \(\phi\) then contains at least one of those forms, and can be assigned to one to give the expression. We next give a deterministic fixed-parameter algorithm for this alternating-form decision over any fixed finite field.

**Rank of contractions and essential dimension.** Let \(A(v)=\iota_v\phi\) be the alternating bilinear form \((x,y)\mapsto\phi(v,x,y)\). Its kernel as a linear map in \(v\) is the radical \(\mathcal R=\{v\mid\iota_v\phi=0\}\). It can be computed by linear algebra, and \(\phi\) factors through \(V/\mathcal R\). This quotient preserves existence of an isotropic subspace of a given codimension bound: inverse images preserve codimension, while images of existing isotropic subspaces are isotropic and have codimension no larger. Call \(n-\dim\mathcal R\) the essential dimension.

Suppose \(B=A(v_0)\) has rank \(r\) over some extension field \(E\) and \(|E|>r+1\). If no \(B+tA(w_i)\) increases rank for any element \(t\in E\) or any basis vector \(w_i\) of \(V\), the essential dimension is at most \(r+\binom r2\). In fact, choose coordinates splitting off a nondegenerate \(r\)-dimensional block for \(B\) and its kernel \(N\). For two kernel coordinates \(a,b\), the minor of \(B+tA(w_i)\) using the nondegenerate block and row \(a\), column \(b\) has coefficient of \(t\) equal to the determinant of that block times \(A(w_i)_{ab}\). It vanishes as a polynomial, because its degree is at most \(r+1<|E|\) and it vanishes at every \(t\). Hence every \(A(w_i)\) vanishes on \(N\times N\). By linearity and alternation, a vector of \(N\) belongs to \(\mathcal R_E\) if its contraction vanishes on pairs from the \(r\)-dimensional block. These are only \(\binom r2\) linear conditions on \(N\). This proves the bound over \(E\), and linear rank and nullity agree with those over the base field.

**Algorithm.** Let \(q\) be the fixed field cardinality. For current budget \(k\ge1\) take \(s=16(k+1)^2\), and extend by degree \(d\), the smallest positive integer with \(q^d>2s\). Then \(s>2kd\), as \(d\le 6+2k\) for \(q\ge2\). The extension can be constructed by exhaustive search for an irreducible polynomial of degree \(d\), with cost depending only on \(k,q\).

If the essential dimension is at most \(s+\binom s2\), pass to the radical quotient and enumerate all its subspaces over the base field. This dimension bound depends only on the parameters. Otherwise, start with \(v_0=0\) over the extension. While its contraction has rank \(r<s\), try \(v_0+t w_i\) for all basis vectors \(w_i\) and all extension elements \(t\). Some trial increases rank, since failure would contradict the essential dimension bound just proved. After at most \(s\) increases obtain a contraction of extension rank at least \(s\). Expand its vector in a field basis of the extension of degree \(d\). The contraction is a linear combination of the resulting \(d\) base contractions. At least one base contraction has rank greater than \(2k\), because otherwise subadditivity bounds the extension rank by \(2kd<s\). Choose its vector \(v\).

Choose a \(2k+2\)-dimensional subspace \(X\) on which \(A(v)\) is nondegenerate, by taking \(k+1\) pairs from an alternating-form basis. For each subspace \(T\subseteq X\) of codimension at most \(k\) in \(X\), compute
\[
M_T=\{w\in V\mid\phi(w,T,T)=0\}.
\]
Every such \(M_T\) is proper. The restriction \(A(v)|_T\) is nonzero, since a restriction to codimension at most \(k\) can drop the rank of a bilinear form by at most \(2k\). Thus \(v\notin M_T\). Discard \(M_T\) of codimension more than \(k\). Otherwise recurse on \(\phi|_{M_T}\), reducing the budget by \(\operatorname{codim}_V M_T\). At budget zero test whether the remaining form is identically zero. If an isotropic solution \(H\) existed, the branch \(T=H\cap X\) is among the choices and \(H\subseteq M_T\). Conversely any recursive solution is an isotropic subspace in the original space with the required codimension. The number of choices at a node depends only on \(k,q\) and the recursion depth is at most \(k\). All major linear-algebra operations have polynomial complexity in \(n\) with absolute exponent. This gives the asserted running time and recovers \(H\).


**One summand over \(\mathbb F_4\).** If the exterior image \(\phi\) is nonzero, a possible linear factor \(\ell\) lies in
\[
\{\ell\in V^*:\ell\wedge\phi=0\}.
\]
This vector space has dimension at most three. Indeed, choose any independent members and make them the initial coordinate forms. Each exterior monomial of \(\phi\) must contain every such coordinate, because wedging by one coordinate injects the span of the monomials omitting it. A nonzero cubic monomial can contain at most three. Therefore we enumerate a bounded number of possible \(\ell\), and each outer weight \(c\in\mathbb F_4^\times\). Checking \(f/c=\ell Q+w\), \(w\in W_0\), is linear algebra over \(\mathbb F_2\). A basis for \(W_0\) can be computed from the description below.

If \(\phi=0\), identify \(f\in W\) with its coefficient matrix \(F\) on the monomials \(x_i^2x_j\), including the diagonal. Write \(F^*=F^{[2]\mathsf T}\) for transpose followed by entrywise squaring. A cube of a linear form with coefficient vector \(a\) gives the matrix \(a^{[2]}a^{\mathsf T}\). Such matrices span over \(\mathbb F_2\) the Hermitian matrices \(F=F^*\): coordinate forms give the diagonals, and the forms \(x_i+t x_j\), \(t=1,\omega\), give a basis for each off-diagonal pair after subtracting the diagonals. In particular \(W_0=\ker(F\mapsto F+F^*)\).

We claim \(f\) is a single weighted projected cubic precisely when \(\operatorname{rank}(F/c+(F/c)^*)\le2\) for some \(c\in\mathbb F_4^\times\), including \(f=0\). In the single-projection description, if \(\ell=0\) then this rank is zero. Otherwise \(\ell\wedge\bar Q=0\) in the exterior algebra, so \(Q=\ell m+S^2\) for linear forms \(m,S\). The square term follows because all nonsquarefree quadratic monomials are squares and the field is perfect. If \(a,b,d\) are the coefficient vectors of \(\ell,m,S\), the matrix of \(\ell Q\) is \(a^{[2]}b^{\mathsf T}+d^{[2]}a^{\mathsf T}\). Adding its Hermitian conjugate gives
\[
a^{[2]}(b+d)^{\mathsf T}+(b+d)^{[2]}a^{\mathsf T},
\]
which has rank at most two.

Conversely every Hermitian matrix of rank at most two has the form \(a^{[2]}b^{\mathsf T}+b^{[2]}a^{\mathsf T}\). One can diagonalize the Hermitian form by congruence to a diagonal with that many ones. A nonzero Hermitian form always has a vector with nonzero self-pairing, because an off-diagonal entry can be tested by the vectors \(e_i+t e_j\) and the trace \(\mathbb F_4\to\mathbb F_2\) is onto. Removing its orthogonal complement proves diagonalization. For a single one use \(a=e_1,b=\omega e_1\). For two ones use \(a=e_1+e_2,b=\omega e_1+\omega^2e_2\). Congruence preserves the form of the expression. Now \(F/c\) differs from the matrix of \(\ell^2m\), with coefficient vectors \(a,b\), by a Hermitian matrix in \(W_0\). This gives a single projection, proving the test and its polynomial running time.

**One summand over \(\mathbb F_2\).** On the polynomial ring define the derivation \(D(x_i)=x_i^2\). For any list over \(\mathbb F_2\), Newton gives the simpler identity \(E_3=E_1 E_2+D(E_2)\). To see this, in a cube of a linear form the \(x_i^3\) coefficient is its \(i\)-th coefficient and the \(x_i^2x_j\) coefficient is the product of its \(i\)-th and \(j\)-th coefficients. In the sum of cubes, the pure coefficients cancel \(E_1^3\). At each mixed pair, adding \(E_1^3\) leaves the coefficient of \(x_ix_j\) in \(E_2\). These are exactly the coefficients of \(D(E_2)\). Since \(E_1,E_2\) can be prescribed arbitrarily, the single-projection class is exactly \((\ell+D)Q\). For nonzero exterior image use the same wedge-annihilator enumeration of \(\ell\), followed by linear algebra for \(Q\). If the exterior image is zero, the coefficient matrix \(F\) on \(x_i^2x_j\) is realizable if and only if \(F\) is alternating or has rank at most one. The case \(\ell=0\) gives exactly the alternating matrices as \(D(Q)\). For \(\ell\ne0\), take \(\ell=x_1\) by a linear change over \(\mathbb F_2\), which commutes with \(D\). Write \(Q=Q_0+x_1Q_1+a x_1^2\) in the remaining coordinates. Then
\[
(\ell+D)Q=D(Q_0)+x_1(Q_0+D(Q_1))+a x_1^3 .
\]
Zero exterior image forces \(Q_0\) to have no mixed monomials. Hence \(D(Q_0)=0\), and the result is \(x_1\) times a square, with matrix rank at most one. Conversely any rank-one matrix corresponds to a linear form times a square and is obtained with that square as \(Q\). The zero case is included. \(\square\)


## 2. Exact and border projection classes coincide for characteristic-two cubics and separate for characteristic-three quartics

The source studies exact and border versions of the elementary-symmetric projection model separately. The difference can already occur for a single projection in characteristic three. In contrast, every fixed summand bound for cubics in characteristic two defines a closed class over an algebraically closed field. [Primary source, Section 3 and Section 4](https://arxiv.org/html/2509.05009#S3)

**Closedness for cubics.** Let \(K\) be algebraically closed of characteristic two. By the first two coefficient construction and Newton's identity, the set of individual cubic projections is \(\{\ell Q+w\mid\ell,Q,\ w\in W\}\), with \(\ell,Q\) linear and quadratic, respectively, and \(W\) the span of all nonsquarefree cubic monomials. The reasoning is the same as for the finite-field case above, except that every scalar is a cube in \(K\), so the span of cubes over \(K\) can be absorbed into a single projection. As in the exterior criterion, membership in \(\Sigma^{[k]}\mathrm{Sym}\) for \(k\ge1\) is equivalent to the squarefree image admitting an isotropic subspace of codimension at most \(k\).

This is a Zariski-closed condition. For \(k<n\), take the incidence of alternating forms and \((n-k)\)-dimensional subspaces on which the forms vanish. It is closed in the product of the affine space of forms and the Grassmannian, since the vanishing condition is restriction to the tautological vector bundle. Its image in the affine space is closed because the Grassmannian is projective. The cases \(k=0\) and \(k\ge n\) are immediate, and the preimage under the linear squarefree quotient remains closed. Therefore border and exact classes coincide for every summand bound in this cubic model.

**Strict quartic gap.** Let \(K\) be algebraically closed of characteristic three. In ten variables write \(z_1,z_2\) for two coordinates and \(U,V\) for disjoint four-dimensional variable blocks. Choose nondegenerate quadratics \(A(U),B(V)\), for example sums of the four coordinate squares. Then
\[
F=z_1^2 A(U)+z_2^2 B(V)
\]
belongs to the border of the single-projection class in degree four, but has no exact single projection, even after a scalar multiplier.

For clarity, we use the following quartic identity. Given a list of linear forms, put \(E_j=e_j(L_1,\ldots,L_m)\), \(P_4=\sum_i L_i^4\). Newton identities give
\[
E_4=E_1(E_3-E_1E_2)-E_2^2+E_1^4-P_4.
\]
The first three coefficients can be prescribed over every field of characteristic three using truncated products of linear factors. For degree \(j\le3\), the alternating product over subsets of \(j\) linear forms \(L_i\),
\[
\prod_{S\subseteq[j]}\left(1+t\sum_{i\in S}L_i\right)^{(-1)^{j-|S|}},
\]
has first positive-degree coefficient \((-1)^{j-1}(j-1)!\prod_i L_i\) at degree \(j\). This follows by taking the formal logarithm first over the rationals: inclusion-exclusion kills all terms not using every \(L_i\), and the remaining coefficient at degree \(j\) is the displayed integer. The identity specializes to characteristic three. Replace any inverse factor by eight copies of that factor modulo \(t^5\), since \((1+tL)^9=1\bmod t^5\). Hence one can add any desired homogeneous form in degree \(j\) without changing lower coefficients, and prescribe the three coefficients in increasing order.

Put
\[
Q_\epsilon=\epsilon^{-2}z_1^2+\tfrac12\epsilon^2 A(U).
\]
Over \(K(\epsilon)\), choose a list with \(E_1=z_2\), \(E_2=\sqrt{-1}\,Q_\epsilon\), and \(E_3=z_2 B+z_2E_2\). The identity gives \(E_4=z_2^2B+Q_\epsilon^2+E_1^4-P_4\). Appending four factors whose product is \(1+t^4 L^4\) adds \(L^4\) to \(E_4\) without changing lower coefficients. These factors exist for each \(L\) since \(1+s^4\) splits over \(K\). The correction needed to obtain
\[
F_\epsilon=z_2^2B+Q_\epsilon^2-\epsilon^{-4}z_1^4
\]
is a sum of signed fourth powers of forms already present and the form \(\epsilon^{-1}z_1\). The signs are absorbed by fourth roots in \(K\). No root of the rational parameter is needed. Thus \(F_\epsilon\) is a single projected elementary symmetric polynomial and has coefficientwise limit \(F\).

For the obstruction, let \(W\) be the degree-four span of \(x_i^3x_j\). The identity for \(E_4\) implies that any exact projected quartic, also after scaling, is congruent to \(\ell H+Q^2\) modulo \(W\), with \(\ell,H,Q\) of degrees \(1,3,2\). Here we absorb nonzero scalars into \(H\) and \(Q\) using algebraic closedness. The subspace \(W\), equivalently the span of all \(L^3M\) for linear \(L,M\), is preserved by linear substitution. We show that for every \(\ell\), the restriction of \(F\) to a suitable three-dimensional subspace of \(\ker\ell\) is \(t^2D(x,y)\) modulo \(W\), where \(D\) is a nondegenerate quadratic in two variables.

If \(\ell\notin\operatorname{span}(z_1,z_2)\), use \(\ker z_2\cap\ker\ell\). The functional \(z_1\) is nonzero on this intersection. There is a two-dimensional nondegenerate plane for \(A\) in \(U\cap\ker\ell\), since a hyperplane restriction in the four-dimensional nondegenerate space \(U\) has rank at least two. Join this plane to a vector in \(\ker z_2\cap\ker\ell\) with \(z_1=1\). Subtract a vector of the plane to make the new vector orthogonal to the plane for \(A\). This does not change its \(z_1\) coordinate. The restricted form is as asserted, up to a multiple of \(t^4\) that lies in \(W\). If \(\ell\) is in the span of \(z_1,z_2\), take any surviving direction in the two-coordinate space and a nondegenerate plane in \(U\) if \(z_1\) is nonzero on that direction, or in \(V\) otherwise. This also covers \(\ell=0\).

Finally, \(t^2D(x,y)\) is never congruent to a square of a quadratic modulo \(W\). Consider the full polarization, the coefficient of \(s_1s_2s_3s_4\) after substituting \(\sum_i s_i v_i\). It kills \(W\) by Frobenius. At \((a,a,b,b)\) the polarization of the square of a quadratic with symmetric matrix \(C\) is
\[
8\big(C(a,a)C(b,b)-C(a,b)^2\big),
\]
since \(2=-1\) in characteristic three. This is \(8\Lambda^2 C\) evaluated twice at \(a\wedge b\). The analogous polarization for \(t^2D(x,y)\) gives \(4\) times the mixed exterior form for the rank-one matrix on \(t\) and the nondegenerate matrix on \(x,y\). This follows by taking the difference of the polarization of the square of their sum and the two separate squares, then dividing by \(2\). The mixed form has rank two on the two coordinates \(t\wedge x,t\wedge y\), and vanishes on the remaining coordinate \(x\wedge y\). Every bivector in dimension three is decomposable, so equality of these polarization values would identify the two quadratic forms on the entire exterior square. Since the characteristic is odd, their symmetric matrices would have equal rank. The rank of \(\Lambda^2 C\) is \(\binom{\operatorname{rank}C}{2}\), which can be \(0,1,3\) in dimension three. The required rank two is impossible. This proves the strict gap. \(\square\)


## 3. Extension to every fixed finite field of characteristic two and size at least four

The recognition algorithm of Section 1 applies over every fixed finite field \(K\) of characteristic two with \(|K|\ge4\). When \(|K|>4\), the exterior criterion used there holds already for a single summand. For \(K=\mathbb F_4\) the one-summand Hermitian test accounts for the different space of cube corrections.

To see this, fix \(L\) and choose \(a,b\in K\). The product of the three factors having coefficients \(aL,bL,(a+b)L\) has zero first coefficient, second coefficient \((a^2+ab+b^2)L^2\), and third coefficient \(ab(a+b)L^3\). Because finite fields are perfect, choose \(s^2=a^2+ab+b^2\) and append two factors with coefficient \(sL\). Their product is \(1+t^2s^2L^2\), which cancels the second coefficient and leaves the third unchanged. Taking \(a=1\) and \(b\notin\{0,1\}\) fixes a nonzero \(\beta=ab(a+b)\). Scaling provides all cubic corrections \(\beta c^3 L^3\) with \(c\in K\), and concatenating lists adds corrections.

Let \(K_0\) be the \(\mathbb F_2\)-linear span of the cubes of scalars in \(K\). It is a field: it contains \(1\), is closed under products of sums of cubes, and for \(h\ne0\) in \(K_0\) the identity \(h^{-1}=h^2(h^{-1})^3\) shows that \(h^{-1}\) belongs to \(K_0\). If \(u\in K\setminus K_0\), the expansion of \((u+1)^3\) shows \(u^2+u\in K_0\). Thus \(u\) has an irreducible quadratic over \(K_0\) with other root \(u+1\). Since \(u^3\in K_0\), the conjugate cubes are equal, making \(u^2+u+1=0\). There can be at most two elements outside \(K_0\). An additive coset of \(K_0\) of size \(|K_0|\) is disjoint from \(K_0\) whenever the extension is proper. Therefore a proper extension here requires \(K_0=\mathbb F_2\) and \(K=\mathbb F_4\), which is indeed exceptional since all its nonzero cubes are \(1\).

It follows that for \(|K|>4\) the corrections include each scalar multiple of each \(L^3\). The span of cubes over \(K\) is the entire nonsquarefree subspace \(W\), by the independent mixed coefficient pairs obtained from \(x_i+x_j\) and \(x_i+c x_j\) with \(c\ne0,1\). Together with arbitrary first and second coefficients and Newton's identity this gives the exact characterization \(\mathrm{Sym}_3=\{\ell Q+w:w\in W\}\). Thus the alternating three-form algorithm applies to all summand bounds \(k\ge1\); the zero-summand case is immediate. In the exceptional field \(\mathbb F_4\) the correction for a single unweighted summand is \(W_0\) of Section 1 instead. \(\square\)
