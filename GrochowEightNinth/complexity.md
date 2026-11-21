# Elementary symmetric polynomials in positive characteristic

These are informal proofs of three statements drawn from *Computing the Elementary Symmetric Polynomials in Positive Characteristics*. The statements use ordinary polynomial coordinates and the source's model of a single elementary symmetric polynomial applied to arbitrary linear forms. [Primary source](https://arxiv.org/html/2509.05009)

## 1. Exact dimension of the order-two zero locus

**Theorem.** Let \(2\le d\le n\), and let \(V_2(e_d^n)\) be the common zero locus of the elementary symmetric polynomial and its first derivatives, with dimension taken over an algebraic closure. In characteristic zero its dimension is \(d-2\). In characteristic \(p>0\) put \(P=p^{1+\lfloor\log_p d\rfloor}\), the smallest power of \(p\) strictly larger than \(d\). Then
\[
\dim V_2(e_d^n)=
\begin{cases}
d-1,&P\mid n-d+1,\\
d-2,&P\nmid n-d+1 .
\end{cases}
\]
More precisely, the \((d-1)\)-dimensional irreducible components are exactly the coordinate-equality subspaces coming from partitions into \(d-1\) blocks whose sizes are all \(1\bmod P\). This corrects Conjecture 2.11 and its cited sufficiency criterion at degrees that are powers of \(p\). At \(p=d=2\) and \(n=3\), for example, the first derivatives vanish on the diagonal line and \(e_2^3(a,a,a)=a^2\), so the common zero locus is the origin. [Conjecture 2.11 and Proposition 2.6](https://arxiv.org/html/2509.05009#S2)

**Proof.** Let \(F(t)=\prod_i(1+x_it)\). At any point where the first derivatives vanish, each coordinate \(x_i\) is a root of
\[
\sum_{a=0}^{d-1}(-z)^a e_{d-1-a}(x)
\]
as a polynomial in \(z\), because its value at \(z=x_i\) is the coefficient of \(t^{d-1}\) in \(F(t)/(1+x_it)\). The leading coefficient is \((-1)^{d-1}\). Hence there are at most \(d-1\) distinct coordinate values, and the locus is contained in the union of the subspaces defined by equality on the blocks of partitions into \(d-1\) nonempty blocks. Each of these subspaces is irreducible and has dimension \(d-1\). A component of that dimension must equal one of these subspaces.

Fix such a partition and call its independent block values \(a_1,\ldots,a_{d-1}\), with multiplicities \(m_1,\ldots,m_{d-1}\). Assume the whole subspace lies in \(V_2(e_d^n)\). The vanishing derivatives say that deleting one copy of any single block value leaves \(e_{d-1}=0\). More generally, deleting one copy from each of any \(s\) distinct blocks leaves \(e_{d-s}=0\). To pass from \(s\) to \(s+1\), choose two different members \(i,j\) of an \((s+1)\)-set of blocks. Compare deleting from all but \(i\) and deleting from all but \(j\). On the multiset obtained by deleting from the full set, the difference of the two identities is \((a_i-a_j)e_{d-s-1}=0\). Since the block values are independent indeterminates, this forces the desired vanishing. At \(s=d-1\) this gives
\[
\sum_{i=1}^{d-1}(m_i-1)a_i=0 .
\]
In characteristic zero it forces all \(m_i=1\), contradicting \(n\ge d\). In characteristic \(p\) it forces \(m_i\equiv1\bmod p\).

Now fix \(j\) and any \(p^u\le d\) with \(u\ge1\). Choose \(d-p^u\) distinct other blocks, possible because \(d-p^u\le d-2\). The coefficient in the restricted \(e_d^n\) of \(a_j^{p^u}\) times the product of their block variables is \(\binom{m_j}{p^u}\) times their multiplicities. These multiplicities equal \(1\) in the field. Thus \(\binom{m_j}{p^u}=0\bmod p\), so the \(u\)-th base-\(p\) digit of \(m_j\) is zero. This last fact also follows directly by expanding \((1+t)^{m_j}\) as the product of its base-\(p\) digit factors \((1+t^{p^v})^{m_{j,v}}\). It follows that \(m_j\equiv1\bmod P\).

Conversely, when every \(m_j\equiv1\bmod P\), Frobenius gives
\[
\prod_j(1+a_jt)^{m_j}\equiv\prod_j(1+a_jt)\pmod {t^{d+1}} .
\]
The right side has degree \(d-1\). Deleting one copy from block \(j\) gives the same congruence with the \(j\)-th linear factor removed on the right, whose degree is \(d-2\). The required coefficient and all derivatives vanish. A partition with the specified multiplicities exists exactly when \(P\mid n-d+1\), by putting all extra multiplicity in a single block. In the remaining cases the upper bound becomes \(d-2\). The coordinate subspace supported on any \(d-2\) coordinates always lies in the locus, giving equality. \(\square\)

## 2. The first degree with unbounded border affine Chow rank

Use border affine Chow rank in the source's sense, the minimum number of products of affine linear forms in a coefficientwise one-parameter limit. There is no bound on the number of factors in each product. [Section 4 and Theorem 3.9](https://arxiv.org/html/2509.05009#S4)

**Theorem.** Over every field of characteristic \(p>0\), every polynomial of total degree \(d\le p\) has border affine Chow rank at most \(2\). For \(n\ge3\) and \(2\le d\le p\), the worst case in \(n\) variables has rank exactly \(2\). In degree \(p+1\) the worst-case rank is \(\Theta_p(n)\), with the explicit upper bound \(2(n+1)\). Thus \(p+1\) is the first degree with no constant upper bound in the number of variables.

**A construction of prescribed initial coefficients.** For linear forms \(L_1,\ldots,L_j\), the formal product
\[
G(t)=\prod_{S\subseteq[j]}\left(1+t\sum_{i\in S}L_i\right)^{(-1)^{j-|S|}}
\]
is \(1+(-1)^{j-1}(j-1)!L_1\cdots L_jt^j\) modulo \(t^{j+1}\) over the integers. Indeed, take the formal logarithm over the rationals in independent placeholders \(L_i\). By inclusion-exclusion the power-sum difference at each degree smaller than \(j\) vanishes. At degree \(j\) only monomials containing every \(L_i\) survive, giving \(j!\prod_iL_i\). The coefficient from the logarithm is consequently \((-1)^{j-1}(j-1)!\prod_i L_i\), and the identical first nonzero coefficient occurs in the product. All coefficients of the product of formal units lie in the integer polynomial ring, so the resulting identity specializes in every characteristic. In characteristic \(p\) an inverse factor can be replaced modulo any prescribed \(t^{D+1}\) by \(p^a-1\) repetitions, once \(p^a>D\), because \((1+tL)^{p^a}=1+t^{p^a}L^{p^a}\).

For \(j\le p\), the scalar \((j-1)!\) is nonzero. Scaling one of the forms and using this construction for every monomial gives a finite list of linear forms \(B_i\) with
\[
\prod_i(1+tB_i)\equiv1+t^j f\pmod {t^{j+1}}
\]
for any homogeneous polynomial \(f\) of degree \(j\). Concatenating lists adds their first nonzero coefficients. The same construction, used successively at \(j=1,\ldots,p\), gives a list with any prescribed collection of elementary symmetric coefficients in those degrees, since one can change degree \(j\) without altering the lower degrees.


**Upper bounds and the rank-one boundary.** For a homogeneous degree-\(d\) polynomial in the construction, the two products in
\[
\epsilon^{-d}\left(\prod_i(1+\epsilon B_i)-1\right)
\]
give a border representation. A constant scalar can be absorbed in an affine factor. Homogenization and then setting the homogenizing variable to one gives the same result for inhomogeneous polynomials. At degree \(p+1\) every homogenized form is a sum \(\sum_{i=0}^n x_i g_i\) of \(n+1\) forms \(g_i\) of degree \(p\). Multiplication by \(x_i\) preserves the number of products in a border representation, giving the stated bound.

To see that border rank one adds no nonzero polynomials to exact rank one, normalize each affine factor over \(K(\epsilon)\) by its smallest coefficient valuation. The reduction modulo \(\epsilon\) of the resulting factor is a nonzero affine form. Their product is nonzero because the polynomial ring is a domain, so the limit, if nonzero, is exactly the product of the reductions times a scalar. For every \(d\ge2\) the homogeneous polynomial \(x_1x_2^{d-1}+x_3^d\) is irreducible. It is primitive as a polynomial in \(x_1\) over \(K[x_2,x_3]\) and is linear over the fraction field, so Gauss's lemma applies. A representation by affine factors in more variables could be specialized back to these three variables, making such a representation impossible there as well. This gives the lower bound \(2\).

**Linear lower bound in degree \(p+1\).** Here is the coefficient argument with the constants tracked. A border sum with \(k\) product terms for a homogeneous polynomial can be assumed to have each affine factor's constant term nonzero as an element of \(K(\epsilon)\). Add a sufficiently high power of \(\epsilon\) to any zero constant term. All error terms then vanish in the limit, since only finitely many factors occur, with a finite lower bound on coefficient valuations. Normalize those constants to \(1\) and absorb the scalar factors in the outside coefficients. The degree-\((p+1)\) part of each product is now a scalar multiple of \(e_{p+1}(L_1,\ldots,L_m)\) on linear forms.

Write \(E_j=e_j(L_1,\ldots,L_m)\), \(P_j=\sum_i L_i^j\). Newton's identity in characteristic \(p\) is
\[
E_{p+1}=\sum_{i=1}^{p+1}(-1)^{i-1}E_{p+1-i}P_i .
\]
Its terms \(i=1,\ldots,p-1\) are products of two forms of positive degree. The term \(i=p\) is a scalar multiple of \(E_1^{p+1}\) by Frobenius, and the last term is a signed sum of \((p+1)\)-st powers of linear forms. Neither of the latter contributes to a squarefree monomial of degree \(p+1\). Thus each of the \(k\) terms is replaced on these squarefree coefficients by at most \(p-1\) products. Put \(q=k(p-1)\).

On \(N=(p+1)b\) variables, let \(c_S\) denote the coefficient on the squarefree monomial of each \((p+1)\)-subset \(S\). Consider the coefficient polynomial
\[
\sum_{\Pi}\ \prod_{S\in\Pi} c_S ,
\]
where \(\Pi\) ranges over unordered partitions of the \(N\) variables into \(b\) blocks of size \(p+1\). If the coefficients come from \(q\) products of two homogeneous forms, expand in formal coefficients of their separate factors. A fixed resulting monomial records disjoint factor subsets with a product index attached. For a given product index \(i\), there are \(b_i\) chosen coefficients of its first factor and \(b_i\) of its second factor. Every matching between the two lists yields exactly one contribution to the original coefficient monomial, and these are all the contributions, because the factors use disjoint nonempty variable sets. The multiplicity is \(\prod_i b_i!\). It is zero in \(K\) when \(b>q(p-1)=k(p-1)^2\). This polynomial identity applies over \(K(\epsilon)\) and persists when the final coefficient vector has a limit. But for a sum of \(b\) disjoint squarefree monomials of degree \(p+1\) its value is \(1\), as only the partition into those blocks contributes. Taking \(b=\lfloor n/(p+1)\rfloor\) proves the lower bound linear in \(n\) for fixed \(p\). This follows the partition metapolynomial argument in the primary source. \(\square\) [Claims 3.6–3.8 and Theorem 3.9](https://arxiv.org/html/2509.05009#S3)

## 3. Exact quartic projections in characteristic three and failure of the proposed sufficient condition

Here \(\mathrm{Sym}\) consists of forms \(e_d(L_1,\ldots,L_m)\) for an arbitrary finite list of homogeneous linear inputs. The source asks in Section 4 whether the decomposition into reducible forms and powers underlying Claim 3.7 is also sufficient in higher characteristic. It is insufficient already for one projection in characteristic three. [Claim 3.7 and Section 4](https://arxiv.org/html/2509.05009#S4)

**Theorem.** Over an algebraically closed field of characteristic \(3\), put \(W=\operatorname{span}\{x_i^3x_j:i,j\in[n]\}\) in degree four. A quartic form \(f\) is in \(\mathrm{Sym}\) if and only if
\[
f\equiv \ell H+Q^2\pmod W
\]
for a linear form \(\ell\), a cubic \(H\), and a quadratic \(Q\). In particular, if \(q_U,q_V\) are nondegenerate quadratics in two disjoint sets of four variables, then their product \(q_Uq_V\) is not in \(\mathrm{Sym}\). The product is itself reducible and therefore satisfies the proposed decomposition condition. The nonmembership remains valid over every field of characteristic \(3\) when the two quadratics remain nondegenerate.

**Characterization.** The subspace \(W\) equals the span of fourth powers of linear forms. One inclusion follows by expanding \(L^4=L^3L\). For the other, vary the scalar \(a\) in \((x_i+ax_j)^4\) and use coefficient extraction in \(a\) over the infinite field. Any scalar multiple of a fourth power is another fourth power, since the field is algebraically closed.

The preceding construction gives a list of linear forms with arbitrary \(E_1,E_2,E_3\) of the respective degrees. In characteristic three, Newton's identity yields
\[
E_4=E_1E_3-E_2(E_1^2+E_2)+E_1^4-P_4
\equiv E_1(E_3-E_1E_2)-E_2^2 \pmod W .
\]
This proves necessity, since \(-1\) is a square. Given \(\ell,H,Q\), choose \(E_1=\ell\), \(E_2=\sqrt{-1}\,Q\), and \(E_3=H+\ell E_2\), and realize these with the list construction. The difference from the desired \(E_4\) belongs to \(W\). To add any fourth power \(L^4\) to \(E_4\) without changing the first three coefficients, append a list whose generating product in \(t\) is \(1+t^4L^4\). Such a list exists because \(1+s^4\) splits into linear factors with constant term \(1\) over the field. Applying this to a sum of fourth powers realizes the entire difference. \(\square\)


**A product of two quadratics outside the model.** Suppose the displayed criterion holds for \(f=q_Uq_V\). In each four-dimensional block choose a two-dimensional subspace in the kernel of \(\ell\) on which the block's form is nondegenerate. Such a choice exists because a hyperplane in a nondegenerate four-dimensional quadratic space has radical of dimension at most one, hence rank at least two. Restrict to the direct sum of the two chosen subspaces. Over the algebraic closure choose coordinates \(e_1,e_2,e_3,e_4\) in which the two restricted forms have matrices \(A=\operatorname{diag}(1,1,0,0)\) and \(B=\operatorname{diag}(0,0,1,1)\). The term \(\ell H\) vanishes on this restriction. The subspace generated by terms \(L^3M\) is preserved under the restriction and any linear coordinate change. Thus \(q_Aq_B-Q^2\) lies in that subspace, where \(q_A(x)=x^{\mathsf T}Ax\) and similarly for \(B\).

For a quartic \(g\) define its full polarization at \(v_1,\ldots,v_4\) as the coefficient of \(t_1t_2t_3t_4\) in \(g(\sum_i t_iv_i)\). It kills every \(L^3M\) by Frobenius. At \((x,x,y,y)\), the polarization of \(Q^2\), with \(Q(x)=x^{\mathsf T}Cx\) and \(C\) symmetric, is
\[
8\big(C(x,x)C(y,y)+2C(x,y)^2\big)
=8\big(C(x,x)C(y,y)-C(x,y)^2\big).
\]
This is \(8\,(\Lambda^2 C)(x\wedge y,x\wedge y)\), using the induced symmetric form on the exterior square. The polarization of \(q_Aq_B\) at these arguments is \(4 R(x\wedge y,x\wedge y)\), where \(R=\Lambda^2(A+B)-\Lambda^2 A-\Lambda^2 B\). One can also obtain the formula by subtracting the polarizations of \(q_A^2\) and \(q_B^2\) from that of \((q_A+q_B)^2\) and dividing by \(2\). In the ordered exterior basis \((e_{12},e_{34},e_{13},e_{14},e_{23},e_{24})\), the matrix of \(R\) has zero first block and identity last block of order four.

Let \(J\) be the matrix of the exterior pairing \(u,v\mapsto(u\wedge v)/(e_1\wedge e_2\wedge e_3\wedge e_4)\). A symmetric bilinear form whose quadratic evaluations vanish on every decomposable exterior vector is a scalar multiple of \(J\). To verify this directly, evaluate on each \(e_{ij}\), and on sums of two basis vectors sharing an index. The only entries still possible are complementary pairs \(12,34\), \(13,24\), and \(14,23\). Evaluating on \((e_1+e_3)\wedge(e_2+e_4)\) and \((e_1+e_2)\wedge(e_3+e_4)\) forces these three entries to be proportional to \((1,-1,1)\). The vanishing polarization therefore gives
\[
M=\Lambda^2 C=\tfrac12 R+\lambda J
\]
for a scalar \(\lambda\).

In the chosen basis \(J^2=I\). Exterior multiplication gives \(M^{\mathsf T}JM=\det(C)J\), as applying \(C\) to both two-vectors multiplies their exterior product by \(\det(C)\). Since \(C\) is symmetric, \(M\) is symmetric. On the two-dimensional first block, \(R=0\) and \(J\) is invertible, so the identity forces \(\det(C)=\lambda^2\). On the last block \(R=I\) and \(J\) is a signed permutation matrix with zero diagonal and nonzero off-diagonal entries. Putting \(\alpha=1/2\), the same identity would give
\[
\alpha^2 J+2\alpha\lambda I=0
\]
on that block. This is impossible at its off-diagonal entries. Thus the proposed representation does not exist, even after passing to the algebraic closure. \(\square\)


## 4. Recognizing sums of cubic symmetric projections is NP-complete

**Decision problem.** Fix \(K=\mathbb F_2\) or \(\mathbb F_4\). The input is the coefficient vector of a homogeneous cubic \(f\in K[x_1,\ldots,x_n]\) and a nonnegative integer \(k\) in binary. Decide whether \(f\) is a linear combination of at most \(k\) cubic polynomials \(e_3(L_1,\ldots,L_m)\), each with its own finite list of homogeneous linear forms over \(K\). The list lengths are unrestricted by the input. This problem is NP-complete over either field. Over any field containing \(\mathbb F_4\), the reduction also proves NP-hardness for cubics with zero-one coefficients. This answers the recognition question of Section 4 for variable \(k\). [Section 4 and Corollary 3.4](https://arxiv.org/html/2509.05009#S4)

**Lower bound from a graph.** For a simple graph \(G=(V,E)\), introduce variables \(x_v\) for vertices and \(y_e\) for edges, and let
\[
f_G=\sum_{e=\{u,v\}\in E} x_u x_v y_e .
\]
We prove that every representation as a sum of \(k\) projected symmetric cubics requires \(k\ge\tau(G)\), the minimum vertex-cover size. Over characteristic two, Newton's identity reads
\[
E_3=E_1E_2+E_1^3+\sum_i L_i^3 .
\]
All cubes of linear forms vanish modulo the squares of the variables, so each summand reduces to a product of a linear and a quadratic form in that quotient, also after a scalar multiplier. The quotient in characteristic two is the exterior algebra on the coordinate linear forms, because its generators commute and square to zero. Thus a representation with \(k\) summands makes the alternating three-form corresponding to \(f_G\) vanish on a subspace \(H\) of codimension at most \(k\): take the common kernel of the \(k\) linear factors, and restrict all three arguments to it.

Let \(U\) be the image of \(H\) under projection onto the vertex-coordinate space \(K^V\), and \(W_0=H\cap K^E\). For \(a,b\in U\), take any lifts in \(H\) and evaluate the alternating three-form on those lifts and \(z\in W_0\). The result is the pairing of \(z\) with the edge-coordinate vector
\[
\big(a_u b_v-a_v b_u\big)_{\{u,v\}\in E}.
\]
Hence \(W_0\) annihilates the image of \(\Lambda^2 U\) under this map, and its codimension in \(K^E\) is at least the rank of the map. Choose a subset \(S\subseteq V\) on which the coordinate restrictions form a basis of \(U^*\), so \(|S|=\dim U\). For every edge internal to \(S\), the corresponding coordinate functional on \(\Lambda^2 U\) is the wedge of two different members of that basis. These are independent. It follows that
\[
\operatorname{codim}H\ \ge\ |V|-|S|+|E(G[S])|\ \ge\ \tau(G).
\]
The final inequality follows by taking all vertices outside \(S\) and one endpoint for each edge internal to \(S\). This gives a cover with at most the middle expression's size.

**Matching upper bound over \(\mathbb F_4\).** Assign each edge to one of its endpoints in a minimum cover. Then \(f_G\) is a sum of \(\tau(G)\) reducible cubics \(x_v Q_v\). Every product \(\ell Q\) of a linear and a quadratic form is one projected symmetric cubic over this field. Use the initial-coefficient construction to obtain a list with \(E_1=\ell\) and \(E_2=Q\). Its cubic differs from \(\ell Q\) by \(\ell^3+\sum_i L_i^3\). For any existing form \(L\), append the three factors whose product is \(1+t^3 L^3\), using the three cube roots of unity \(1,\omega,\omega^2\). This adds \(L^3\) to the cubic without changing its first two coefficients. In characteristic two these additions cancel the displayed discrepancy, including the cube of \(\ell\). The correction involves just cubes of forms already present or prescribed, so it requires no root extraction from other coefficients. The same construction works over any field containing \(\mathbb F_4\). Thus the exact minimum number for \(f_G\) is \(\tau(G)\) over these fields, giving a polynomial-time reduction from Vertex Cover.

**Upper bound with one extra summand over \(\mathbb F_2\).** Define a linear map \(T\) from quadratics to cubics by \(T(x_i^2)=0\) and \(T(x_ix_j)=x_i^2x_j+x_ix_j^2\) for different indices. This definition uses all graph variables, including the edge variables. In a list of linear forms over \(\mathbb F_2\), if \(E_1\) is zero or a single coordinate variable, then Newton's identity gives \(E_3=E_1E_2+T(E_2)\). Indeed, for \(L=\sum_i a_i x_i\) the coefficient of \(x_i^3\) in \(L^3\) is \(a_i\), and that of \(x_i^2x_j\) is \(a_i a_j\), since \(a_i^2=a_i\). The diagonal coefficients of \(\sum L^3\) cancel those of \(E_1^3\). For different indices \(i,j\), the mixed coefficient of \(E_2\) is the sum of within-form products \(\sum a_i a_j\) plus the product of the two \(E_1\) coefficients. That product is zero under the stated condition. This proves the identity.

For the cover expression \(f_G=\sum_v x_v Q_v\), the initial-coefficient construction makes each \(x_v Q_v+T(Q_v)\) one projected cubic. One more list with \(E_1=0\) and \(E_2=\sum_vQ_v\) supplies the correction \(T(\sum_vQ_v)\), which cancels in characteristic two. Thus the minimum representation count lies between \(\tau(G)\) and \(\tau(G)+1\). To decide whether \(\tau(G)\le k\), apply the recognition query at bound \(2k+1\) to the cubic from two disjoint copies of \(G\). The cover number doubles, and the one-unit correction cannot bridge the resulting two-unit gap.

**Polynomial certificates over either finite field.** The truncated units \(1+tL\) in \(K[x][t]/(t^4)\) generate a finite abelian group. Its order is at most \(|K|^{O(n^3)}\), since the coefficient of \(t^i\) is homogeneous of degree \(i\) for \(i\le3\). Each generator has order dividing \(4\), by Frobenius. Greedily select generators among the allowed factors, each time strictly increasing the generated subgroup. Each strict increase raises the subgroup order by at least a factor of two, so \(O(n^3)\) selected factors generate the group. Every group member is a product of their powers with exponents at most \(3\), giving a projected cubic list of polynomial length. Also every cubic monomial is \(e_3\) of its own three factors, so any cubic is a sum of at most \(\binom{n+2}3\) projected cubics with scalar multipliers. This caps the necessary number of lists even when \(k\) is in binary. A certificate supplies the lists and scalars. Multiplying their generating products truncated modulo \(t^4\) and comparing the cubic coefficient vector verifies the certificate in polynomial time. \(\square\)
