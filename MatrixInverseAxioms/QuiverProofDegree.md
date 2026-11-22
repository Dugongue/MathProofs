# Exact Polynomial Calculus degree for quiver representation isomorphism

Let \(A,B\) be two explicit finite-dimensional representations of a finite quiver over a field \(F\). For each arrow \(a:u\to v\), write their maps as \(A_a:A_u\to A_v\) and \(B_a:B_u\to B_v\). Use variables \(X_v:A_v\to B_v\), \(Y_v:B_v\to A_v\), and the literal equations
\[
 X_v A_a-B_aX_u=0,\qquad Y_vX_v=I_{A_v},\qquad X_vY_v=I_{B_v}.
\]
There are no coordinate field equations. The quiver may have loops, repeated arrows, or relations satisfied by the two representations. Its size and dimension vector may vary. Ordinary Polynomial Calculus (PC) uses binary field-linear combinations and multiplication by a single variable. Degree refers to the largest actual total degree of any proof line. This extends the ordinary matrix conjugacy encoding of Question 7.3 from one loop to arbitrary finite linear actions of this form. [Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

## The formula

Let \(H=\operatorname{Hom}_F(A,B)\) be the solution space of the forward linear equations. Decompose both representations over \(\overline F\) into indecomposables, and write \(a_T,b_T\) for the multiplicities of an isomorphism type \(T\). For unequal counts \(a,b\) set
\[
 \delta_F(a,b)=
 \begin{cases}
 0 & \min(a,b)=0,\\
 2 & \min(a,b)>0,\ \operatorname{char}F=0,\\
 \min\bigl(\min(a,b)+2,\ 2p^{v_p(|a-b|)}\bigr)
     & \min(a,b)>0,\ \operatorname{char}F=p>0 .
 \end{cases}
\]
The exact minimum degree is as follows.

1. If all multiplicities agree, the equations are satisfiable over \(F\).
2. If at some vertex exactly one of \(A_v,B_v\) has dimension zero, a literal inverse axiom is a nonzero constant. The degree is zero.
3. For the remaining instances the degree is two exactly when some vertex \(v\) admits \(C\in\operatorname{End}_F(A_v)\), \(D\in\operatorname{End}_F(B_v)\) such that
   \[
       X_v C=D X_v\quad\text{for all }X\in H,\qquad
       \operatorname{tr}C-\operatorname{tr}D\ne0 .
   \]
4. Every other negative instance has degree \(\max(3,\min_{a_T\ne b_T}\delta_F(a_T,b_T))\).

In characteristic zero every negative instance has degree at most three. If the reverse arrow equations \(Y_vB_a-A_aY_u=0\) are also supplied as inputs, the degree is exactly \(\min_{a_T\ne b_T}\delta_F(a_T,b_T)\), with one exception at degree zero. When this minimum is zero but there is no literal nonzero constant axiom, the answer is two. Simultaneous similarity, isomorphism of finite-dimensional modules given by generator matrices, marked-subspace transport and linear chain-complex isomorphism all use the same formula on their respective literal forward and inverse equations.

The rectangular-degree input to this theorem is the all-characteristic result for independent matrices \(P,Q\) of shapes \(b\)-by-\(a\) and \(a\)-by-\(b\) with \(PQ=I_b\), \(QP=I_a\). Its exact degree is \(\delta_F(a,b)\). Its proof uses the matching-design extension and a Laurent-weight argument in positive characteristic. [Rectangular degree proof](https://github.com/Dugongue/MathProofs/blob/55f3f9c1c78a81d4d617f902845a8c94a8455c33/GeneralCongruenceSparseConjugacy/ConjugacyDegree.md) · [Riis's matching designs](https://arxiv.org/html/2611.07280v1#S14)

## Proof of the degree formula

**Fields and bases.** For a degree bound \(d\), iteratively close the span of the usable axioms under multiplication by single variables from its intersection with polynomials of degree at most \(d-1\). All calculations take place in the finite-dimensional space of polynomials of degree at most \(d\). Linear span, intersection with a coordinate subspace, and a linear map commute with field extension, so the final span does too. Basis changes at the vertices induce homogeneous linear substitutions in the corresponding variable tuples, and each transformed axiom is a linear combination of original axioms. Multiplying by a linear form is implemented by the separate variable multiplications and addition. Existence of a bounded-degree proof is therefore invariant under the vertex basis changes. As for satisfiability, an isomorphism over \(\overline F\) is defined over a finite extension \(L/F\). Restricting scalars gives an isomorphism of \([L:F]\) copies of each original representation. Krull–Schmidt cancellation then gives \(A\simeq B\) over \(F\), the usual Noether–Deuring argument. [Noether–Deuring](https://personal.math.ubc.ca/~reichst/benson-reichstein-v2.pdf)

**Lower bound from decomposed inputs.** Choose one based representative per indecomposable type over \(\overline F\) and write \(A\) and \(B\) as direct sums in the chosen bases. For type \(T\), substitute \(X_v=P_T\otimes I_{T_v}\), \(Y_v=Q_T\otimes I_{T_v}\) on its blocks, using the same rectangular pair at every vertex with \(T_v\ne0\). Set off-type blocks to zero. For equal multiplicities take both maps to be the identity. Then both directions of every arrow equation vanish. On any given vertex block the inverse equations become repetitions of rectangular inverse equations or zero. Since \(T\) has nonzero dimension at some vertex, its two rectangular inverse families occur. The substituted variables are variables, one, or zero, so the proof degree cannot increase. The rectangular pairs are independent across types.

For disjoint variable systems the minimum PC refutation degree of their union is the minimum of the local degrees. To prove the lower bound in this fact, fix a degree \(d\), let \(V_T\) be the local degree-\(d\) consequence space, and choose a local polynomial basis compatible with \(V_T\) and the degree filtration. Such a basis is obtained by extending the basis for \(V_T\) first at every degree, then completing the whole basis there. Give each vector its degree. Products of these basis vectors of total degree at most \(d\) give a basis of the global degree-\(d\) space, by the total-degree filtration on a tensor product. Span only those products with at least one selected consequence factor. This span contains the usable axioms and is compatible with the degree filtration. Multiplying a basis product of total degree at most \(d-1\) by a variable keeps a selected consequence factor in a different block or replaces it by a legal local multiple in its own block. Thus the span contains all global degree-\(d\) consequences. If none of the local spaces contains one, select the constant one as a complementary basis vector in each local space and conclude that the global span misses one. Applied to the rectangular specialization, this gives the numerical lower bound \(\min_T\delta_F(a_T,b_T)\).

**Preparation and upper bound.** For each arrow, the reverse intertwiner equation follows in degree three by the identity
\[
 A_aY_u-Y_vB_a
 =Y_v(X_vA_a-B_aX_u)Y_u
   +(I-Y_vX_v)A_aY_u+Y_vB_a(X_uY_u-I).
\]
Project \(X,Y\) linearly onto \(\operatorname{Hom}(A,B)\), \(\operatorname{Hom}(B,A)\), obtaining \(\widehat X,\widehat Y\). Each entry difference is a scalar combination of the appropriate forward or reverse linear equations because the projection error vanishes on that linear kernel. Telescoping
\[
 \widehat Y_v\widehat X_v-I
 =(Y_vX_v-I)+(\widehat Y_v-Y_v)\widehat X_v+Y_v(\widehat X_v-X_v)
\]
and the expression with \(X,Y\) interchanged gives the projected inverse equations within degree three. If both arrow directions are input axioms, the same preparation costs degree at most two.

Over the algebraic closure put \(E=\operatorname{End}(A\oplus B)\), with \(e,f\) the two summand projectors. The projected maps belong to \(fEe,eEf\), and their inverse products to \(fEf,eEe\). The standard endomorphism quotient of a finite direct sum of indecomposables gives
\[
 E/\operatorname{rad}E \cong \prod_T M_{a_T+b_T}(\overline F).
\]
In the \(T\)-factor, \(e,f\) are complementary idempotents of ranks \(a_T,b_T\). One way to see this is to take the block components and reduce the equal-type blocks modulo the radicals of their local endomorphism rings. Compositions through different indecomposable types reduce to zero, since a unit composite would make one indecomposable split off another. The resulting algebra map is the semisimple quotient by the usual Krull–Schmidt description of the radical. Its matrix entries are linear functionals on the endomorphism space and may be extended linearly to the full direct sum of vertex matrix spaces. Apply these functionals to the projected inverse lines. This gives the two inverse systems of the indicated sizes in homogeneous linear forms. Any rectangular proof simulates after substitution of these forms within its original degree. When one multiplicity is zero the extracted nonzero constant is already a linear combination of the prepared axioms. This proves the upper bound with the degree-three overhead, or the degree-two overhead when the reverse arrows were supplied.

**Exact cutoff at degree two.** Assume there is no literal constant axiom and stop a prospective degree-two proof at its first nonzero constant. All derived linear lines before then belong to the span of the forward equations. Every permitted multiplication of a nonzero line is therefore a variable multiple of an element of that span. All other degree-two lines are combinations of these, the forward equations, and the input inverse entries. In particular a nonzero constant appears if and only if a scalar combination of the inverse entries has nonzero constant and its homogeneous quadratic part vanishes identically after substituting a basis-parametrization of \(H\) for \(X\), leaving \(Y\) independent. For the converse, a quadratic polynomial vanishing under that substitution lies in the ideal of the forward linear forms, in degree two. This assertion uses a formal polynomial identity, valid even over a finite field, by completing the independent forward equations to coordinates. Each required quadratic is then a sum of linear multiples of forward equations.

Write the inverse combination as \(\sum_v[\operatorname{tr}(C_v(Y_vX_v-I))-\operatorname{tr}(D_v(X_vY_v-I))]\). Independent variables in each \(Y_v\) force the condition \(X_v C_v=D_vX_v\) separately at that vertex. At least one vertex must contribute a nonzero constant. Conversely one vertex suffices. No degree-one refutation is possible because the available degree-one equations are homogeneous. This proves the cutoff and the complete formula.

The criterion also has a numerical interpretation. Use a basis of the image \(H_v=\{X_v:X\in H\}\) as the arrows from \(A_v\) to \(B_v\) of a two-vertex quiver. Its endomorphisms are exactly the pairs \(C,D\) above. Over the closure, decompose this evaluation representation into indecomposables. The trace difference vanishes on the radical because each radical element is nilpotent and therefore has trace zero at both vertices. On the semisimple quotient it is the sum of the ordinary block traces weighted by the source-minus-target dimensions of those indecomposables, as seen by lifting the diagonal matrix units to summand idempotents. Off-diagonal copy blocks have zero trace at each vertex. Consequently degree two occurs exactly when at least one evaluation indecomposable has dimension difference nonzero in the coefficient field. Computing \(H\) followed by Gaussian elimination for \(C,D\) is sufficient, without decomposing the evaluation representation.

## Deterministic computation of the full degree over every finite field

Let \(F\) be any explicitly presented finite field. Its size and the quiver may vary. Rónyai's deterministic radical algorithm applied to the structure constants of \(E\) computes \(\operatorname{rad}E\) in polynomial time. A basis and multiplication table for \(E\) follow by linear algebra on the arrow equations for \(A\oplus B\). Write \(S=E/\operatorname{rad}E\), and compute its center \(C\) by commutation linear equations. Abstractly
\[
 C=\prod_i K_i,\qquad S=\prod_i M_{n_i}(K_i)
\]
for finite extensions \(K_i/F\), since every finite division ring is commutative. We need only the pairs of integers \(n_i^2\) and \(a_i n_i\), the componentwise \(C\)-ranks of \(S\) and \(\bar e S\) respectively. The multiplicities to insert into the geometric formula are \(a_i\) and \(b_i=n_i-a_i\). Indeed every field factor \(K_i\) is separable over \(F\) and splits as a product of copies of the algebraic closure. Each corresponding absolute type has that same pair of ranks. [Rónyai's structure algorithms](https://doi.org/10.1016/S0747-7171(08)80017-X) · [Deterministic radical and factoring-based full decomposition](https://arxiv.org/abs/2608.30340)

The required ranks can be computed without factoring or constructing individual Wedderburn blocks. For a finite \(C\)-module \(M\), choose \(x\ne0\) and compute \(I=\operatorname{Ann}_C(x)\) by linear algebra. The other ideal \(J=\operatorname{Ann}_C(I)\) is computed the same way, and \(C=I\oplus J\). On \(I M\), recurse without a rank increment. On \(J M\), quotient by \(Jx\) and recurse with a rank increment of one on this portion. Indeed at every field in the support \(J\), the vector \(x\) spans exactly one dimension. Compute the identities of \(I,J\) by projecting \(1\) to the two ideals, and use these to obtain the respective module restrictions. Omit an empty ideal. A zero module leaves a constant rank profile on the remaining center. The output is a finite family of explicitly given central idempotents on whose supports the computed rank is constant. A split strictly decreases each nonzero center dimension. In a step without a split the module dimension decreases. There are at most \(\dim_F C\) branches ending in nonzero center components, with polynomial path length, and all steps use field-linear arithmetic on spaces of polynomial dimension.

Run this procedure for \(S\), then for \(\bar e S\) on each resulting sector. Recover \(n_i\) by integer square root and \(a_i\) by division by \(n_i\). Equal-rank components may stay grouped. Apply the literal degree-zero and degree-two checks, then the formula. This gives exact degree in deterministic polynomial bit time in the explicit input length and \(\log |F|\). Only the numerical computation is asserted, since outputting a refutation with the minimum degree may require superpolynomial sparse size.

## The one-arrow case and sharp worst-case thresholds

Consider one arrow with source dimension \(m\) and target dimension \(n\), the same on both input representations, and ranks \(r=\operatorname{rank}A\ne s=\operatorname{rank}B\). Put \(u=\min(r,s)\), \(w=\max(r,s)\) and \(g=w-u\). The indecomposable types are the identity arrow and the two one-vertex simple representations. Their respective smaller multiplicities are \(u,m-w,n-w\), with all gaps of absolute size \(g\). The degree is two exactly when \(u=0\), \(s=m\), or \(r=n\). Otherwise the degree is three in characteristic zero. In characteristic \(p\) it is three if one of the three smaller multiplicities is zero, and otherwise it is
\[
  \max\!\bigl(3,\min(u+2,m-w+2,n-w+2,2p^{v_p(g)})\bigr).
\]
To check the degree-two distinction, express the arrows as rectangular rank normal forms. At the source vertex the possible forward maps are block lower, with columns partitioned into sizes \(r,m-r\), rows into \(s,m-s\), and just the upper-right block forced zero. At the target vertex the possible maps are block upper, with columns partitioned into \(r,n-r\) and rows into \(s,n-s\), and just the lower-left block forced zero. These patterns follow directly from the forward intertwiner equation, which identifies the two upper-left blocks without further constraining either projection individually. For a space spanned by the allowed matrix units, \(C,D\) must have equal diagonal labels along each allowed edge, and their diagonal labels are otherwise unconstrained. Indeed insert a single matrix unit and compare its own entry. Taking \(C,D\) diagonal also proves sufficiency of every prescribed label assignment. A fully populated corner incident with every allowed row and column through at least one edge makes the corresponding bipartite graph connected. In the source pattern this occurs when \(r>0\) and \(m-s>0\), and in the target pattern it occurs when \(s>0\) and \(n-r>0\). In each connected case the graph has the same number of rows and columns, so its trace difference vanishes. At the other boundaries the pattern has an isolated coordinate: the source graph when \(r=0<s\) or \(s=m>r\), and the target graph when \(s=0<r\) or \(r=n>s\). Such a coordinate alone gives trace difference \(1\) or \(-1\). In particular swapping endpoints can change the degree from three to two in the literal one-direction encoding. For \(m=3,n=2,r=1,s=2\), the forward system has degree three and its swapped system has degree two.

For any finite quiver and pairs with equal dimension vectors in characteristic \(p>0\), the **least possible maximum vertex dimension** for a negative pair of PC refutation degree at least \(d\ge4\) is
\[
       2(d-2)+p^{\lceil\log_p\lceil d/2\rceil\rceil}.
\]
The assertion takes the minimum across quivers and pairs, and is already attained on one arrow. For the lower bound every discrepant type must have smaller count at least \(d-2\), and its gap must be a nonzero multiple of the least power \(q\) of \(p\) with \(q\ge\lceil d/2\rceil\). Take a vertex on the support of a positive-gap type. The equal dimension condition forces some negative-gap type there. On either side these two types contribute at least \(2(d-2)+q\), since each of their nonzero vertex dimensions is at least one. For attainment take the one-arrow ranks \(r=d-2\) and \(s=r+q\) in equal source and target dimension \(2(d-2)+q\). Both ranks are interior, the three smaller counts are \(d-2\), and the formula gives degree exactly \(d\). Thus even one-arrow matrix rank equivalence has linear worst-case PC degree at every fixed positive characteristic. In characteristic zero an interior rank mismatch has degree three, already attained with \(m=n=3\).

These main claims are written arguments. The lower-bound input is independently identified above. The finite checker tests the cutoff against direct closure in the original equations and illustrates the factorization-free center calculation. [Finite checker](check_quiver_degree.py)
