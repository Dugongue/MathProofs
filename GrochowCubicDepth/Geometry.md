# Local singularities of cubic-form orbit closures inside algebra laws

Let \(K\) be algebraically closed and let \(V\) have dimension \(n\geq2\). Put \(Q=\operatorname{Sym}^2 V\), \(P=\operatorname{Sym}^3 V\), \(q=\dim Q\), and \(b=\dim P\). The cubic gadget is
\[
 A_h=\operatorname{Sym}(V\oplus Kz)/\big((V,z)^4,zV,z^3-h\big),\qquad h\in P .
\]
Use a fixed \(N\)-dimensional space \(E\) for these laws, with \(a=q+1\), \(m=n+1\), and \(N=1+m+a+b\). The graded dimensions are \((1,m,a,b)\). We take orbit closures with their reduced structures. In the augmented version, the law and its linear augmentation are both coordinates, and \(\operatorname{GL}(E)\) acts on both by transport. In the ordinary version, only the law is a coordinate.

Fix a nonzero \(f\), write \(C=\overline{\operatorname{GL}(V)f}\subseteq P\), and let \(X\) be the augmented algebra orbit closure of \(A_f\). The ordinary algebra orbit closure can be used instead when \(N\) is invertible in \(K\) or when \(K\) has characteristic different from two.

**Theorem.** A neighborhood in \(X\) of each split endpoint \(A_g\), \(g\in C\), has the following local description.

1. If \(g\neq0\), there is a Zariski neighborhood with local product coordinates over \(C\). At the pointed level,
   \[
   \widehat{\mathcal O}_{X,A_g}\ \cong\
      \widehat{\mathcal O}_{C,g}[[t_1,\ldots,t_s]],\qquad
   s=2N-1+m(a+b)+ab+2n+a(a+b)+b^2+q+n .
   \]
   Thus the algebra closure and the form closure have the same singularity up to a smooth factor. The product description also holds at all points on the chart with nonzero recovered cubic, including when their multiplication is written in a nonhomogeneous basis.
2. At \(g=0\), the same chart gives a smooth factor times the explicit reduced variety \(Y_C\) below. Its points with zero recovered cubic can have a nonzero filtered multiplication correction, even though every point with nonzero recovered cubic is isomorphic to its associated graded algebra.
3. If \(C\) spans \(P\), \(X\) is singular at \(A_0\). This holds for every \(f\neq0\) in characteristic zero, including binary cubics for which \(C=P\) is smooth.

The augmented version works in every characteristic.

## The local coordinates for multiplication

A law \(B\) in the chart is commutative, associative, unital, and augmented. Its augmentation kernel \(M\) satisfies \(M^4=0\), and the graded dimensions are \((1,m,a,b)\). The grading here is that of \(\operatorname{gr}_M B\). In degree one the chart has an intrinsic line \(L\) on which multiplication from degree one to degree two has rank one. A generator \(\zeta\) of that line has nonzero square. The complementary \(n\)-space \(U\) is the kernel of multiplication by \(\zeta\). It depends only on the line. We impose that multiplication induces isomorphisms
\[
 \operatorname{Sym}^2 U\oplus K\zeta^2 \longrightarrow M^2/M^3,
 \qquad
 \operatorname{Sym}^3 U\longrightarrow M^3 .
\]
In the first map the symbol \(\zeta^2\) in the source denotes the additional formal basis vector. The definition permits \(\zeta^3=0\).

These data hold for each \(A_h\). They hold on an open set of \(X\) around each \(A_g\), as can be checked using polynomial equations and rank. Here are the details ensuring the recovered data are regular on the chart. On a full-rank minor of \(v\mapsto L_v\), where \(L_v\) denotes left multiplication, the linear equations \(L_e=I_E\) give the identity \(e\) by Cramer's rule. All remaining equations hold on \(X\) there by density. Associativity, augmentation identities and \(M^4=0\) also extend by density. The ranks of the power maps \(M^{\otimes i}\to E\) are bounded by their ranks on the orbit, so equality holds on the open sets where appropriate minors survive. Their images and graded quotients are vector bundles there. For the ordinary version with \(N\) invertible, the augmentation on the entire orbit is \(v\mapsto N^{-1}\operatorname{tr} L_v\). Indeed \(L_v\) is the augmentation scalar times the identity plus a nilpotent operator. The graph of this equivariant linear expression is closed, so projection to laws identifies the augmented and ordinary orbit closures in that case.


Even when \(N\) is not invertible, in characteristic different from two the augmentation is regular on the ordinary closure locally at the endpoints in the theorem. Fix a basis \(v_1,\ldots,v_N\) of the ambient space whose elements each have the property that \(e,v_i,v_i^2,v_i^3\) are independent at the chosen endpoint. This is a nonempty open condition on possible \(v_i\), since a lifted \(x_1\) has that property, so such a basis exists. Recover \(e\) by the unit minor as above. On an open neighborhood, solve for the coefficient \(c_i\) of \(v_i^3\) when expressing \(v_i^4\) in the basis of its four-dimensional cyclic space. More explicitly, use a nonzero four-row minor of the columns \(e,v_i,v_i^2,v_i^3\) to define the coefficients. The remaining rows agree by density. On the orbit the nilpotence equation \((v_i-\epsilon(v_i)e)^4=0\) gives \(c_i=4\epsilon(v_i)\). Thus the values \(c_i/4\) define a regular map to the augmentation space on that neighborhood. Its graph agrees with the augmented closure over this open set, because it agrees on the dense orbit and is closed over the set. This identifies the reduced local models of the two closures.

To see regularity of the line even in characteristic two, take the vector space spanned by the \(2\times2\) minors of multiplication by a general degree-one element. These minors are quadratics in that element's coordinates. On a split law, write those coordinates \(u=\sum_i c_i x_i+d\zeta\). The quadratic span is precisely the space of quadratics vanishing at the point \(K\zeta\). Indeed the minors include \(c_i^2\) from columns \(x_i,x_j\) and rows \(x_i^2,x_i x_j\) for \(j\neq i\), \(c_i c_j\) from columns \(x_i,x_j\) and rows \(x_i^2,x_j^2\), and \(c_i d\) from columns \(x_i,\zeta\) and rows \(x_i^2,\zeta^2\). All minors vanish at \(K\zeta\). Thus the span has codimension one, its annihilator is evaluation at the distinguished point, and the distinguished line is unique. This result also holds for all chart laws with the given degree-two structure.

On a neighborhood with frames for the graded pieces, impose this codimension by rank minors and choose a nonzero pivot minor to compute the annihilator as a regular projective point. For coefficients \(e_{ij}\) of that point in the dual monomial basis, restrict to \(e_{ii}\neq0\) and recover the degree-one projective coordinates \(e_{ij}/e_{ii}\). For the split law this is the line \(K\zeta\), since evaluation has coordinates proportional to \(\zeta_i\zeta_j\). The recovered line has multiplication rank at most one on \(X\) there by density, and rank one and nonzero square on an open set around the endpoint. Its kernel therefore gives a regular complement. The two multiplication isomorphisms in the chart are open rank conditions. The same construction exhibits the chart as a locally closed rank locus of the ambient law space, where one imposes the equations for the unit, augmentation, powers, and recovered line. These equations are satisfied on \(X\) near each \(A_g\) because they hold on the dense orbit; all rank lower bounds and chosen pivots are open. This explains why the chart cuts out a neighborhood in \(X\) despite rank drops elsewhere in the ambient closure.

Here is a coordinate construction on that locus. The configuration consists of \(e,M,M^2,M^3,L,U\). The first four entries are an identity vector and a flag of the indicated dimensions, with \(e\notin M\). The last two give a line and a complementary hyperplane in \(M/M^2\). In an open flag chart choose regular lifts \(x_1,\ldots,x_n,z\) of a basis of \(U\) and a generator of \(L\), thereby identifying \(U\) with \(V\). The lifts can be fixed from the configuration by ordinary matrix pivots. Record the actual products \(x_i x_j,z^2\) as a linear map \(K^a\to M^2\) inducing an isomorphism onto \(M^2/M^3\), and record the cubic \(x_i x_j x_k\) as an isomorphism \(P\to M^3\). These are arbitrary choices subject to the invertibility conditions, and all their coordinates together with the flag give a smooth variety \(S\). Its dimension is
\[
 \dim S=2N-1+m(a+b)+ab+2n+a(a+b)+b^2 .
\]
Here \(2N-1\) counts \(e\) and \(M\), the next two terms count the two Grassmannian choices \(M^2,M^3\), and \(2n\) counts the line and complementary hyperplane. The last two terms count the quadratic lifts and the cubic basis maps.

In these coordinates multiplication is specified by the displayed monomial basis and by
\[
 z^3=h\in P,\qquad zv=\phi(v)\in P,\qquad
 \phi\in H=\operatorname{Hom}(V,P).
\]
All other mixed monomials of degree three vanish. For instance \(zvv'=(zv)v'=0\) because \(zv\in M^3\); the argument for \(z^2v\) is the same. Products of filtration degree at least four vanish. Conversely, prescribe those products using the chosen basis, the unit, and arbitrary \(h,\phi\). The result is associative: when three positive-degree factors all have filtration degree one, their triple product is the prescribed cubic \(x\)-monomial, \(z^3\), or zero for a mixed triple, independent of parenthesization. All triples of total filtration degree at least four give zero, and triples involving the identity obey associativity. The constructed flag, complementary hyperplane and line are recovered by the preceding rank tests. This constructs inverse regular maps between the law chart and the product with the pair \((h,\phi)\), since basis and pivot inversions are regular on the open sets on which they are used. The degree-two multiplication intrinsic to the recovered line uses these data and is independent of \((h,\phi)\). Any further pivot restrictions simply restrict the product to open subsets.

## Which laws are split and which lie on the orbit closure

Change the lift of \(z\) by an element of \(M^2\) with quadratic \(x\)-part \(u\in Q\). Change the lifts of \(v\in V\) by an element of \(M^2\) with \(z^2\)-coefficient \(\ell(v)\), where \(\ell\in V^*\). Lower-order data in the graded algebra stay fixed, while the mixed product changes by
\[
 \phi(v)\longmapsto \phi(v)+uv+\ell(v)h .
\]
The other terms of the lift changes make no contribution. For example \(z\) kills the quadratic \(x\)-monomials and \(z^2\) kills \(V\). All choices of \(u,\ell\) occur. A law is split, meaning isomorphic to its associated graded algebra, if and only if some lifts have all mixed products \(zv=0\). Sufficiency follows from the displayed presentation. For necessity a splitting provides such lifts because an isomorphism on the associated graded algebra preserves the intrinsic line and the kernel complement.

Let
\[
 J=\{\,v\mapsto uv:u\in Q\,\}\subseteq H,\qquad D=H/J.
\]
The dimension of \(J\) is \(q\). If \(h\neq0\), the map \(V^*\to D\) taking \(\ell\mapsto[v\mapsto\ell(v)h]\) is injective. A nonzero map \(v\mapsto uv\) has rank \(n\) because multiplication by a nonzero polynomial is injective. A map \(v\mapsto\ell(v)h\) has rank at most one. This also shows that the map \((u,\ell)\mapsto(v\mapsto uv+\ell(v)h)\) has rank \(q+n\) for every \(h\neq0\), in any characteristic.

For split algebras \(A_h,A_f\), isomorphism is equivalent to \(h\in\operatorname{GL}(V)f\). An isomorphism induces an associated graded isomorphism and hence acts by \(T\in\operatorname{GL}(V)\) and \(z\mapsto cz\) on the degree-one summands. The relation in degree three gives \(T\cdot f=c^3h\), or \((c^{-1}T)\cdot f=h\). Conversely a form change of basis extends to the algebra. Thus the orbit in the local coordinates is exactly the set with \(h\in\operatorname{GL}(V)f\) and \(\phi\in J+V^*h\), with all smooth data allowed.

Because \(K\) is algebraically closed, \(C\) is a cone, since nonzero scalars are cubes. Define the reduced closed variety
\[
 Y_C=\left\{\,(h,\psi)\in P\oplus D:
    \exists\, [\lambda]\in\mathbb P(C),\
    h\in K\lambda,\quad
    \psi\in\{[v\mapsto\ell(v)\lambda]:\ell\in V^*\}\,\right\}.
\]
For closedness, use the tautological line bundle \(\mathcal L\) on \(\mathbb P(C)\). The bundle \(\mathcal L\oplus(V^*\otimes\mathcal L)\) maps to the trivial bundle \(P\oplus D\). It injects fiberwise with constant rank by the preceding rank argument. Its image is a vector subbundle, as is seen on nonvanishing maximal minors, so its total space is closed in \(\mathbb P(C)\times(P\oplus D)\). The projection is proper. The part of that total space with \(h\in\operatorname{GL}(V)f\) is dense, because \(\mathcal L\) away from its zero section identifies with \(C\setminus\{0\}\) and the orbit is dense and open in \(C\). Thus its image has closure equal to the whole projected image. This is exactly the closure of the orbit pair \((h,[\phi])\).

After a linear splitting \(H\cong J\oplus D\), the chart of \(X\) therefore identifies with \(S\times J\times Y_C\), with the understood open coordinate chart restrictions. This equality is valid as reduced varieties. The ambient chart is locally closed, its intersection with \(X\) is open in \(X\), and the orbit is dense there. This proves the asserted local model at every point of the chart. For \(h\neq0\) the direction \([\lambda]\) in \(Y_C\) is forced to be \([h]\), and the remaining coordinate is an \(n\)-dimensional vector bundle over \(C\setminus\{0\}\). This proves the local product and the completed local ring formula.

## The zero boundary

The zero fiber of \(Y_C\to C\) consists precisely of the projected tensors \([v\mapsto\ell(v)\lambda]\) with \(\lambda\in C\). For \(n\geq3\) two nonzero rank-one tensors yielding the same class in \(D\) must coincide. Their difference has rank at most two, whereas every nonzero member of \(J\) has rank \(n\). In particular the form direction \([\lambda]\) is unique for every nonzero such class when \(n\geq3\).

Nonzero corrections occur over the zero cubic. Choose \(\ell\neq0\) and use the one-parameter family \(h=tf\), \(\phi(v)=\ell(v)f\), while fixing the smooth coordinates. For \(t\neq0\) it is a law on the orbit of \(A_f\), since \(\ell(v)f=t^{-1}\ell(v)h\) can be removed by a lift change. At \(t=0\) the correction cannot be removed by \(J\), by the rank argument. Its associated graded law is \(A_0\) and the law itself is nonsplit.

The point corresponding to \(A_0\) has \((h,\psi)=(0,0)\). If \(C\) spans \(P\), the cone \(Y_C\) spans \(P\oplus D\). The pairs \((h,0)\) span the first factor, and the projected tensors \((0,[\ell(\cdot)\lambda])\) span the second. The tangent space of a reduced affine cone at its vertex is its linear span, since its ideal is homogeneous and the only tangent equations at the vertex are linear. Hence the tangent space here has dimension \(b+nb-q\), while \(\dim Y_C=\dim C+n\) by the dense vector bundle over the nonzero part. The difference is at least \(nb-q-n>0\) for \(n\geq2\). A smooth factor preserves this tangent excess. In characteristic zero \(\operatorname{Sym}^3 V\) is irreducible as a \(\operatorname{GL}(V)\)-representation, so the span of any nonzero orbit is \(P\).

For an explicit contrast in characteristic zero, take \(n=2\), \(f=x^3+y^3\). Its orbit is the open set of binary cubics with three distinct projective roots, because projective changes of variables are transitive on triples of distinct roots, and an overall scalar is absorbed in a linear change of basis. Thus \(C=P\). Here \(a=b=4\), \(m=3\), \(N=12\), and \(\dim S=115\). The algebra closure is \(124\)-dimensional near \(A_0\), whose tangent space has dimension \(127\), although the form closure is smooth at zero. For an example at a nonzero endpoint, take \(f=x^2y\) and \(g=x^3\). The form closure is the reduced discriminant hypersurface, since binary cubics with a double and a distinct simple root are dense in the cubics with repeated roots and form one orbit. On the chart of nonzero \(x^3\)-coefficient, a change of variables eliminates the \(x^2y\) coefficient of the associated monic cubic. Its remaining discriminant equation is \(-4p^3-27r^2=0\) in the depressed cubic coefficients \(p,r\). The germ at \(g\) is a cusp times two smooth coordinates. The law chart at \(A_g\) gives the same cusp times \(122\) smooth coordinates.

## The local model in the full ordinary three-tensor orbit closure

The same reduced local singularity appears for the **ordinary three-tensor** of multiplication, with a further smooth factor of dimension $2N(N-1)$. The statement has the same characteristic scope as the ordinary unmarked law version above.

Express the tensor as a bilinear map $\beta:U_1\times U_2\to W$ between $N$-dimensional spaces. Fix nonzero elements $u_0,v_0$ that are the two input units at the split endpoint. On the open set where $A=\beta(-,v_0)$ and $B=\beta(u_0,-)$ are invertible, define
\[
m(x,y)=\beta(A^{-1}x,B^{-1}y),\qquad e=\beta(u_0,v_0).
\]
The law $m$ has unit $e$, and $Au_0=Bv_0=e$. Conversely a unital law $m$ and a pair of invertible frames with these specified columns recover $\beta=m(A-,B-)$. Both coordinate maps are regular on this open set. On a unit-coordinate chart one can complete $e$ to a basis by keeping the other columns fixed, so the frames form a product of two fixed smooth varieties, each an open subset of an affine space of dimension $N^2-N$. The unit itself is regular on the indicated law chart by the linear equations for the unit.

If $\beta$ is an ordinary tensor translate of the source multiplication, evaluating its two invertible slices shows that normalization above is an algebra law isomorphic to the source. More explicitly, in source coordinates the slices are multiplication by two units, and $m$ is the original multiplication scaled by their product inverse. Conversely if $m$ is in the algebra-law orbit, any allowed pair of frames gives an ordinary tensor translate. Thus the tensor orbit on the chart is the law orbit times the smooth frame factors. In the product chart its closure is the law closure times the same factors. This proves the claimed local model for reduced ordinary three-tensor orbit closures at the encoded endpoints, including the nonsplit zero boundary.

## Relation to the literature

Grochow and Qiao put cubic-form equivalence and algebra isomorphism into a common tensor-isomorphism complexity class. Grochow, Mulmuley and Qiao analyze orbit-closure degenerations in the study of border complexity. The chart above transfers the local geometry of a cubic-form orbit closure into an ordinary algebra orbit closure at nonzero endpoints, and computes the extra nonsplit degenerations at the zero boundary. [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110) · [Grochow, Mulmuley and Qiao, Boundaries of VP and VNP](https://doi.org/10.4230/LIPIcs.ICALP.2016.34)

Zwara studies smooth maps of module schemes that preserve orbit-closure singularities. Here the coordinates are on multiplication laws for varying algebras, with the smooth factors and a rank-one correction given explicitly. Elias and Rossi establish canonical grading for compressed short Gorenstein algebras, and Jelisiejew uses inverse-system orbits and their tangent spaces to compare short algebras with their associated graded algebras. The present algebra has a top socle piece of dimension \(b>1\), and its splitness on this stratum is governed by the lift-change formula. [Zwara, Smooth Morphisms of Module Schemes](https://www.cambridge.org/core/journals/proceedings-of-the-london-mathematical-society/article/abs/smooth-morphisms-of-module-schemes/84E1351A1629F7EDCA44ACDA1BF1E302) · [Elias and Rossi, Analytic Isomorphisms of Compressed Local Algebras](https://arxiv.org/abs/1207.6919) · [Jelisiejew, Classifying Local Artinian Gorenstein Algebras](https://doi.org/10.1007/s13348-016-0183-1)

An exhaustive finite control over the field of two elements checked associativity and the lift-change formula for all 4,096 binary tables, with 7,077,888 basis triples. It also checked distinct nonzero projected classes for all 7,161 nonzero rank-one tensors in the ternary defect example.

The claims are for the reduced orbit closures and the specified local rank chart. The proof is in prose, with no Lean verification or independent priority claim.
