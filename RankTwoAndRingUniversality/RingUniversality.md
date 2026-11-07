# Compiling free-module tensor systems over arbitrary commutative rings

## Statement

Let \(R\) be a commutative ring with identity. Fix a bound on the order of a component tensor. A named system of mixed tensors on finite free \(R\)-modules reduces by a deterministic many-one reduction to ordinary 3-tensor isomorphism over \(R\). The number of named sorts and component tensors may grow with the input. Each sort carries one invertible linear map, and a dual occurrence carries its contragredient. The reduction outputs free-module tensors, and uses no divisions or rank computations. For dense coordinate inputs the output has polynomial size, with exponent depending on the order bound. Every output coefficient is an input coefficient, zero, or one. In particular, fixed-degree formal polynomial equivalence and associative unital algebra isomorphism in the finite-free basis model reduce to ordinary free-module 3-tensor isomorphism over arbitrary commutative rings. Conversely, ordinary free-module 3-tensor isomorphism reduces to finite-free associative unital algebra isomorphism.

The proof uses a free triangular algebra before taking its multiplication tensor. The named sorts and equations are recovered by canonical off-diagonal corners. Sections 6–8 prove the reverse reductions from free 3-TI to matrix tuple conjugacy, symmetric and alternating matrix tuple congruence, commutative associative unital algebra isomorphism, and symmetric and alternating trilinear form equivalence. We assume \(R\ne0\), since the zero ring gives trivial isomorphism within a prescribed input format. A sort with no nonzero-rank tensor product involving it can be omitted after comparing its ranks on both sides. Thus dimensions are bounded by explicit input lengths even when zero-sized components are supplied.

## 1. A shared module and list of marked polynomials

Let \(D\ge 3\) be at least the component order bound. Form a free module \(W=Rt\oplus\bigoplus_a W_a\), using one \(W_a\) for each individual slot and a primal and a dual reference summand of the appropriate rank for each named sort. Name all summands, including \(Rt\), separately. For a tensor of order \(r\) on its \(r\) distinct slot copies, its coefficient array specifies an element of \(\operatorname{Sym}^r W\) homogeneous of degree one in each of those copies. This multihomogeneous part of the symmetric power is canonically the tensor product of the slot copies, over any \(R\). Multiply by \(t^{D-r}\) to make degree \(D\).

Add degree-\(D\) polynomials for each reference primal–dual identity tensor and for the identity between each slot and the opposite reference of its sort. These tensors have degree 2 on their two summands and are multiplied by \(t^{D-2}\). A pair of matrices acting on an identity tensor preserves it exactly when one is the inverse transpose of the other. Hence a block-diagonal map on \(W\) fixing \(t\) preserves these identity polynomials exactly when every slot carries the prescribed map of its named sort or its contragredient. On those maps the remaining polynomial equations are exactly the original tensor equations. The two instance sides have the same format and the same identity polynomials. A scalar order-zero component, if included, can first be compared directly across the two instances and omitted.

The argument below works for any labeled list of degree-\(D\) polynomials \(F_c\) whose coefficient of \(t^D\) is zero, under block-diagonal maps fixing \(t\). For an ordinary degree-\(d\) form on a single base space \(V\), use \(W=Rt\oplus V\) with one polynomial \(t^{D-d}f\) for \(D=\max(3,d)\).

## 2. Construct the algebra

There are a source 0 and a next vertex 1, with corner \(0\to1\) a copy of \(W\). For each polynomial \(F_c\), add a chain \(0,1,2_c,\ldots,D_c\), with the vertices after 1 private to that chain. Every forward corner within a chain at distance \(j-i\) is \(\operatorname{Sym}^{j-i}W\), except that the corner \(0\to D_c\) is

\[
\operatorname{Sym}^D W\big/R(F_c-t^D).
\]

This corner is free with the basis of degree-\(D\) monomials other than \(t^D\). Multiplication along a chain is symmetric multiplication, followed by the quotient when it lands in the terminal corner. The quotient relation can be imposed consistently because the terminal corner cannot be multiplied by another forward chain corner on either side. Associativity then follows from associativity of symmetric multiplication. If there are no polynomials one can add an identically zero labeled polynomial.

For each named summand \(W_a\), including the \(t\)-line, add a private sink \(z_a\), a scalar corner \(1\to z_a\), and a corner \(0\to z_a\) equal to the sum of all summands of \(W\) other than \(W_a\). Define the only two-step product ending at \(z_a\) as scalar multiplication after the projection from \(W\) to that complement. The kernel in the \(0\to1\) corner of multiplication by the whole \(1\to z_a\) corner is exactly \(W_a\). No product of three off-diagonal elements ending at this sink can be nonzero.

For each vertex \(i\) so far, add two private sources \(s_{i,1},s_{i,2}\) with one corner \(s_{i,h}\to i\) each, of dimension \(M_{i,h}\). All marking dimensions are distinct and larger than the rank of every corner before adding the private sources. Products of two off-diagonal corners involving one of these marking corners are zero, even if their endpoints match. All unspecified off-diagonal corners and products are zero. Give each vertex its diagonal copy of \(R\), acting by scalar multiplication on incident corners. Diagonal identities \(e_i\) are orthogonal and sum to the unit. This defines a finite free associative \(R\)-algebra. In particular, the common initial edge introduces no mixed-chain product since every directed continuation stays in one chain. Any associativity identity involving a marking corner and at least one other off-diagonal factor has both sides zero.

## 3. Recover the constraints from arbitrary algebra isomorphisms

Let \(J\) be the sum of all off-diagonal corners. It is nilpotent because every off-diagonal product strictly advances in an acyclic directed order. It is intrinsically the two-sided ideal generated by commutators. The quotient by \(J\) is commutative, and an element \(x\) in any corner \(i\to j\) with \(i\ne j\) satisfies \([e_i,x]=x\).

The \((R^k,R^k)\)-bimodule \(J/J^2\) is intrinsic, where \(R^k=A/J\). In this bimodule the surviving nonzero corners are the consecutive chain edges, the scalar arrows to the projection sinks, and the private source marking corners. Every longer chain corner is spanned by products of shorter corners, by the monomial basis, including after the terminal quotient. Each projection output is spanned by products because the projection is surjective. Thus all the surviving corners are free and of the stated ranks. Over each residue field \(R/\mathfrak m\), an algebra isomorphism induces a permutation of the primitive idempotents of \((R/\mathfrak m)^k\). The unique bimodule corner of rank \(M_{i,h}\) fixes its two endpoints \(s_{i,h}\) and \(i\). This determines the permutation at every maximal ideal. An \(R\)-algebra map \(R^k\to R^k\) is given on each standard idempotent by entries that are idempotent in \(R\). If such an entry reduces to 0 at every maximal ideal it is zero, since an idempotent in the Jacobson radical is zero. If it reduces to 1 everywhere, apply the same argument to its complement. Therefore the induced map on \(A/J\) fixes the vertex labels over \(R\) itself.

Write \(e'_i\) for the images of the diagonal idempotents under an algebra isomorphism to the second instance. The element \(u=\sum_i e'_i e_i\) equals 1 modulo nilpotent \(J\), so is a unit. The identity \(e'_i u=u e_i\) shows that conjugating the given isomorphism by \(u^{-1}\) makes it preserve the actual diagonal idempotents. It now acts by invertible linear maps on all corresponding named corners. In particular the first edge map \(G\) preserves each summand of \(W\), by the projection kernels. It acts on \(t\) by a unit \(c\in R^*\).

Consider two consecutive edge maps \(G_i,G_{i+1}\) in one chain. The unquotiented distance-2 corner implies

\[
G_i(x)G_{i+1}(y)=G_i(y)G_{i+1}(x)\quad\text{in }\operatorname{Sym}^2W.
\]

Distance 2 is unquotiented because \(D\ge3\). Apply the induced symmetric action of \(G_i^{-1}\) and put \(Q=G_i^{-1}G_{i+1}\). For distinct basis vectors \(e_a,e_b\), the identity \(e_a(Qe_b)=e_b(Qe_a)\) forces \(Q_{ab}=Q_{ba}=0\) by the square coefficients, and \(Q_{bb}=Q_{aa}\) by the mixed coefficient. Thus \(Q\) is a scalar matrix, with unit scalar by invertibility. The rank-one case has the same conclusion directly. Since all chains share the first edge, each chain edge is a scalar multiple of \(G\).

The length-\(D\) products span the terminal corner. Their images are given by \(a_c\operatorname{Sym}^D(G)\) before taking the quotient, where \(a_c\) is the product of the edge scalars and is a unit. Therefore \(\operatorname{Sym}^D(G)(F_c-t^D)\) lies in \(R(F'_c-t^D)\). Since \(G\) preserves \(Rt\) and its chosen complement, neither transformed \(F_c\) nor \(F'_c\) contains \(t^D\). Comparing that coefficient gives

\[
\operatorname{Sym}^D(G)F_c=c^D F'_c.
\]

Hence \(c^{-1}G\) fixes \(t\) and carries every marked polynomial exactly to its target. Section 1 recovers a mixed tensor-system isomorphism. Conversely any such system isomorphism extends to \(W\), fixes \(t\), and extends to the entire algebra by the same map on all edges, its symmetric powers on chain corners, the induced complement maps on projection outputs, and identities on scalar and marking corners. This establishes both directions.

## 4. One ordinary tensor

The multiplication of any finite free associative unital \(R\)-algebra \(A\) is a tensor in \(A^*\otimes A^*\otimes A\). An ordinary equivalence between two multiplication tensors is equivalent to three invertible \(R\)-linear maps \(L,M,H:A\to B\) satisfying \(H(xy)=L(x)M(y)\). Put \(a=L(1)\) and \(b=M(1)\). The identities \(H(x)=L(x)b\) and \(H(y)=aM(y)\) show right multiplication by \(b\) and left multiplication by \(a\) are invertible linear maps. This makes \(a,b\) units: solve \(a a'=1\), then injectivity of left multiplication gives \(a'a=1\), and the right-multiplication argument is analogous. The linear isomorphism \(P(x)=a^{-1}H(x)b^{-1}\) has \(L(x)=aP(x)\) and \(M(x)=P(x)b\), so \(P(xy)=P(x)P(y)\) and \(P(1)=1\). Conversely an algebra isomorphism is such a triple using the same map on each algebra copy. The algebra construction thus produces one ordinary tensor instance. Its use on an ordinary tensor regarded as a one-component system also proves the reverse reduction to associative unital algebra isomorphism.

## 5. Complexity and relation to prior work

There are polynomially many vertices and corners in the input format. A chain corner has at most \(\binom{\operatorname{rank}W+D-1}{D}\) basis vectors. The marking ranks may be chosen as one plus the maximum preceding corner rank plus a vertex index. Thus the algebra rank and the dense size of its multiplication tensor are polynomial for fixed \(D\). Coordinates can be assembled directly. In a terminal corner a monomial product is either a retained monomial or \(t^D\), which is replaced by the input coefficients of \(F_c\). The construction needs no factorization, division, rank oracle, or ring-dependent algorithm. It is a coordinate projection with constants in the natural explicit coefficient model.

Futorny, Grochow and Sergeichuk establish tensor-system universality over fields. Grochow and Qiao use path algebras in Theorem B of their first paper. The present construction uses labeled corners detected in the commutator ideal, quotients by monic marked polynomials, and the classical rigidity of associative multiplication isotopy. The proof is informal. [Futorny–Grochow–Sergeichuk](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Theorem B](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full) · [Albert on isotopy](https://doi.org/10.2307/1968960)

The previous MathProofs mixed compiler supplies the field precedent for named primal and dual occurrences. The indexed Axiom Stacks declaration `SymmetricAlgebra.GradedAlgebra.liftι` records the graded symmetric-algebra interface, and Physlib's `SymmetricAlgebra.adjoin_range_ι` records generation in degree one. Here the monomial basis makes the specific spanning argument explicit over arbitrary rings. These library references identify reusable interfaces. The new arbitrary-ring reductions have no Lean certificate here. [MathProofs mixed compiler](https://github.com/Dugongue/MathProofs/blob/main/BalancedOrdinaryReduction.lean) · [Axiom Stacks symmetric grading](https://github.com/AxiomMath/Stacks/blob/5ed82d14634e8d9576bb844c7bd4e3da66d450e7/StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SymmetricAlgebraGrading.lean) · [Physlib degree-one generation](https://github.com/leanprover-community/physlib/blob/4e2182f2b6f0a54207a2fa62002c264217f875d6/PhyslibAlpha/Mathematics/SymmetricAlgebra.lean)

## 6. Matrix conjugacy and congruence

Apply the first construction to an ordinary tensor regarded as a one-component mixed system, obtaining the tagged triangular algebra \(A\). The left-regular image \(a\mapsto L_a\) is a split inclusion into \(\operatorname{End}_R(A)\) because evaluation at 1 sends \(L_a\) to \(a\). Thus conjugacy of the tuple of left-multiplication matrices of a basis, allowing invertible changes of the tuple index, implies conjugacy of the image subalgebras and hence isomorphism of the original algebras. Conversely an algebra isomorphism conjugates their regular images. This proves the reverse reduction for the matrix-conjugacy action.

For congruence use the free module \(W=A\oplus A^*\) and the family of bilinear forms indexed by \(a\in A\)

\[
J_a((x,\phi),(y,\psi))=\psi(ax)+\epsilon\phi(ay).
\]

Here \(\epsilon=1\) gives symmetric forms and \(\epsilon=-1\) gives alternating forms, including characteristic 2. The family is a split copy of \(A\), since the values \(J_a((1,0),(0,\psi))\) determine \(a\). An algebra isomorphism gives a congruence of the families using its action on \(A\) and the inverse transpose on \(A^*\).

For the converse, the matrix of \(J_a\) is \(\bigl(\begin{smallmatrix}0&L_a^t\\\epsilon L_a&0\end{smallmatrix}\bigr)\). A congruence with tuple-index change sends the invertible \(J_1\) to some invertible \(J'_b\). This makes \(L_b\) invertible, so \(b\) is a unit by the argument of Section 4. The congruence conjugates the algebra generated by \(J_1^{-1}J_a\) to the algebra generated by \((J'_b)^{-1}J'_{a'}\), as \(a'\) varies. Under the faithful representation

\[
A\times A^{\mathrm{op}}\longrightarrow\operatorname{End}_R(W),\qquad
(u,v^{\mathrm{op}})\longmapsto\operatorname{diag}(L_u,L_v^t),
\]

the first algebra is generated by \((a,a^{\mathrm{op}})\). Replacing 1 by a unit \(b\) gives generators \((d,(bdb^{-1})^{\mathrm{op}})\), with \(d=b^{-1}a\) arbitrary. Applying an inner automorphism on the opposite factor identifies the two generated algebras.

Write \(J\) for the off-diagonal ideal of \(A\). The algebra generated by the diagonal pairs is exactly

\[
D(A)=A\times_{A/J}A^{\mathrm{op}}.
\]

Indeed the quotient \(A/J\) is commutative, so the generators lie in the indicated fiber product. The product of the pairs for \(a,b\), minus the pair for \(ab\), is \((0,(ba-ab)^{\mathrm{op}})\). The commutators span \(J\), so these differences supply \(0\times J^{\mathrm{op}}\), and subtracting from diagonal pairs supplies \(J\times0\). Every element of the fiber product is then a sum of available elements.

One can recover \(A\) from any isomorphism of these constructed \(D(A)\) algebras. The commutator ideal in \(D(A)\) is \(J\times J^{\mathrm{op}}\), using \([e_i,x]=x\) in each off-diagonal corner. Its quotient by its square has a copy of every original surviving arrow in each direction. For each tag rank \(M_{i,h}\), the two copies identify its unordered endpoint pair over every residue field. The intersection of the pairs for \(M_{i,1}\) and \(M_{i,2}\) is precisely vertex \(i\). The other endpoint of each pair is its respective private source, so every vertex is fixed. Apply the idempotent and conjugation arguments of Section 3 to make an isomorphism preserve the diagonal idempotents in \(D(A)\). For every original forward ordered pair \(i\to j\), the corresponding corner in \(D(A)\) is exactly that corner of the first factor, because \(A\) has no backward corner. These forward corners and the diagonal form a subalgebra isomorphic to \(A\). Thus an isomorphism of the constructed \(D(A)\) algebras implies \(A\cong A'\).

For the symmetric power interpreted as quadratic polynomials, use the family \(q_a(x,\phi)=\phi(ax)\). The full mixed polarization of these quadratics is \(J_a\) with \(\epsilon=1\), even in characteristic 2. Thus polynomial family equivalence implies the congruence just proved sufficient, and the converse is induced by the original algebra isomorphism. This handles both the symmetric bilinear and the formal quadratic versions of the second action.

## 7. Commutative associative unital algebra isomorphism

For the symmetric family in Section 6 define \(\beta:W\times W\to A^*\) by \(\beta(w,w')(a)=J_a(w,w')\). Its values span \(A^*\), since \(\beta((1,0),(0,\psi))=\psi\). On the free module \(C=R\oplus W\oplus A^*\) define a commutative associative unital algebra by ordinary scalar multiplication, by \(ww'=\beta(w,w')\), and by requiring the last summand to annihilate \(N=W\oplus A^*\). In particular \(N^2=A^*\) and \(N^3=0\). Family congruences extend to algebra isomorphisms by duality on the tuple index.

To prove the converse, let \(C\to C'\) be an algebra isomorphism. Over each residue field the image of \(N\) is the nilradical, so the reduction of the \(W\)-component map \(X:W\to W'\) induced by the given isomorphism is an isomorphism on \(N/N^2\). Hence \(X\) itself is invertible over \(R\). Write \(r(w)\) for the scalar component of the image of \(w\in W\). For distinct basis vectors \(x,y\) in one of the two halves \(A,A^*\) of \(W\), the source product \(xy=0\), since each half is isotropic for every \(J_a\). Taking the \(W'\)-component of the target product gives

\[
r(x)X(y)+r(y)X(x)=0.
\]

Apply \(X^{-1}\) and compare coefficients. Both scalars vanish. Each half has rank at least two in the triangular construction, so \(r\) vanishes on all of \(W\). It then vanishes on \(N^2=A^*\) by multiplicativity and the spanning products. Applying this reasoning to the inverse isomorphism proves that \(N\) is preserved, and consequently \(N^2\) is preserved. The induced maps on \(N/N^2\) and \(N^2\) recover the congruence of \(\beta\), hence the symmetric family congruence of Section 6. This proves the claimed equivalence even when \(R\) has nilpotents.

## 8. Single symmetric and alternating trilinear forms

Let \(C\) be any finite free commutative associative unital algebra. On two named summands \(C,C\) and a third \(C^*\), use the formal cubic \(f_C(x,y,\phi)=\phi(xy)\). For the symmetric trilinear version, take its full mixed-coefficient polarization. For the alternating trilinear version, define the form by zero on tuples of pure summand vectors with a repeated summand and by the signed evaluation \(\phi(xy)\) on the six orders of the three distinct summands. The latter is the exterior tensor obtained by putting each structure constant in the wedge of one basis covector from each of the three summands, in order. Every algebra isomorphism extends to an equivalence of all three forms.

In both trilinear versions the centroid recovers \(C\). Each typed pairing separates each argument using the unit and free dual. To isolate an off-diagonal centroid block from summand \(i\) to summand \(j\), insert two inputs from \(i\) and one from the remaining summand \(k\), then move the centroid action from the first input to the \(k\) input. The latter expression is zero and the former is the typed pairing with the indicated block. Thus all off-diagonal blocks vanish. For a typed triple in its fixed order, the diagonal equations read \(\phi((Px)y)=\phi(x(Qy))=(S\phi)(xy)\). The signs are the same on both sides because the order of the slots stays fixed. Setting \(x\) or \(y\) to 1 shows that \(P,Q\) are both multiplication by the same element of \(C\), and that \(S\) is the dual multiplication map. Conversely these maps give the entire centroid. Its algebra under composition is therefore canonically \(C\). For formal cubic equivalence, apply the symmetric mixed-coefficient polarization before taking the centroid. Neither trilinear argument divides by a factorial.

All constructions from Section 6 onward are polynomial in the dimensions of the supplied bases. Their coefficients use copies, zero, one and, in the alternating construction, signs. The reverse reductions give each of the five free-module actions of Grochow–Qiao–Stange–Sun Theorem 3.7 the same polynomial-time degree as ordinary free-module 3-TI over every commutative ring, with the respective symmetric and alternating interpretations specified above. The ring sequel proves those equivalences under its diagonal-full hypothesis. The arbitrary-ring equivalences here are an extension of that theorem. The sequel's separately stated characteristic-two matrix tuple isometry algorithm question remains distinct from these equivalences. [Grochow–Qiao–Stange–Sun, Theorem 3.7](https://arxiv.org/html/2611.00735v1#S3.SS3)
