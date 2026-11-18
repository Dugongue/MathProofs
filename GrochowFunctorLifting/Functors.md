# Functorial tensor reductions for all linear restrictions

Grochow and Qiao’s Open Question 7.5 asks which of their tensor reductions extend from isomorphisms to all homomorphisms, and how this relates to asymptotic spectra. Their source morphism from $T$ to $T'$ is a tuple of linear maps $f_i:V_i\to V'_i$ with $(\bigotimes_i f_i)T=T'$. The maps may be singular and the dimensions may change. The following gives positive answers for several of the reduction directions, using replacement object constructions where needed. The target categories are ordinary categories with all their homomorphisms. The scope does not exhaust the question. [Grochow–Qiao, §2.3 and Open Question 7.5](https://par.nsf.gov/servlets/purl/10494304)

**Results.** For every field and fixed $d\ge3$, $d$-tensor isomorphism has polynomial-size kernel reductions functorial on all such maps to associative algebras, to commutative cube-zero algebras and their unitalizations, and to class-two Lie algebras. For $d=3$, trilinear form equivalence with the same map on all modes also admits such a reduction over every field. For characteristic different from two and three the corresponding reduction to cubic form equivalence is likewise functorial. Further functors below cover symmetric and alternating matrix-space tensors, matrix conjugacy under its intertwiner convention, and class-two exponent-$p$ groups over odd finite fields. The underlying spaces remain part of the input, including for zero tensors and degenerate supports.

## Associative algebra by a relation in the full path space

Take vertices $0,\ldots,d$, with arrow space $V_i$ from $i-1$ to $i$. The path algebra uses the tensor product $V_{i+1}\otimes\cdots\otimes V_j$ for the space of paths from $i$ to $j$, with composition by concatenation. Add at each vertex $i$ a private loop space $K^{i+1}$ whose elements kill the radical and whose only nonzero multiplication outside the radical is the scalar action of their own vertex idempotent. This is an associative algebra, since the loop spaces are square-zero bimodules over the diagonal quotient. Quotient by $KT$ in the full path space from $0$ to $d$, meaning the zero subspace when $T=0$. This line is a two-sided ideal because neither end of such a path can be extended.

A tensor morphism induces the tensor product of its factor maps on each path space and fixes the vertex idempotents and private loops. The relation is preserved because $T$ maps to $T'$. This gives a unital algebra homomorphism. Identity and composition follow from identity and composition of tensor products.

The radical $J$ consists of the positive paths and private loops, because it is nilpotent and the quotient is $K^{d+1}$. From $J/J^2$ as a bimodule over this quotient, the private diagonal dimensions $i+1$ identify all vertices, including those adjacent to a zero-dimensional arrow space. The off-diagonal blocks identify the $V_i$. Multiplication induces a canonical map from the tensor product of these $d$ arc blocks to $J^d$, since replacement of any representative by a vector in $J^2$ changes the product by a vector in $J^{d+1}=0$. Its kernel is exactly $KT$. An algebra isomorphism therefore gives invertible factor maps carrying the tensor's line to the other tensor's line. For nonzero tensors, rescaling one factor then gives an actual tensor isomorphism. If that line is zero, both tensors are zero and the recovered dimensions suffice.

This supplies a functorial version of the associative-algebra direction of Theorem A. The original presentation uses a tensor as a contraction into a last arrow space, so its invertible-arrow formula uses an inverse transpose. The line relation above permits arbitrary linear restrictions and still reflects isomorphism. The algebra and induced maps can be built by tensor products and Gaussian elimination. Their sizes are polynomial in the explicit dimensions and tensor data.

## Commutative cube-zero and class-two Lie algebras

First consider three factors $U,V,W$. A degree-one space is a direct sum of five named summands
$$
H=Ke\oplus U\oplus V\oplus W\oplus X,\qquad X=U\otimes V.
$$
Use the degree-two space $Z=X_2\oplus((X\otimes W)/KT)$, where $X_2$ is a copy of $X$. The nonzero products are the canonical $U\times V\to X_2$, the identification $(\lambda e,x)\mapsto\lambda x$ from $Ke\times X\to X_2$, and the quotient $X\times W\to(X\otimes W)/KT$. The product is symmetrized for a commutative algebra, or extended by skew symmetry and zero on pairs within each named summand for an alternating Lie bracket. The latter convention also gives an alternating bracket in characteristic two. Degree two annihilates the whole algebra. Thus the commutative multiplication is associative and cube-zero, or the bracket satisfies Jacobi and has class at most two. The products span $Z$.

Define the maps on the degree-one summands by $e\mapsto e$, the stipulated tensor factor maps, and $f_U\otimes f_V$ on $X$. The maps on degree two are the tensor product on $X_2$ and the induced quotient map on $(X\otimes W)/KT$. These preserve the indicated products. To recover the summands in the ordinary unmarked algebra, use the following intrinsic construction.

### Recovering the summands without putting markings in the target category

Write $H=\bigoplus_{i=1}^s H_i$ and $D=\dim H$. Add degree-one spaces $L_i=K^i\oplus H$, of distinct dimensions $D+i$, and degree-two spaces $H_i\otimes L_i$. The only new products are $H_i\times L_i\to H_i\otimes L_i$ by tensoring. All products of two $L$ vectors are zero, and all degree-two elements annihilate the algebra. In the Lie case use the chosen product sign on each ordered pair and its negative on the reverse. On a morphism use $\mathrm{id}_{K^i}\oplus f_H$ on $L_i$ and the induced tensor map on its product space, where $f_H$ is the direct sum of the specified core maps. The assignments preserve composition for every source morphism.

For either algebra let $A^2$ be the span of products. It is exactly the declared degree-two space, and $P=A/A^2$ carries the induced bilinear product into $A^2$. The dimension formula
$$
\dim P=(s+1)D+\sum_{i=1}^s i
$$
determines $D$. The set of $p\in P$ whose multiplication map from $P$ has rank at most $D$ is precisely $L=\bigoplus_i L_i$. For $p\in L$ it vanishes on $L$. If the $H_i$ component of $p$ is nonzero, multiplication on $L_i$ is injective and has rank $D+i>D$.

The product of an element of $L$ with the quotient $H=P/L$ is well-defined because $L^2=0$. For $\ell\in L$ its annihilator in $H$ is the sum of those $H_i$ for which $\ell_i=0$ or $H_i=0$. Among these annihilators, the maximal proper ones are $K_i=\bigoplus_{j\ne i} H_j$ indexed by the nonzero $H_i$. Let $L_0$ be the subspace of $L$ annihilating all of $H$. Then
$$
\dim\operatorname{Ann}_L(K_i)-\dim L_0=\dim L_i=D+i,
$$
which labels each $K_i$ intrinsically. Intersect the $K_j$ for the other nonzero summands to recover $H_i$ itself. The unrepresented labels correspond precisely to zero spaces. Finally the old degree-two space and product are recovered by quotienting $A^2$ by the span of products with $L$. Thus every ordinary algebra isomorphism induces an isomorphism of the full core preserving its named summands.

### Recovering the input tensor

In the core of the three-factor construction, multiplication by $e$ identifies $X$ with $X_2$. If an induced isomorphism maps $e$ to $\lambda e'$, its map on $X$ is therefore $\lambda^{-1}(f_U\otimes f_V)$, by comparison with the $U\times V$ product. The kernel of the product map $X\otimes W\to Z$ is the tensor line. That line is preserved and the input tensors are isomorphic, by rescaling one factor if needed. This also handles a zero input tensor and zero-dimensional factors.

For any fixed $d$, replace the grouped product $U\otimes V$ by the internal nodes of a binary tree on the $d$ factors. Each nonroot internal node has a degree-one space given by its tensor product of leaves and a degree-two copy of that space. Its child product is the canonical tensor product into that copy. Multiplication by the same named scalar $e$ identifies the node with that copy. The root child product lands in the full tensor space modulo $KT$. Distinct child pairs and scalar products give exactly the indicated core. Each node map under an isomorphism is a nonzero scalar times the product of its leaf maps, by induction comparing the child and scalar products. The root kernel thus recovers the tensor line. The tree size is fixed for fixed $d$, and its spaces are polynomial in the explicit dimensions and tensor input.

Unitalization $K\oplus A$ gives a commutative unital algebra and maps all algebra homomorphisms here to unital homomorphisms. Its radical is $A$, so it still reflects isomorphism. This gives functorial versions of both commutative-algebra directions and the class-two Lie direction of Theorem B.

## Trilinear forms with one map acting in all three positions

For $S=U\oplus V\oplus W$ put
$$
E=S\oplus (K\oplus S)^{\otimes3}\oplus((K\oplus S)\otimes U)\oplus V.
$$
Regard $T$ as a tensor in $E^{\otimes 3}$ using the three separate summands $U,V,W$ in its respective positions. Each source morphism acts by the corresponding direct-sum and tensor-product maps on $E$. Its same-map tensor cube carries $T$ to $T'$.

If an invertible same-map transporter exists between two outputs, it takes the minimal support of each mode to the minimal support of the corresponding mode. A mode support here is the image of the flattening obtained by contracting the other modes. Its subspace is contained in its named summand of $S$. The output dimension is
$$
s+(s+1)^3+(s+1)\dim U+\dim V,\qquad s=\dim S.
$$
For fixed $s$ the last two terms are base-$s+1$ digits and recover all three dimensions. The intervals of possible values for successive $s$ are disjoint, since the gap in the cubic term exceeds $s(s+1)+s$. The case $s=0$ has one possible input shape. Thus any output isomorphism gives factor maps on the mode supports that can be extended to invertible maps on the original spaces. This is the all-morphism reduction to trilinear form equivalence in the same-space, all-covariant convention of §2.2.

## Cubic form equivalence

Assume the characteristic is different from two and three. We use symmetric three-tensors, identified with cubic forms by polarization with the same covariant convention for linear substitution. All operations below are over the input field.

Let $D(T)$ be the sum of the dimensions of the three minimal mode supports of $T$. An arbitrary tensor morphism cannot increase any of those dimensions, by applying its factor map to the corresponding support. Put $b=D(T)+1$ and $c_i=b^{2i}$ for $i=1,2,3$.

Start with one semantic copy of each factor. For each mode $i$ add $c_i$ disjoint pairs of leaf spaces, each pair consisting of copies of the other two factors. Form a symmetric tensor on the direct sum as follows. On the three semantic spaces include the symmetrization of $T$. For each leaf pair in family $i$, include another copy of the symmetrization of $T$ using semantic mode $i$ and that pair. Symmetrization means summing the six placements on the three named spaces. It has multilinear value exactly the corresponding contraction of $T$ when each input lies in its prescribed space.

A source morphism maps all semantic copies by the given maps, and maps the first $c'_i$ leaf pairs to the corresponding target pairs by those same factor maps. It sends all remaining pairs to zero. Because the numbers of copies cannot increase, this is well-defined and composes exactly as initial-segment truncation. Every surviving term becomes the required target term.

### Keeping the original dimensions and the support sum

Padding by unused spaces can make the original shape and $D(T)$ recoverable from the total output dimension, without including any extra tensors. Write $S=U\oplus V\oplus W$, $s=\dim S$, and $a=s+1$. The preceding tensor construction's ambient dimension $N_0$ is less than $a^9$ for $s\ge1$, since $c_i\le a^6$ and each pair has dimension at most $s$. Append the following spaces:
$$
(K\oplus S)^{\otimes14},\quad
(K\oplus S)^{\otimes9}\otimes U,\quad
(K\oplus S)^{\otimes10}\otimes V,\quad
(K\oplus S)^{\otimes11}\otimes K^{D(T)}.
$$
The maps on these spaces are the induced tensor maps, with the last factor using coordinate truncation on $K^{D(T)}$. The dimension is $a^{14}+N_0+a^9\dim U+a^{10}\dim V+a^{11}D(T)$. The values for successive $s$ are disjoint, since the extra terms are less than $a^{12}$ and the gap to $(a+1)^{14}$ is larger. For fixed $s$ the base-$a$ digits recover $\dim U,\dim V,D(T)$ and hence $\dim W$. For $s=0$ the output dimension is one and there is only one shape. The padding is polynomial in the explicit dimensions and has no tensor entries.

### Recovering the three modes from the cubic

Write $E_{\rm eff}$ for the effective dual space of the output cubic obtained by quotienting its common contraction kernel. It is the direct sum of the duals of the original supports and their copies in the leaves. To verify this, a nonzero effective semantic component gives a nonzero contraction on a paired leaf block, because $T$ is concise on its supports. A pure leaf vector with a nonzero effective component gives a nonzero contraction paired with the unique partner leaf copy and its semantic mode. These blocks have disjoint leaf pair names, so the indicated contractions cannot cancel. Padding and unused directions within copies are exactly the discarded directions.

Write the resulting symmetric trilinear form as $P$. In this paragraph $D=D(T)$. The pure leaf subspace $L$ is exactly the set of vectors whose contraction $P(x,-,-)$ has rank at most $2D$. A pure leaf contraction has only an off-diagonal block between semantics and leaves, and hence has rank at most $2D$. If $x$ has a nonzero semantic component in mode $i$, the restriction to pairs of leaves in family $i$ has rank at least $2c_i>2D$. The leaf admixture contributes zero to this restriction. For $D=0$ the tensor is zero and the input shape already suffices.

For $h$ in the quotient $H=E_{\rm eff}/L$, use the well-defined bilinear form $B_h=P(h,L,L)$ on $L$. The independence of the lift follows from $P(L,L,L)=0$. Its rank is the sum over $i$ of $2c_i$ times the rank of contraction by the $i$-th semantic component of $h$. The inequalities $D\sum_{j\le i}c_j<c_{i+1}$ for $i=1,2$ therefore recover an intrinsic flag
$$
H_1\subset H_1\oplus H_2\subset H
$$
by the rank cutoffs $2c_2$ and $2c_3$.

The core trilinear form descends canonically to $H$ by evaluating on any complementary section $R$ of $L$ satisfying $P(R,R,L)=0$. The original semantic subspace is one such section. To prove independence, any other is its graph under a linear map $u:H\to L$. For all $x,y\in H$ and $\ell\in L$ its defining condition gives
$$
B_x(u(y),\ell)+B_y(u(x),\ell)=0.
$$
For three vectors, apply cyclic versions of this equality with the third vector's leaf image. The three terms with one semantic input and two leaf inputs in the resulting cubic each sum pairwise to zero. Since two is invertible they all vanish. The terms with one leaf or three leaves already vanish. Thus the two sections give the same core trilinear form.

Evaluate this core form on one vector of the first flag step, a representative of the second step modulo the first, and a representative of the third step modulo the second. It depends only on the three indicated choices in the associated graded spaces, because the core is zero unless all three distinct semantic modes occur. It is precisely the original trilinear contraction of $T$ on its three supports. Every output isomorphism induces a transporter on these supports. Extend to the original three spaces using the recovered dimensions as before. This proves an isomorphism-reflecting functor to cubic form equivalence for every field of the claimed characteristic.

## Symmetric and alternating matrix-space tensors

There is also a direct all-morphism reduction to the symmetric and alternating tensor types with first two factors the same space $E$ and third factor an independent space $F$. Symmetry means the fixed points of transposition in $E\otimes E$. Alternation uses the subspace generated by $x\otimes y-y\otimes x$, with zero diagonal in characteristic two. The maps act by the same linear map on both copies of $E$. These are the tensor types behind the symmetric and alternating isometry directions of Theorem B.

Use semantic spaces $U,V$ in $E$ and $W$ in $F$. Use the same three families of leaf pairs as for the cubic construction, with $c_i=(D+1)^{2i}$ and with copies on their corresponding side $E$ or $F$. Include the core and tag copies of $T$, now symmetrizing or alternating just the two $E$ positions. Use the same coordinate truncation on morphisms. Append the shape and support-sum padding from the cubic construction to $E$ alone, with $N_0$ now its unpadded dimension. The same numerical bounds and digit decoding apply.

Write the resulting form as $P$ with two inputs from the effective $E$ dual and one from the effective $F$ dual. The effective duals consist exactly of the semantic support duals and their leaf copies. A nonzero effective semantic component gives a nonzero contraction on its separate leaf blocks. A nonzero leaf component gives a nonzero contraction with its semantic mode and the partner in its own pair. The uniqueness of each paired slot prevents cancellation.

A pure $E$ leaf has contraction rank at most $D$ on $E\times F$, since the two nonzero blocks pair semantic $E$ with leaf $F$ or leaf $E$ with semantic $F$. A nonzero semantic $U$ or $V$ component has rank at least $c_i>D$ on its paired leaf blocks. This identifies $L_E$, the pure $E$ leaf subspace. For the contraction on $E\times E$ by a vector in $F$, the corresponding cutoff is $2D$, since a nonzero $W$ component gives rank at least $2c_3$. This identifies $L_F$. Denote the two semantic quotients by $H_E,H_F$. The rank of $P(x,L_E,L_F)$ on $H_E$ distinguishes the $U$ step $H_U$ with cutoff $c_2$. A pure $U$ component has rank at most $Dc_1<c_2$, while a nonzero $V$ component gives rank at least $c_2$.

Choose complements $R_E,R_F$ of the two leaf spaces satisfying $P(R_E,L_E,R_F)=0$. The original semantic complements satisfy this condition. Relative to them another such pair is given by maps $u$ from $H_E$ to $L_E$ and $v$ from $H_F$ to $L_F$. The condition for a semantic $x,z$ and a leaf input $\ell$ is
$$
P(u(x),\ell,z)+P(x,\ell,v(z))=0.
$$
When $\ell$ is from the $W$ family, the second term is zero because both leaves in that family lie in $E$. Varying $z$ and $\ell$ therefore forces all $W$-family components of $u(x)$ to vanish. When $\ell$ is from a $U$ or $V$ family, the first term is zero. Varying $x$ and $\ell$ forces the corresponding $F$-leaf coordinate of $v(z)$ to vanish. The tests isolate every leaf pair and are nondegenerate on each effective mode support, so $v=0$ and $u$ has no component in the $W$ family. Expansion on the new complements gives the same core trilinear form. A contribution with two $E$ leaves would need the $W$ family, and a contribution with one leaf and two semantics is zero. This proof works in every characteristic.

Evaluate the decoded core on $H_U$, $H_E/H_U$, and $H_F$. The result is the original tensor on its three supports. Use the padding to extend to invertible source factor maps. Thus these are functorial versions of the two matrix-space isometry directions in their shared-factor tensor categories.

## Matrix-space and matrix-algebra conjugacy via intertwiners

For operators we explicitly use the intertwiner category. A source and target are vector spaces $E,E'$ with operator subspaces $\mathcal M,\mathcal M'$. A morphism is a pair of linear maps $g$ and $\eta$ from $E,\mathcal M$ to $E',\mathcal M'$ respectively with $g a=\eta(a)g$ for every $a$ in the source operator space. If the operators form an algebra, require that $\eta$ respect its operations. Composition is componentwise and isomorphisms are exactly conjugacies.

Build a bimap with named left spaces $U,X=U\otimes V$ and right spaces $V,W,Ke$. Its outputs are $X_2$ and $(X\otimes W)/KT$. Products are $U\times V$ tensoring into $X_2$, $X\times Ke$ scalar multiplication into $X_2$, and the quotient of $X\times W$ tensors. One may first pad each input space with $K$ and leave the tensor in the original summands. This is functorial, makes every named space nonzero, and still reflects isomorphisms by restriction to supports and extension to the smaller original dimensions.

Write $P_0,Q_0$ for the existing left and right spaces. To left summand $P_i$ attach a right leaf of dimension $\dim Q_0+i$ using $K^i\oplus Q_0$. Its product with $P_i$ is the canonical tensor product into a private output. Attach left leaves to right summands by the same rule using $P_0$, with separate private outputs. All other leaf products are zero. Call the resulting bimap $\mu$ on $P\times Q$ with output $Z$. The two total input dimensions recover $\dim P_0,\dim Q_0$ by the dimension formula of the one-space tags. Pure left leaves have left multiplication rank at most $\dim Q_0$. A nonzero semantic component has larger rank on its private right leaf, so the left leaf space is intrinsic. The right side is analogous. Maximal proper annihilators of right leaf vectors in $P_0$ are the complements of the named summands, labeled by the dimensions of their right leaves. The left leaves recover the right types. Quotienting the output by products involving leaves recovers the core. Its two maps into $X_2$ force the transporter on $X$ to be a scalar times the tensor product of the first two factor maps. Its remaining product recovers the tensor line as kernel. Every map comes from the specified direct-sum, tensor and quotient morphisms.

The bimap has zero common annihilator in both inputs and its values span $Z$. This follows from the private tags for every semantic summand and the nonzero semantic summand attached to each leaf. Put $E=Z\oplus Q$ and let $N_p$ act from $Q$ to $Z$ by $\mu(p,-)$ and kill $Z$. The space $N(P)$ has common kernel $Z$ and sum of images $Z$. A conjugacy therefore gives a bimap isomorphism on the operator parameter $P$, the quotient $Q$, and $Z$. An arbitrary source morphism gives the intertwiner $f_Z\oplus f_Q$, with operator map $N_p\mapsto N'_{f_Pp}$. This supplies a functorial reduction to Matrix Space Conjugacy in this category.

The unital algebra $K I\oplus N(P)$ has square-zero radical $N(P)$ and scalar quotient. Its algebra conjugacies preserve the radical and again reflect tensor isomorphism. The morphism extends by fixing the scalar coefficient. For the matrix Lie version, use the ordered associative product of the earlier class-two construction, placing each indicated product in just one order and setting the reverse product to zero. Its commutator is the earlier Lie bracket. The left regular representation on the unitization is faithful on this space, so it gives a matrix Lie algebra of class at most two. All the induced associative algebra maps intertwine the left multiplication operators. A conjugacy preserves the bracket on the operator space and hence reflects tensor isomorphism.

## The group direction over odd finite fields

Let $K$ have odd characteristic $p$. For a reduction to the ordinary group category, the class-two Lie algebra constructed above must reflect input isomorphism even after restricting scalars to $\mathbb F_p$. The following extra products do this for every finite extension $K/\mathbb F_p$.

Pad the original factor spaces by one dimension as in the bimap construction so that all named spaces are nonzero. Add four named one-dimensional $K$ summands generated by $a_1,a_2,b_1,b_2$. Put the following products, in the indicated order for the alternating bracket, into one shared new degree-two $K$-line with basis $z$:
$$
a_1 b_1=z,\quad a_1 b_2=z,\quad a_2 b_1=z,\quad a_2 b_2=\gamma z,
$$
where $\gamma$ generates $K$ over $\mathbb F_p$. Also add the canonical product between $Ka_1$ and each old semantic summand into its own new copy. Apply the sort recovery tags to all the semantic summands, both old and new. For every source morphism the four new generators remain fixed.

The same sort recovery works for an $\mathbb F_p$-linear isomorphism, with ranks and dimensions multiplied by $\dim_{\mathbb F_p} K$. Since every semantic summand is nonzero, the private leaf $L_i$ is exactly the annihilator in the leaf space of the complement of its associated semantic space $H_i$. The tag product $H_i\times L_i\to H_i\otimes_K L_i$ forces the two factor maps to be semilinear for the same field automorphism. To see this, compare the images of $(\lambda x)\otimes y=x\otimes(\lambda y)$ for nonzero $x,y$. Equality of nonzero elementary tensors gives
$$
f(\lambda x)=\sigma(\lambda)f(x),\qquad
g(\lambda y)=\sigma(\lambda)g(y).
$$
The scalar is independent of both nonzero choices, and additivity and multiplication prove that $\sigma$ is a field automorphism. The products with $a_1$ force the automorphism to agree across the old semantic summands and the $a_1$ line. The four scalar products share an output, so their factor maps have this same automorphism as well. Write $c_{a_i},c_{b_i}$ for the nonzero scalings on the four generators. The first three identities give $c_{a_1}=c_{a_2}$ and $c_{b_1}=c_{b_2}$. The fourth then forces $\sigma(\gamma)=\gamma$. Thus the induced core isomorphism is $K$-linear and yields the original tensor isomorphism.

On the additive space of the resulting Lie algebra take the group law $x*y=x+y+\tfrac12[x,y]$. The group has class two and exponent $p$. Brackets are recovered by group commutators, and addition is recovered by undoing half the commutator in the product. Thus arbitrary group homomorphisms preserve the $\mathbb F_p$-Lie structure, and all Lie homomorphisms give group homomorphisms in this construction. To give generators as matrices, use the faithful affine left action
$$
x\longmapsto
\begin{pmatrix}I+\tfrac12\operatorname{ad}(x)&x\\0&1\end{pmatrix}.
$$
The images of $\mathbb F_p$ basis vectors generate because the group operations recover addition and prime-field scaling. This yields the required polynomial-size output in the matrix-generator model, and is functorial for all the input morphisms.

## A spectrum consequence with explicit field scope

Christandl, Fawzi, Ta and Zuiddam already define the symmetric tensor spectrum and relate it by a surjective restriction to the ordinary tensor spectrum in their algebraically closed setting. The following direct argument gives the surjective spectral restriction for cubics over any field of characteristic different from two and three. It uses their symmetrizing tensor and the same general extension theorem. [Christandl–Fawzi–Ta–Zuiddam, Lemma 3.8 and Theorems 4.2–4.3](https://arxiv.org/pdf/2104.01130#page=15)

Use direct sum and Kronecker product of symmetric three-tensors and the preorder of same-map restrictions. The diagonal tensors have their usual order by flattening rank. Each nonzero cubic has a nonzero scalar evaluation, since the field is infinite or has more than three elements. Every scalar is a sum of four cubes because $(t+1)^3+(t-1)^3+2(-t)^3=6t$. Thus a nonzero cubic can restrict to the tensor unit after taking a bounded direct sum of its copies. Conversely polarization expresses each cubic as a linear combination of cubes, and the scalar identity expresses each coefficient by cubes as well. So every cubic is a restriction of a finite diagonal tensor. The Strassen preorder axioms now follow using the compatibility of restrictions with direct sum and Kronecker product. As usual zero tensors with unused coordinates may be identified with zero by mutual restriction.

Let $h$ be the sum of the six permutations of $e_1\otimes e_2\otimes e_3$. If $g=(P_1\otimes P_2\otimes P_3)f$ for symmetric $f,g$, then $f\otimes h$ restricts to $g$ by one map in all three positions. On the copy labeled $i$ use $a_iP_i$ with $a_1a_2a_3=1/6$. Commutation with the permutations gives six copies of $g$ with this common coefficient. Consequently for any symmetric spectral point $\phi$ the ordinary restriction $f\to g$ gives
$$
\phi(g)^n\le \phi(f)^n\phi(h)
$$
by applying the same gadget to the $n$-th Kronecker powers, using just one additional $h$. Taking $n$-th roots shows $\phi(g)\le\phi(f)$. Therefore every symmetric spectral point descends to the ordinary tensor subsemiring formed by the classes admitting a symmetric representative. Its value is independent of the ordinary isomorphism representative because the argument applies in both directions. Strassen's subsemiring extension theorem extends it to an ordinary spectral point. Forgetting symmetry thus has a surjective pullback of spectra.

The other functors above are kernel reductions on objects and preserve all source morphisms. No compatibility with direct sum or Kronecker product is asserted for them. This distinction is material for the last clause of Open Question 7.5.
