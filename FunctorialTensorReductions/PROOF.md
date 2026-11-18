# Tensor-isomorphism reductions that act on all homomorphisms

Grochow and Qiao's Open Question 7.5 asks which of their tensor-isomorphism reductions can be made functorial on all homomorphisms. This note gives functorial replacements for several of the named reductions, including Theorem A over every field, and replacements for the group, alternating matrix-space, and associative and Lie algebra branches of Theorem B. The constructions preserve and reflect isomorphism. Their arrow maps are defined on every tuple satisfying the paper's covariant tensor equation, including rectangular and singular maps. [Grochow–Qiao, Part I, §2.4, Theorems A and B, and Open Question 7.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)

## 1. From ordinary tensors to unital associative algebras

A source object is a tensor $T\in V_1\otimes\cdots\otimes V_d$ over a field $F$. An arrow $T\to S$ is a tuple of linear maps $P_i:V_i\to V_i'$ with $(\bigotimes_iP_i)T=S$. The target arrows are unital $F$-algebra homomorphisms. For fixed $d$ the construction takes polynomial time in the tensor data and the explicitly presented mode dimensions.

First take $d\ge2$. Use core quiver vertices $v_0,\ldots,v_d,z$. At $v_{i-1}\to v_i$ the arrow space is $V_i$. There is a second arm $v_0\xrightarrow{a}z\xrightarrow{b}v_d$ of two fixed scalar arrows. Give each core vertex a positive, distinct number of private outward leaves. Each leaf has one incoming scalar arrow and no outgoing arrows. Use the $d+2$ counts $1,\ldots,d+2$, assigned in the fixed vertex order. Define
$$
A(T)=FQ/\langle ab-T\rangle,
$$
where paths multiply in traversal order and $T$ is identified with the vector in the space of main paths from $v_0$ to $v_d$. The relation has coefficient one on the tag path $ab$. For $d=1$ use the same construction on $T\otimes 1\in V_1\otimes F$, with second-mode map $1$ on every arrow.

On a source arrow, map core and leaf idempotents to their counterparts, map fixed arrows to themselves, and use $P_i$ on the $i$th arrow space. Extend by concatenation and linearity. The relation is carried to the relation in the target, so the resulting unital homomorphism is defined for every arrow. The image of each generator determines this map, so identities and compositions hold. The arrow restrictions also show faithfulness.

Here is a basis-explicit construction. List vertex vectors and all basis paths. Delete $ab$ and every $ab\ell$ with $\ell$ a private outgoing leaf arrow of $v_d$. These are the only paths containing $ab$, since $v_0$ has no incoming arrow and leaves have no outgoing arrows. The ideal is the linear span of $ab-T$ and $(ab-T)\ell$ for those $\ell$. Each of these vectors has a distinct deleted pivot and all other coordinates are on retained paths. Multiply basis paths by concatenation and rewrite the deleted paths by their tensor expressions. There are at most a constant depending on $d$ times $\prod_{i=1}^d(1+\dim V_i)$ paths, and every structure constant is zero, one, or an input coefficient (in the chosen bases). This gives the stated polynomial bound, also with a zero-dimensional mode.

For reflection, let $N$ be the arrow ideal in the quotient. It is nilpotent because the quiver is acyclic, and $A(T)/N$ is a product of copies of $F$. Thus $N$ is the Jacobson radical. Since the relation lies in the square of the original arrow ideal, the directed graph with arrow multiplicities is recovered from the idempotent components of $N/N^2$ for the primitive coordinate idempotents of $A(T)/N$. Every core vertex has at least one outgoing leaf and is therefore nonterminal, even if its variable arrow spaces vanish. The terminal vertices are exactly the leaves. The distinct numbers of outgoing terminal neighbors label the core vertices intrinsically. Every isomorphism $A(T)\cong A(S)$ consequently fixes the labels in the semisimple quotients.

The images of the chosen complete orthogonal family of vertex idempotents under such an isomorphism agree modulo the radical with the target idempotents, after naming the corresponding leaves. They can be made to agree exactly by an inner automorphism. In detail, for ordered idempotents $e_j,e_j'$ with these properties, $u=\sum_j e_j'e_j$ satisfies $u\equiv 1\bmod N$ and $ue_j=e_j'u$. It is invertible because $N$ is nilpotent. Conjugate by $u$ or $u^{-1}$ in the direction that identifies the families.

An isomorphism now maps each full vertex-to-vertex space $e_{v_{i-1}}A(T)e_{v_i}$ to its counterpart. This space is exactly $V_i$, since no longer path has those endpoints. Similarly the two tag arrow spaces are lines. Write $P_i$ for the recovered invertible maps and $a\mapsto\alpha a'$, $b\mapsto\beta b'$. The quotient contains the full main-path space from $v_0$ to $v_d$ injectively, because its basis paths were retained. Applying the isomorphism gives
$$
(\bigotimes_i P_i)T=\alpha\beta S.
$$
The nonzero scalar $\alpha\beta$ can be absorbed into $P_1$. This proves reflection. If the target category has named vertex idempotents, named tag arrows and named leaf arrows, the same construction is fully faithful into that category: a homomorphism preserving the names determines arbitrary linear $P_i$ on the full spaces $V_i$, and the tag relation gives exactly the source arrow equation.

The construction also works over a commutative local ring $R$ with finite free mode modules. The path normal forms are unchanged. The ideal of arrows remains nilpotent and the semisimple quotient is $k^{Q_0}$ for the residue field $k$. An $R$-algebra isomorphism reduces to one of the displayed field algebras and thus identifies the core labels modulo the Jacobson radical $J$. In the preceding conjugation argument $1+J$ consists of units, which suffices. Each recovered vertex-to-vertex map is an $R$-linear isomorphism of the corresponding free mode modules, and $\alpha,\beta$ are units. In a finite commutative ring, the same statement follows by applying this argument to each local direct factor. The finite coefficient ring is held fixed on morphisms, so its idempotents and their components are preserved.

Finally, any unital algebra $A$ is represented faithfully by its left multiplication algebra $\{L_a:a\in A\}\subseteq\operatorname{End}_F(A)$, since $L_a(1)=a$. Use the category of matrix spaces whose arrows $(P,\psi)$ satisfy $PX=\psi(X)P$, where $\psi$ is a linear map of the given matrix spaces. An algebra homomorphism $f$ gives $P=f$ and $\psi(L_a)=L_{f(a)}$. For invertible arrows this is exactly simultaneous conjugacy. Conjugacy of two such matrix spaces is algebra isomorphism by multiplication of their operators. This extends the associative matrix-algebra conjugacy branch of Theorem B to all such intertwining morphisms.

## 2. A common construction for the class-two Lie and cube-zero commutative branches

Write $T\in V_1\otimes V_2\otimes V_3$. We give two natural quotients of universal bilinear maps. In the Lie construction put $X=V_1\otimes V_2$. In the commutative construction put
$$
A_1=V_1\oplus F^2,\qquad
A_2=V_2\oplus A_1\oplus F,\qquad X=A_1\otimes A_2,
$$
and use the obvious injections to regard $T$ as a tensor with first two factors $A_1,A_2$. The dimensions of $A_1,A_2$ satisfy $2\le \dim A_1<\dim A_2$. Write $Y=V_3$ and put $D=X\oplus Y\oplus Fa\oplus Fb$, with $h=\dim D$. Denote these four ordered core blocks by $D_1,\ldots,D_4$. Take $M_i=(D\oplus F^2)^{\oplus i}$ for $1\le i\le4$, with distinct formal copies of these spaces. Put $M=\bigoplus_iM_i$ and $E=D\oplus M$. Use the universal pairing $C(E)=\bigwedge^2 E$ in the Lie case and $C(E)=\operatorname{Sym}^2 E$ in the commutative case. We denote its product symbol by $\star$.

Define $W(T)=C(E)/K_T$. The subspace $K_T$ is the direct sum of the following three kinds of relations.

1. Set $D_i\star M_i=0$ for each $i$. All other mixed core and marker blocks, and all marker-marker blocks, remain free.
2. Inside $C(X)$, quotient by the kernel of the following map on pure generators. In the Lie case take
   $$
   (u\otimes v)\wedge(u'\otimes v')\longmapsto
   (u u')\otimes(v\wedge v') .
   $$
   Here $u u'$ is the product in $\operatorname{Sym}^2 V_1$. In the commutative case take
   $$
   (u\otimes v)(u'\otimes v')\longmapsto
   (u\wedge u')\otimes (v\wedge v').
   $$
3. In $Fa\star Fb\oplus(X\star Y)$, quotient by the line $F(a\star b-T)$. Since $X,Y$ are distinct direct summands, $X\star Y=X\otimes Y$ canonically.

Both displayed maps are well-defined: in the Lie case the bilinear map is alternating, including characteristic two, and in the commutative case interchanging its factors changes two signs. All quotients are polynomial-time operations on explicit finite-dimensional bases.

Make an algebra $L(T)$ on $E\oplus W(T)$ by taking the product of two elements of $E$ to be the class of their universal product, and all products involving $W(T)$ to be zero. In the Lie case this alternating bracket satisfies Jacobi and gives a class-two Lie algebra. In the commutative case the product is commutative and associative and all triple products vanish. Adjoining a unit by $F\oplus L(T)$ gives the unital version of the commutative reduction. In a finite-dimensional nilpotent algebra its unitization has Jacobson radical the original nilpotent algebra, so reflection extends to this version.

The raw ordered dimensions are retained by adding an abelian summand $C_0(V_1,V_2,V_3)$ whose products with everything are zero. To obtain it functorially, set
$$
B(U,V)=\operatorname{Sym}^2(U\oplus V)\oplus V,\qquad
C_0(V_1,V_2,V_3)=B(B(V_1,V_2),V_3).
$$
For $s=\dim U+\dim V$, the dimension of $B(U,V)$ is $s(s+1)/2+\dim V$. The intervals for successive $s$ are consecutive and disjoint. Therefore $\dim C_0$ determines the ordered triple, also when one or more dimensions vanish. Write $\widehat L(T)=L(T)\oplus C_0$.

Each source arrow induces the indicated tensor-product and direct-sum maps on $X,Y,D$, the identity on scalar tag lines, and the corresponding maps on $M_i$ and $C_0$. Functoriality of symmetric and exterior powers gives preservation of the first two sets of relations, and the equation on $T$ preserves the third. The resulting quotient map on $W$ gives a homomorphism on $\widehat L$. These maps respect identities and compositions by construction.

### Recovery of the four core blocks

The bilinear map $\beta:E\times E\to W(T)$ has zero common radical. If $x=d+m$ with $m\ne0$, some $m'\in M$ has $m\wedge m'\ne0$ in the alternating case, and a nonzero $m'$ gives $m m'\ne0$ in the symmetric algebra case. Those components survive in the quotient. If $x\in D$ is nonzero, choose a nonzero component in $D_i$ and any nonzero marker vector from $M_j$ for $j\ne i$. The corresponding mixed component survives. Thus the quotient of $\widehat L$ by its center in the Lie case, or by its annihilator in the commutative case, is exactly $E$. The derived or product subspace is $W(T)$, since universal pair products span it. The quotient of the center or annihilator by $W(T)$ therefore reveals $\dim C_0$. In either case $E$ and $\beta$ are intrinsic parts of the object.

Consider the subspace $\ker\beta(x,-)$ in $E$. If the marker part of $x$ is nonzero, the marker part of every null partner lies in a space of dimension at most one. In the alternating case this follows from $m\wedge m'=0$, and in the commutative case from $m m'=0$ in the symmetric algebra. Thus the null space has dimension at most $h+1$. If $x\in D$ has at least two nonzero core components, the corresponding independent mixed constraints force every null partner to have zero marker part. If $x\ne0$ is in the single block $D_i$, a null partner has marker part precisely arbitrary in $M_i$, along with its allowed core part. Its null dimension is consequently in
$$
[\,i(h+2),\,i(h+2)+h\,].
$$
These intervals are disjoint and lie above $h+1$. The dimension of $E$ is $11h+20$, so $h$ is intrinsic. Each nonzero $D_i$ is therefore recovered by its null-dimension interval, adjoining the zero vector. A zero block is revealed by the absence of nonzero vectors in its interval.

### Recovery of the two factors of $X$

For the Lie pairing, let $x\in V_1\otimes V_2$ act as a linear map $V_1^*\to V_2$ and define $y$ similarly. If the indicated Lie projection of $x\wedge y$ vanishes, evaluating it on any covector $\phi$ gives $x(\phi)\wedge y(\phi)=0$. For rank-one $x=u\otimes v$, this forces the image of $y$ to lie in $Fv$. Indeed, fix $\phi_0$ with $x(\phi_0)\ne0$ and compare the equations at $\phi_0$ and $\phi_0+\phi$ for $\phi\in\ker x$. Conversely, a map $y$ with image in $Fv$ lies in the null space by the displayed projection. Thus $\ker\beta_X(x,-)=V_1\otimes Fv$. If $x$ has rank at least two, take covectors $\phi,\psi$ with independent images. Their proportionality scalars for $y$ are equal by considering $\phi+\psi$. Compare any other nonzero image with one of these independent images to equate its scalar, and use the preceding kernel argument with both images to conclude $y$ vanishes on $\ker x$. Hence $y=cx$. This also suffices for $\beta_X(x,y)=0$, since the projection is alternating. If both dimensions are at least two, this characterizes rank-one tensors by the larger null spaces and intrinsically distinguishes the family $V_1\otimes Fv$ among them. If a factor dimension is one, every invertible map on $X$ is already a product map. If a factor is zero the raw tensor is zero, and dimension recovery suffices for isomorphism reflection.

For the commutative pairing, the projection to $\bigwedge^2 A_1\otimes\bigwedge^2 A_2$ is the first variation of all $2\times2$ minors. For example the coordinate indexed by rows $i,j$ and columns $a,b$ is
$$
x_{ia}y_{jb}+y_{ia}x_{jb}-x_{ib}y_{ja}-y_{ib}x_{ja}.
$$
Put $x$ in diagonal rank-$r$ normal form with $r$ initial ones. For $r=1$ the null partners $y$ are precisely the matrices supported on the first row and first column, of dimension $\dim A_1+\dim A_2-1$. For $r=2$, every entry outside the initial $2\times2$ block is zero, and this block is subject to the single trace-zero condition. For $r\ge3$, all off-diagonal entries vanish by using an initial diagonal index distinct from the row and column, while diagonal entries beyond $r$ vanish by pairing with an initial index. The remaining diagonal entries satisfy $y_{ii}+y_{jj}=0$ for distinct $i,j\le r$. Thus the null dimension for all $r\ge2$ is at most three over every field. Since $\dim A_1+\dim A_2-1>3$, this characterizes rank-one tensors in all characteristics.

A linear isomorphism of rectangle spaces preserving rank-one tensors in both directions either preserves or interchanges the two families of maximal linear subspaces of decomposable tensors together with zero. Indeed, the sum of two decomposable tensors with both factor pairs independent has rank two. Applying this to all pairs in a linear subspace gives exactly the two possible families $Fa\otimes A_2$ and $A_1\otimes Fb$. In the commutative construction their dimensions are unequal, ruling out interchange. In the Lie construction the larger null spaces already fix the second family. To see that preservation of this family forces a product map, choose a basis $v_j$ in the second space and write the maps on its fibers as $u\otimes v_j\mapsto P_j u\otimes w_j$. Invertibility implies the $w_j$ form a basis. The rank-one condition of each image of $u\otimes(v_j+v_k)$ implies $P_j u,P_k u$ are proportional for every $u$; then $P_j^{-1}P_k$ is scalar by linearity on basis vectors and their sums. The resulting scalars are absorbed into the second factor map.

### Reflection and the group reduction

From any algebra isomorphism obtain the induced isomorphism on $E$ and infer that it maps $K_T$ onto $K_S$. The core blocks are preserved by the null-dimension argument. The tag lines are scaled by nonzero $\alpha,\gamma$. From the single relation in $Fa\star Fb\oplus(X\star Y)$ one gets
$$
(P_1\otimes P_2\otimes P_3) T=\alpha\gamma S
$$
on the original or padded modes. The scalar can be absorbed into $P_3$. For padded modes, each factor map carries the support of the padded tensor to the corresponding support of the other. For a tensor, its support in one mode is the span of the contractions by covectors on the other modes. These supports lie in the original summands. Use the induced isomorphism on each support and extend it to an isomorphism of the original mode spaces, which have equal dimensions by the construction with $C_0$. This proves the claimed reflection for the Lie and commutative constructions.

Over an odd prime field the Lie construction gives an all-homomorphism functor to groups of nilpotency class at most two and exponent dividing $p$. On the underlying Lie vector space use
$$
x*y=x+y+\tfrac12[x,y].
$$
Bilinearity and centrality give associativity, and multiplication by itself $p$ times is zero. Lie maps are group homomorphisms. Conversely, the group commutator is the Lie bracket and addition is recovered from $x*y$ by subtracting half of this central element, with the half expressed as an integer power. Every group homomorphism therefore preserves addition and $\mathbb F_p$-scalars, and is a Lie homomorphism. The group is specified by polynomially many polynomial-size matrices without writing a Cayley table: for a bilinear map $\beta$, the group element $(x,w)$ has faithful affine-linear action
$$
(z,t)\longmapsto(z+x,\ t+w+\tfrac12\beta(x,z))
$$
on $E\oplus W$, with the additional abelian summand included by independent translations. Composition gives the group law. Basis elements generate, and the affine action is given as a linear matrix on an extra homogenizing coordinate. This establishes the prime-field case of Theorem B's generating-matrix group target. Section 4 handles all odd-characteristic finite extension fields.

### Matrix-space version

The same construction gives a functor into actual alternating matrix spaces with their forward subspace morphisms: an arrow $P:E\to E'$ satisfies $(\bigwedge^2P)K_T\subseteq K_S$. To handle varying raw dimensions, replace $E$ by $E\oplus C_0$ and include all pair products involving $C_0$ in $K_T$, so its role is the intrinsic radical of the quotient pairing. Embed $\bigwedge^2 E$ into alternating matrices by $x\wedge y\mapsto xy^{\mathsf T}-yx^{\mathsf T}$, also in characteristic two. An invertible morphism in this category is exactly ordinary congruence of matrix spaces. The proof above on $E$ modulo the radical gives reflection. Over characteristic different from two, the commutative construction similarly gives symmetric matrix spaces using the natural isomorphism of $\operatorname{Sym}^2 E$ with symmetric tensors. These are matrix-space morphisms defined by subspace inclusion. On the canonical inclusion tensors with a separate coefficient slot, this construction does not assert a functor for the ordinary fully covariant tensor equation on that slot.

## 3. Scope and spectra

These are replacement constructions for the named isomorphism reductions. In particular, treating a tensor as an operation with contravariant inputs can express its invertible equivalences but does not by itself assign maps on all covariant arrows in §2.4 of the source. The path relation in §1 uses the tensor as a path vector, and the quotients in §2 use it as a quotient relation. Both choices give the correct direction of every singular map.

Question 7.5 also asks about asymptotic spectra. The ordinary tensor restriction preorder has a standard Strassen spectrum. Symmetric tensors with symmetric restriction also have one over $\mathbb C$. In the latter case, forgetting the symmetry induces the surjective pullback map on spectra proved by Christandl, Fawzi, Ta, and Zuiddam. For the elementary operation of grouping tensor modes by a fixed partition, the induced map on ordinary restriction semirings preserves multiplication, addition, the unit, and restrictions. For addition one deletes the unused mixed summands in the regrouped direct sum. The projection and inclusion both preserve the tensor, so deletion is equality in the restriction-equivalence quotient. Therefore grouping pulls spectral points back, even though it can identify nonisomorphic tensors. [Strassen spectra and symmetric restriction, Christandl–Fawzi–Ta–Zuiddam, Theorems 4.1–4.2](https://arxiv.org/pdf/2104.01130#page=16)

The unital algebra category with all unital maps and ordinary direct product as addition does not itself have a normalized hom-monotone spectrum of this form. There are unital maps $F\to F^2$ and $F^2\to F$, whereas any normalized additive spectral point would assign the values $1$ and $2$. Consequently the full-homomorphism algebra functor in §1 gives no such spectral pullback with these operations. Other preorders and the remaining reductions in Question 7.5 are separate.


## 4. The group reduction over every finite field of odd characteristic

Here the input field is $F=\mathbb F_{p^e}$, with $p$ odd. A direct restriction of scalars of a Lie construction can admit transformations that apply a field automorphism to the input. The following additional relations enforce $F$-linearity in the reflected mode maps.

Use the alternating construction of §2, and add eight new, individually labeled scalar blocks $Fc_1,Fd_1,\ldots,Fc_4,Fd_4$ to $D$. Their source arrow maps are identities. Assign private marker spaces for all twelve core blocks by the same rule $M_i=(D\oplus F^2)^{\oplus i}$, now for $1\le i\le12$. Let $\ell_i=c_i\wedge d_i$. Pick a field generator $\theta$ with $F=\mathbb F_p(\theta)$, which can be the generator in the given field presentation. In the four-dimensional space of the listed pair products impose two extra relations
$$
\ell_3-\ell_1-\ell_2=0,\qquad
\ell_4-\ell_1-\theta\ell_2=0.
$$
All other rules from §2 are unchanged. These extra relations have fixed coefficients and the arrow maps are identities on their generators, so the construction remains functorial on every $F$-linear source arrow. View the resulting Lie algebra as an $\mathbb F_p$-Lie algebra and apply the group law and explicit affine matrix representation from §2.

Let an $\mathbb F_p$-Lie isomorphism of two outputs be given. The center, its quotient by the derived algebra, and the quotient pairing are still intrinsic. The dimension formulas of §2 are now measured over $\mathbb F_p$ and all are multiplied by $e$. In particular $\dim_{\mathbb F_p} E=e(79h+156)$, since $\sum_{i=1}^{12}i=78$. Each nonzero core block $D_i$ is still identified by its interval $e[\,i(h+2),\,i(h+2)+h\,]$. The estimates depend only on the dimensions of vector spaces of solutions of $F$-bilinear equations, so restriction of scalars simply multiplies those dimensions. The two new bracket relations are entirely in core-core blocks and do not alter any of the marker estimates. The dimension of $C_0$ is recovered similarly. If a raw mode has zero dimension, both tensors are zero after reading their equal ordered dimensions. Hence it suffices to consider nonzero mode spaces.

Write $\Phi_i$ for the invertible $\mathbb F_p$-linear map on a nonzero core block. Suppose the pair product of two distinct core blocks $D_i,D_j$ survives as a free, independent summand $D_i\otimes_F D_j$. For any $a\in F$ and nonzero $x\in D_i,y\in D_j$, the identity $[ax,y]=[x,ay]$ in the source and its image in this summand of the target give
$$
\Phi_i(ax)\otimes_F\Phi_j(y)=\Phi_i(x)\otimes_F\Phi_j(ay).
$$
For nonzero $a$, equality of these pure tensors forces a single nonzero scalar $\sigma(a)$ with $\Phi_i(ax)=\sigma(a)\Phi_i(x)$ and $\Phi_j(ay)=\sigma(a)\Phi_j(y)$. Fixing $y$ and varying $x$, and then fixing $x$ and varying $y$, shows that the scalar is independent of both. Put $\sigma(0)=0$. Additivity, multiplicativity and preservation of $1$ follow from the invertible $\mathbb F_p$-linear maps, and finiteness makes the resulting injection of $F$ surjective. The surviving free mixed products give a connected graph on the core blocks. The original tag line $Fa$ has free products with $X,Y$ and all eight new scalar lines. The other original tag line $Fb$ has a free product with $Fc_1$. The same $\sigma$ therefore works on all core blocks.

On the four labeled products an isomorphism has $\Phi(\ell_i)=t_i\ell_i'$ for nonzero $t_i$, since it maps each scalar block to itself in the labeling. The action on scalar multiples of these brackets uses $\sigma$, by the preceding semilinearity on the inputs. Applying it to the first tag relation and using independence of $\ell_1',\ell_2'$ gives $t_3=t_1=t_2$. Applying it to the second gives $t_4=t_1$ and $t_4\theta=\sigma(\theta)t_2$. Thus $\sigma$ fixes $\theta$ and is the identity. All the core maps are $F$-linear, so the factor recovery and tag relation of §2 reflect the original $F$-tensor isomorphism.

This gives an all-homomorphism functorial replacement for Theorem B's group branch over its full odd-characteristic finite-field range. The matrices for the resulting group have entries in $\mathbb F_p\subset F$ and are polynomial in the input size, including the degree of the field presentation. The algorithm uses only explicit vector-space operations and the presentation's field generator. [Grochow–Qiao, Theorem B(1)](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)
