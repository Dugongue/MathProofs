# Free tensor isomorphism captures finitely presented modules over the same ring

Let $R$ be a nonzero commutative unital ring. On each side the input comprises three explicit finite presentations
$$
R^{c_i}\xrightarrow{L_i}R^{r_i}\xrightarrow{p_i}M_i\longrightarrow0
\qquad(i=1,2,3)
$$
and an array giving a representative of $t\in M_1\otimes_R M_2\otimes_R M_3$ in the tensor product of the three free covers. The primed input has its own presentations and tensor $t'$. An isomorphism consists of independent $R$-linear isomorphisms $M_i\to M'_i$ carrying $t$ to $t'$.

**Theorem.** This problem reduces in deterministic polynomial time to ordinary free 3-tensor isomorphism over $R$. With $f_i=r_i+r'_i$, the largest output side is at most
$$
O\!\left(1+\sum_i(f_i+c_i+c'_i)+\sum_{i<j} f_if_j\right).
$$
The presentations list their generators and relations explicitly. The construction only copies ring coordinates and inserts zero and one. In particular, it gives a bit-polynomial reduction over the integers and uniformly over $\mathbb Z/m\mathbb Z$ with $m\ge2$ supplied in binary. It requires no factorization of $m$. Under any unital map $R\to S$, the same comparison is exact for the scalar-extended presentations, input tensors and outputs. This includes nonflat base change.

Consequently the finitely presented interpretation of $\mathsf{3TI}_{R}$ equals $\mathsf{3FTI}_{R}$. This covers all finitely generated modules over a commutative Noetherian ring when the presentations are part of the input. Part V distinguishes these classes and gives complete problems for important free and finite local principal ideal formats. The reduction here relates the two classes over the same ring without requiring a principal ideal hypothesis. [Grochow–Qiao–Stange–Sun, Part V, Definitions 1.1–1.2 and Theorems 1.4 and 1.6](https://arxiv.org/html/2611.00735v1#S1.SS3)

## 1. Stabilize the free presentations

Suppose $p:P\twoheadrightarrow M$, $q:Q\twoheadrightarrow N$ are surjections from finite free modules, and $u:M\to N$ is an isomorphism. Choose linear maps $a:P\to Q$, $b:Q\to P$ lifting $u$ and $u^{-1}$ through the two covers. They exist by choosing preimages of the basis vectors' images. The map
$$
H(x,y)=\big(a x+y-a b y,\;x-b y\big)\qquad(P\oplus Q\to Q\oplus P)
$$
has inverse taking $(z,w)$ to $(w+b(z-aw),\,z-aw)$. On the target apply $q$ to the first coordinate. Since $q a=u p$ and $p b=u^{-1}q$, the result is $u p(x)$. Thus every $u$ lifts to an isomorphism after adjoining the other cover as a summand mapping to zero. This elementary stabilization also applies to two surjections onto a finitely generated submodule. It needs no flatness or projectivity of the quotient. The companion Lean proof gives the lift even when the two covers are projective.

For each input pair stabilize the covers to $F_i=R^{r_i}\oplus R^{r'_i}$ and $F'_i=R^{r'_i}\oplus R^{r_i}$. Write $K_i\subset F_i$, $K'_i\subset F'_i$ for the kernels of the new covers. On the unprimed side a list for $K_i$ consists of the original relation columns in the first summand and the standard basis of the second summand. The primed side uses the reversed construction. Use the first summand injections in all three modes to lift the supplied array to $\widetilde t\in F_1\otimes F_2\otimes F_3$. Define $\widetilde t'$ on the primed side in the same way. Every input isomorphism $u_i$ lifts to an isomorphism $A_i:F_i\to F'_i$ mapping $K_i$ onto $K'_i$.

For each $i$, use $j<k$ for the other two indices. Put $U_i=F_j\otimes_R F_k$. By the universal property of tensor products, the kernel of
$$
F_1\otimes F_2\otimes F_3 \longrightarrow M_1\otimes M_2\otimes M_3
$$
is the sum of the images $K_i\otimes_R U_i\to F_i\otimes_R U_i$, with factors put back in the original order. Indeed a trilinear map out of the three covers factors through the three quotients exactly when it vanishes whenever an input comes from a kernel. The quotient by the indicated sum has this same property. This description does not rely on preserving injective maps under tensor product.

## 2. Encode the quotients by marked free tensors

Let $E_i=U_i^*=\operatorname{Hom}_R(U_i,R)$ and $G_i=F_i\oplus E_i$. In each $G_i$, mark the submodules $F_i\oplus0$ and $K_i\oplus E_i$. Consider the single tensor
$$
\mathcal T=\widetilde t+\tau_1+\tau_2+\tau_3\in G_1\otimes G_2\otimes G_3,
$$
where $\tau_i=\sum_{a}e_a^*\otimes e_a\in E_i\otimes U_i$ in the corresponding order, and $(e_a)$ is the product basis of $U_i$. Each $\tau_i$ uses the $E$ summand in just position $i$. Its entries are zeros and ones. The freedom to alter the free lift of a quotient tensor will come from three independent linear maps on these summands.

The primed objects use the same recipe. An isomorphism of the marked modes has the form
$$
P_i=\begin{pmatrix} A_i&S_i\\0&D_i\end{pmatrix}:G_i\longrightarrow G'_i.
$$
Preserving $F_i\oplus0$ onto $F'_i\oplus0$ gives the invertible restriction $A_i$ and the invertible quotient map $D_i:E_i\to E'_i$. The other mark is transported onto its counterpart if and only if $A_iK_i=K'_i$ and $S_i(E_i)\subseteq K'_i$. In one direction restrict the marked map to the intersection with $F_i\oplus0$ and evaluate it on $0\oplus E_i$. Conversely for any $(x,y)\in G_i$, the first coordinate $A_i x+S_i y$ of $P_i(x,y)$ belongs to $K'_i$ exactly when $x\in K_i$. This gives equality of the marked submodules by bijectivity.

Expand $\otimes_i P_i$ on $\mathcal T$. The source tensor has no components with more than one $E$ summand, and the triangular maps send each $F$ into $F'$. Thus the only sectors to check are the three with one $E'$ factor and the all-$F'$ sector. In the sector with $E'_i$, the equality is
$$
(D_i\otimes B_i)\tau_i=\tau'_i,\qquad B_i=A_j\otimes A_k.
$$
Via $E_i\otimes U_i\simeq\operatorname{End}_R(U_i)$, coevaluation gives the identity. In the target, the left side gives $B_iD_i^*$, using the canonical double-dual identification of the finite free module. Consequently $D_i=(B_i^{-1})^*$ is necessary and sufficient. There is no further constraint on $S_i$ in these sectors.

The all-$F'$ equation is
$$
(A_1\otimes A_2\otimes A_3)\widetilde t+\sum_i(S_i\otimes B_i)\tau_i=\widetilde t'.
$$
As $S_i:E_i\to F'_i$ varies with image in $K'_i$, the term $(S_i\otimes B_i)\tau_i$ ranges over exactly the image of $K'_i\otimes U'_i$ in the all-$F'$ sector. In fact $(B_i e_a)$ is a basis of $U'_i$. Its coefficient at $B_i e_a$ is $S_i(e_a^*)$ and can be chosen independently in $K'_i$. Therefore this last equation can be met precisely when the maps induced by the $A_i$ on the quotients send $t$ to $t'$. The stabilizing lift in Section 1 ensures that every such triple of quotient isomorphisms admits the needed $A_i$. Taking the displayed $D_i$ and choosing the $S_i$ proves that it extends to an isomorphism of the marked tensors. Conversely any isomorphism of the marked tensors induces the three desired quotient isomorphisms.

To express the two marks using a fixed type of free tensor data, use an inclusion $F_i\to G_i$ for the first. For the second use the linear map from a free module with columns the listed generators of $K_i$, embedded in $F_i\oplus0$, and the basis vectors of $0\oplus E_i$. Pad the map's domain with the other input's number of columns mapping to zero. Its target submodule is its image. If a map $P_i$ carries the second mark onto its counterpart, apply Section 1 to the two surjections onto these marked images to lift its restriction to an isomorphism between the padded generator domains. Conversely an isomorphism of the linear-map data preserves the images. Thus these maps encode both marks. They may have dependent columns.

There are a fixed number of named free sorts and labelled tensors of order at most three, including the linear maps and the tensor $\mathcal T$. The sum of their ranks satisfies the bound in the theorem. The pairwise product sorts $E_i$ apply the arity reduction from 7.4. Coevaluation imposes the equations on pairs of factors and avoids an auxiliary sort for the full product of all three free covers.

## 3. Erase the marks over the original ring

The final step uses the fixed-type arbitrary-ring compiler from the earlier MathProofs linear-length reductions. Here are its construction and the ring-valid parts of the recovery argument. It converts a fixed list of typed tensors of order at most three on free sorts, with repeated names and both variances allowed, to one ordinary free 3-tensor, with side length linear in the sum of the ranks.

Convert the labelled tensors to bilinear data using free duality and pad unary or binary records with a scalar sort. Add multiplication on that scalar sort, so its transformation is the identity. For each sort and its dual provide reference indices, and give every data occurrence a private index tied to its appropriate reference. For each index $i$ put three copies $X_i,Y_i,Z_i$ of its free module in three modes, with added scalar positions $X_0,Y_0,Z_0$. Make one typed bilinear map $B:X\times Y\to Z$ on these direct sums. Include multiplication $X_0\times Y_0\to Z_0$, scalar-copy maps $X_i\times Y_0\to Z_i$ and $X_0\times Y_i\to Z_i$, and evaluate every dual reference against its primal reference in the first two modes with output $Z_0$. For a private occurrence $i$ with reference $r$, use a separate $Y$ scalar $s_i$. Use multiplication $X_0\times s_i\to Z_0$ and the identity scalar action $X_i\times s_i\to Z_r$. Finally put each data map in its private block. These rules use distinct input pairs.

An isomorphism preserving the designated $X,Y$ summands also preserves the designated $Z$ summands, as they are images of scalar-copy maps. If $a,b$ are its units on $X_0,Y_0$, its maps on $X_i,Y_i,Z_i$ are $a g_i,b g_i,ab g_i$ by the copy equations. Each scalar $s_i$ acts by $b$ and its other equation makes $g_i=g_r$. Evaluation forces the inverse transpose at each dual reference, since basis covectors and vectors detect all coordinates. The remaining equations are exactly those of the typed system after cancelling $ab$. Every typed-system isomorphism extends with $a=b=1$.

Erase the summand labels by an associative triangular algebra. Use diagonal vertices $0,1,2$, the corners $X,Y,Z$ in directions $0\to1$, $1\to2$, $0\to2$, respectively, and $B$ as their composition. To mark each $X_i$, add a private sink $s$ with corners $1\to s=R$, $0\to s=X/X_i$ and composition the scalar multiple of the projection. The left annihilator in $X$ of the corner $1\to s$ is exactly $X_i$. Use a private source $t$ and corners $t\to1=R$, $t\to2=Y/Y_j$ for each $Y_j$. The corresponding right annihilator in $Y$ is $Y_j$. These projection quotients are free, since these marks are summands of the typed bilinear map. No unfree quotient is used in the algebra. For each vertex so far add a private source with one arrow into that vertex. Give these marking corners distinct free ranks greater than the rank of every nonmarking corner. All unspecified off-diagonal compositions vanish. All nonzero compositions of two off-diagonal elements annihilate all further off-diagonal factors on either side. Associativity follows from that fact and the compatibility of scalar actions at the endpoints.

The sum $J$ of the off-diagonal corners is exactly the commutator ideal. The quotient is a product of copies of $R$, and $x=[e_v,x]$ for an off-diagonal corner starting at $v$, where $e_v$ is its source idempotent. Also $J^3=0$. Any algebra isomorphism induces an isomorphism on $J/J^2$ respecting its bimodule structure over the diagonal quotient. Over every residue field of $R$, the quotient diagonal idempotents are permuted. In $J/J^2$ every marking corner survives in full, and every other corner is a quotient of a free module of strictly smaller rank. Consequently the distinct marking corner dimensions identify both endpoints in the induced permutation over each residue field. Every vertex is an endpoint of a marker. Each diagonal idempotent is therefore fixed modulo every maximal ideal. An idempotent in the intersection of all maximal ideals vanishes, as its complement is a unit. Applying this also to complements gives preservation of the actual diagonal idempotents in the quotient over $R$.

If $f_v$ denotes the image of $e_v$ in the target algebra, let $u=\sum_v f_ve_v$ using the target standard idempotents in the second position. It is $1$ modulo $J$, hence a unit, and $f_vu=ue_v$. Conjugating the isomorphism by $u^{-1}$ preserves each actual vertex and corner. Taking the projection annihilators recovers the marks on $X,Y$, then the earlier copy equations recover the typed system. Conversely a summand-preserving isomorphism of the typed bilinear maps acts on the projection quotients by its induced maps and on the remaining scalar and marking corners by their fixed identifications. This extends to an algebra isomorphism.

Finally the multiplication tensors of two associative unital free algebras are ordinarily isomorphic precisely when the algebras are isomorphic. To see the converse direction, regard a tensor isomorphism as an isotopy $h(xy)=f(x)g(y)$ with three invertible linear maps. With $a=f(1), b=g(1)$ one has $h(x)=f(x)b=a g(x)$. Right multiplication by $b$ and left multiplication by $a$ are therefore bijective, so $a,b$ are units. For instance if $ac=1$, injectivity of left multiplication by $a$ gives $ca=1$. Substitution yields $h(xy)=h(x)b^{-1}a^{-1}h(y)$, so $x\mapsto (ab)^{-1}h(x)$ is a unital algebra isomorphism. An algebra isomorphism gives an isotopy by taking all three maps equal. The number of vertices, corners and marks is fixed by the finite data type. The marking ranks can be the largest nonmarking rank plus distinct positive offsets. The algebra rank and the ordinary tensor sides are thus linear in the sum of the ranks of the typed input sorts. The multiplication table uses coordinate copies and the structural entries zero and one. This proves the asserted reduction with the stated bound.

## 4. Consequences and verification

**Uniform quotient transfer.** Let $I=(a_1,\ldots,a_s)\subset R$ and suppose the input coefficients in $R/I$ are supplied by lifts to $R$. Ordinary free 3-tensor isomorphism over $R/I$ reduces to ordinary free 3-tensor isomorphism over $R$. Present each free quotient mode $(R/I)^n$ by the relation columns $a_l e_j$. Its $R$-linear maps are exactly the $R/I$-linear maps. For modules annihilated by $I$, the tensor products over $R$ and over $R/I$ agree because they have the same balanced maps. Apply the theorem. Taking $R=\mathbb Z$, $I=(m)$ gives uniform reductions from $\mathbb Z/m\mathbb Z$ to integral free 3-tensor isomorphism, including the prime fields, with output side $O(1+\sum_i n_i+\sum_{i<j}n_in_j)$ on dimensions $(n_1,n_2,n_3)$. Copying the input lifts and $m$ gives polynomial binary output time uniformly in $m\ge2$.

**Base change.** After a unital homomorphism $R\to S$, the cokernels of the matrices over $S$ are exactly $S\otimes_R M_i$ by right exactness. Their kernels are the images of the scalar-extended relation matrices. Thus Sections 1 and 2 apply over $S$ using those new images, even if tensoring the original kernel inclusion lost injectivity. The free product and dual bases and the final multiplication tables commute with scalar extension entry by entry. The same compiler works for every nonzero $S$, and comparison over the zero ring is automatically affirmative on both sides. This equivalence concerns existence of transporters over each test ring separately. Their lifts use choices made over that test ring.

**Scope.** The proof uses the arity reduction from [MathProofs, tensor isomorphism universality](https://github.com/Dugongue/MathProofs/tree/main/GrochowProofTransfersIII) and the fixed-type compiler from [MathProofs, linear-length ring reductions](https://github.com/Dugongue/MathProofs/tree/main/IsomorphismCohomologyCrossovers). The comparison with fixed finite rings further uses the earlier [prime-power tensor results](https://github.com/Dugongue/MathProofs/tree/main/PrimePowerTensorIsomorphism). The new assertions here are the stabilized quotient and coevaluation reductions, with quadratic side lengths in the free-cover ranks. A transporter $x\mapsto2x$ on $\mathbb Z/5\mathbb Z$ already illustrates the need to stabilize the usual rank-one integral presentation, since the units of $\mathbb Z$ are $1,-1$. The full argument is written. The accompanying Lean source checks the stabilized lift and the submodule constraint on the shear, and the finite replay checks the sector identity and residual adjustments over rings with zero divisors. Historical priority remains unverified.
