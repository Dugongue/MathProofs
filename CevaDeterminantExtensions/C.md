# Lifting Ceva determinant characters through local-ring quotients

Let $R$ be a nonzero finite commutative local ring, $U=R^\times$, and $\Gamma\le U$. Fix a connected simple graph $G=(V,E)$, a root vertex $v_0$, integer weights $b_v$ with $\sum_v b_v=0$, and one pair of tensors over $R$ on each edge. Construct the Ceva algebra $A$ once over $R$. At every proper quotient $S=R/I$, use the base-changed algebra $A_S=A\otimes_R S$. In particular its markers, matrix sizes and list of payload occurrences are inherited from $A$. Write $\Gamma_S$ for the image of $\Gamma$ in $S^\times$.

For each $S$, let $\mathcal P_S$ be the partition into components of the graph whose edges are the tensor pairs that are nonisomorphic over $S$. Put $b_C=\sum_{v\in C}b_v$, $k_S=|\mathcal P_S|$, and $g_S=\gcd(\exp\Gamma_S,\{b_C:C\in\mathcal P_S\})$. Exponents of trivial groups are 1. A normalized axis action is the tuple $(x_v/x_{v_0})_{v\in V}$ induced by an algebra automorphism on the designated source-to-sink coordinate space of the Ceva construction, after diagonal idempotent alignment. The normalization removes a common scalar.

**Theorem.** The subgroup of normalized axis actions on $A_S$ is
$$
X_S=\{x\in\Gamma_S^V:x_{v_0}=1,\ x|_C\text{ is constant for every }C\in\mathcal P_S\}.
$$
The determinant character on this group is $\eta_S(x)=\prod_v x_v^{b_v}$. In particular
$$
\det\operatorname{Aut}_S(A_S)=\Gamma_S^{g_S}
\quad\text{and}\quad
\#\{\text{determinant-one orbits in the ordinary multiplication-tensor orbit}\}
=[S^\times:\Gamma_S^{g_S}].
$$

For a further proper quotient $S\to T$, let $K=\ker(\Gamma_S\to\Gamma_T)$. Fix a lower action $x\in X_T$ and a prescribed higher determinant $\delta\in\Gamma_S$. It is possible to realize a higher algebra automorphism of determinant $\delta$ whose normalized axis action reduces to $x$ exactly under these two conditions.

1. The coordinates of $x$ are constant on every component in $\mathcal P_S$.
2. For any lift $\widetilde x\in X_S$ of $x$, the quotient $\delta/\eta_S(\widetilde x)$ lies in $K^{g_S}$.

When the conditions hold, there are exactly $|K|^{k_S-1}/|K^{g_S}|$ higher normalized axis actions with that reduction and determinant. Each is induced by at least one algebra automorphism. If $\delta\in\Gamma_S^{g_S}$, exactly
$$
\frac{|\Gamma_T|^{k_S-1}|K^{g_S}|}{|\Gamma_S^{g_S}|}
$$
lower normalized axis actions lift with determinant $\delta$. Here the object being lifted is the tuple of normalized axis coordinates. Choosing an entire lower algebra automorphism also specifies maps on its other Peirce spaces.

## Collisions of projective labels after base change

The established Ceva construction uses $s=|U|$, one distinguished width-$s$ matrix payload carrying the first tensor on each edge, and $|\Gamma|-1$ width-$s$ payloads carrying the second tensor. The corresponding product lines on the edge $e=(v,w)$ have coordinates $R(ae_v+e_w)$ for $a\in\Gamma$, with distinguished label $1$. A width-$m_v$ marker pins $Re_v$ and has $m_v+1\equiv b_v\bmod s$. All these payload occurrences and markers remain after base change, even if several lines coincide.

The automorphism recovery argument for the Ceva algebra applies over $S$. The idempotents align by a triangular conjugation of determinant 1. Residual matrix widths again fix the source, sink, and individual vertex markers. The induced Peirce support on width-$s$ vertices again recovers each three-vertex data block, using positivity of the tensor format. Matrix amplification reflects isomorphism by alignment of full matrix units and cancellation of their finitely generated modules. The resulting algebra isomorphism of the three-vertex payloads recovers the original tensor isomorphism. The marker lines force a diagonal axis action. In particular this recovery uses the supports of the lines before reading their labels.

In $A_S$ two labels $a,a'\in\Gamma$ give the same side line exactly when their images in $\Gamma_S$ agree. This follows by comparing the coordinate with coefficient 1 in the normalized representative. A diagonal action of scales $y_v$ preserves each edge support, so the image of its label $1$ has label $y_v/y_w\in\Gamma_S$. If the tensor pair on this edge is nonisomorphic over $S$, the unique distinguished payload among these occurrences must stay in place, even when its line coincides with those of some other payloads. That forces $y_v=y_w$.

Conversely, take $y_v/y_w\in\Gamma_S$ on each edge and $y_v=y_w$ on nonisomorphic edges. For any isomorphic edge choose a lift $r\in\Gamma$ of its ratio and rotate the original list of labels by $a\mapsto ra$. All its payload algebras are isomorphic over $S$, so the permutation is implemented using augmentation-preserving identifications. On a nonisomorphic edge keep every occurrence fixed. On incoming rows use the common multiplier $y_w$ for the edge pairing and use $y_v$ for the vertex-marker pairing. These maps and the given diagonal map on the source-to-sink space respect all products, including cases of repeated lines. Connectedness and normalization turn these permissible assignments into exactly $X_S$.

The determinant computation also persists. The integer $s$ is divisible by $|S^\times|$ because the quotient map on units is onto. Thus the determinant of an amplified payload automorphism, an $s$-th power, is 1 over $S$. For a permutation cycle of payloads, the product of the individual transport determinants is the determinant of an amplified automorphism. A permutation of the equal-sized payloads or their arrow modules contributes positive sign when $s$ is even, and $-1=1$ already in $R$ when $s$ is odd. Data arrow determinants cancel because their incoming and outgoing pairings have rank $s$. At vertex $v$ the arrow determinants multiply to $y_v^{m_v}$, and the axis itself contributes $y_v$. The full determinant is $\prod_v y_v^{b_v}=\eta_S(x)$.

For the component containing $v_0$, its weight is the negative sum of the other component weights. Consequently the component powers give precisely $\Gamma_S^{g_S}$ by Bézout's identity. The sink and source still provide all left and right multiplication determinants, respectively. Normalizing a multiplication isotopy at the unit identifies its determinant ratio with the determinant of its algebra isomorphism. The image of the stabilizer determinant triples is therefore the inverse image of $\Gamma_S^{g_S}$ under $(u,v,w)\mapsto uv/w$. The special-linear orbit count is the claimed index. [Ceva graph construction and determinant calculation](https://github.com/Dugongue/MathProofs/blob/main/PolyhedralTensorDeterminants/A.md)

## Exact fibers for a higher determinant

An isomorphism over $S$ reduces to one over $T$, so $\mathcal P_S$ is coarser than $\mathcal P_T$. The image of $X_S\to X_T$ is precisely the set of tuples constant on the higher components because $\Gamma_S\to\Gamma_T$ is surjective. Its kernel is $K^{k_S-1}$, the direct power indexed by the components away from $v_0$.

The character restricted to that kernel has image equal to the product of the subgroups $K^{b_C}$ for those components. Since $\exp K\mid\exp\Gamma_S$, this product is $K^{g_S}$. Every lift of a given tuple is obtained from a chosen lift by this kernel. Thus the attainable higher determinants constitute the single coset $\eta_S(\widetilde x)K^{g_S}$, and every value in the coset has a fiber of size $|K|^{k_S-1}/|K^{g_S}|$. This proves the two conditions and their count. The full upper determinant fiber has size $|\Gamma_S|^{k_S-1}/|\Gamma_S^{g_S}|$. Dividing by its common fiber size over the lower group gives the asserted number of lower actions.

For example let $p$ be odd, $S=\mathbb Z/p^3$, $T=\mathbb Z/p^2$ and take the principal unit subgroup. Use one eligible edge with weights $(p,-p)$, root at the second vertex. At the lower level all $p$ normalized actions have determinant 1. At the higher level the subgroup $\Gamma_S^p$ also has order $p$, while $K^p=\{1\}$. The map $x\mapsto x^p$ identifies the $p$ lower coordinates with the $p$ possible higher determinants. Thus for each prescribed higher determinant exactly one of the $p$ lower normalized actions is realizable at that determinant.

## Every permissible precision profile occurs

Fix an odd prime $p$, $N\ge2$, and put $R_j=\mathbb Z/p^j$ for $1\le j\le N$. Build the algebra over $R_N$ using the principal unit subgroup. The image $\Gamma_j$ is cyclic of order $p^{j-1}$, generated by $1+p$. Indeed taking a $p$-th power of $1+c p^a$ with $p\nmid c$ raises the valuation of its difference from 1 by exactly one, by the binomial formula for odd $p$.

At level $j$ define the effective exponent $r_j$ by $D_j=\Gamma_j^{p^{r_j}}$, with $0\le r_j\le j-1$. Then $r_j$ is nondecreasing. As $j$ increases, components merge, replacing component weights by sums and hence increasing the minimum of their $p$-valuations, with zero given valuation $+\infty$. The effective exponent is that minimum capped at $j-1$.

Conversely, every nondecreasing sequence $(r_j)_{j=1}^N$ with $0\le r_j\le j-1$ is realized by a single Ceva algebra. For each maximal constant interval of the sequence with value $h$ and last index $a$, introduce two vertices with weights $+p^h,-p^h$. Connect them by an edge with scalar payloads $p^a xy,0$. For $a=N$ these payloads agree over the starting ring. At precision $j$ these payloads are isomorphic exactly when $j\le a$, since multiplication by units cannot take a nonzero scalar to zero. Join one vertex of every pair to a common zero-weight root by a permanently isomorphic edge, using a pair of equal scalar tensors. The underlying graph is a tree. Pairs whose interval ended before $j$ have merged to weight zero and the other pairs keep their singleton weights. The minimum remaining valuation is exactly $r_j$. Hence the orbit count at every precision equals $(p-1)p^{r_j}$. This uses at most $2N+1$ vertices and only scalar tensors.

## Prescribed axis lifting already encodes ordinary tensor isomorphism

Fix odd $p$ and $N\ge3$. Given an instance $(T,T')$ of ordinary tensor isomorphism over $\mathbb F_p$, lift its coefficients to $\mathbb Z/p^N$ and multiply both lifts by $p^{N-1}$. The resulting tensors are isomorphic over $\mathbb Z/p^N$ exactly when $T,T'$ are isomorphic over $\mathbb F_p$. Any transporter reduces to a transporter over the field by the equality $p^{N-1}a=p^{N-1}b$ exactly when $a\equiv b\bmod p$. Conversely each invertible field matrix lifts to an invertible matrix over $\mathbb Z/p^N$, and the lifted maps preserve the multiplied tensors by the same equality.

Place the resulting pair on a single edge with weights $(1,-1)$, root at the second vertex, and principal $\Gamma$. The lower quotient $\mathbb Z/p^{N-1}$ sees zero tensors, and the explicit nonidentity coordinate $x=1+p$ is always an admissible lower normalized axis action. Prescribe the higher determinant $\delta=1+p$. The higher normalized tuple with that ratio exists exactly when the edge is isomorphic at the higher precision. Thus over this fixed pair of rings, the prescribed axis-lift question with high determinant fixed to $1+p$ is at least as hard as ordinary tensor isomorphism over $\mathbb F_p$. The supplied ordinary change of basis with determinant $(1+p)^{-1}$ converts the upper determinant requirement into a supplied determinant-one correction. The transformation is polynomial for the fixed rings, and its lower projective action is specified regardless of the answer. [Tensor isomorphism over rings](https://arxiv.org/abs/2611.00735)


## Side palettes and a genuinely global lifting obstruction

Allow the payload at label $a\in\Gamma$ on each edge $e$ to be any tensor $T_{e,a}$, with one positive format per edge. Over $S$, use $H_{e,S}$ for the group of translations of $\Gamma_S$ preserving, at every reduced label $b$, the multiset of tensor isomorphism classes carried by the occurrences above $b$. The single-exceptional-label case above is recovered with $H_{e,S}=\{1\}$ or $\Gamma_S$. For a general palette the matrix and marker arguments above give precisely
$$
X_S=\{x\in\Gamma_S^V:x_{v_0}=1,\ x_v/x_w\in H_{e,S}\text{ for every }e=(v,w)\},
\qquad \eta_S(x)=\prod_vx_v^{b_v}.
$$
Indeed for an admissible multiplier the multiset equality permits a bijection between the matching isomorphism classes in each label fiber. These bijections give augmentation-preserving payload transports, and scaling the row on each occurrence realizes the prescribed paired product. The determinant computation is independent of the bijections. Reducing such edge bijections also shows that the reduction of $H_{e,S}$ lies in $H_{e,T}$.

There is a cycle test even once **every individual side ratio admits a lift**. Fix orientations and a spanning tree $\mathcal T$. For lower $x\in X_T$, choose $a_e\in H_{e,S}$ lifting $x_v/x_w$ on each oriented edge $e=(v,w)$, if possible. Write $\beta=|E|-|V|+1$ and use the $\beta$ oriented fundamental cycles of the tree. For an edge tuple $c$, let $\partial(c)$ be its products on those cycles, using reciprocal entries when traversing an edge backwards. On the tree solve $x^c_v/x^c_w=c_e$ with $x^c_{v_0}=1$, and put $\theta(c)=\prod_v(x^c_v)^{b_v}$. Both maps are homomorphisms, by commutativity of the unit group.

Let
$$
F=\prod_e(K\cap H_{e,S}),\qquad
\Phi:F\longrightarrow K^\beta\times K,\qquad
k\longmapsto(\partial(k),\theta(k)).
$$
A higher normalized action reducing to $x$ and of determinant $\delta$ exists exactly when
$$
\bigl(\partial(a)^{-1},\,\delta/\theta(a)\bigr)\in\operatorname{im}\Phi.
$$
If the second coordinate is outside $K$ the condition fails. The number of lifts is then $|\ker\Phi|$. To prove this, all possible high edge ratios are uniquely $a_e k_e$. They come from normalized vertex coordinates exactly when their fundamental cycle products are 1. The tree determines the vertex coordinates uniquely, and the condition on each fundamental cycle says its non-tree edge agrees with them. The character is precisely $\theta(ak)$ on such a tuple. This identifies the lifts with one fiber of $\Phi$, proving the formula. Different initial lifts translate the displayed target by an element of $\operatorname{im}\Phi$. The cycle products are the usual balance test for abelian gain graphs. Their joint fiber with the determinant character gives the exact count for this multiplication-algebra construction. [Zaslavsky on balance and gains](https://people.math.binghamton.edu/zaslav/Tpapers/bg1.jctb1989.pdf)

The obstruction occurs with scalar tensors. Take $S=\mathbb F_2[x,y]/(x,y)^2$, $T=S/(y)$, and $\Gamma=S^\times$. In a cyclically oriented triangle use high subgroups
$$
H_1=\langle 1+x\rangle,\qquad H_2=\langle 1+x+y\rangle,\qquad H_3=\{1\}.
$$
To realize $H_i$, put the scalar tensor $uv$ at labels in $H_i$ and the zero scalar tensor at all other labels. The translation group at high precision is exactly $H_i$, since it must preserve that subset. In a quotient every label inside the image of $H_i$ carries exactly $|H_i\cap K|$ copies of the marked class, and every other label carries zero. The reduced group is therefore precisely the projection of $H_i$. The lower ratios $(1+x,1+x,1)$ come from a lower normalized axis action, and each ratio has a unique lift in its specified high subgroup. Their product is $1+y$, so no higher normalized action exists.

Moreover any binary vector on the fundamental cycles of a connected bipartite graph occurs as this obstruction over the same two rings. In the reduced ring, use coordinate 1 on one part and $1+x$ on the other, choosing the root in the first part. Every edge ratio is $1+x$. In the high ring use the order-two subgroup generated by $1+x$ on all tree edges. For each non-tree edge choose the subgroup generated by $1+x$ or $1+x+y$ according to its prescribed cycle bit. As above, scalar palettes realize precisely these subgroups and each edge ratio has a unique lift. Every fundamental cycle has even length, so the product of the $1+x$ terms is 1 and its $y$ bit is exactly the bit of its one non-tree edge. Subdividing each edge of an arbitrary connected simple graph once supplies a bipartite graph with the same cycle rank.

## Scope and verification

Earlier work established arbitrary compatible determinant subgroup profiles for a single selector over a quotient chain, including exact reduced-label multiset arithmetic. The graph result here computes prescribed normalized lifts and their fibers, gives a scalar-tree realization of its restricted family of profiles, and exhibits cycle obstructions even when all reduced edge ratios lift separately. The full algebra and quotient results have written proofs. Lean independently checks the general joint-fiber equivalence and prescribed-character criterion. The finite control compares fiber formulas with enumeration and checks reduced-label collisions and the scalar precision profiles. [Earlier quotient-profile theorem](https://github.com/Dugongue/MathProofs/blob/main/PrincipalUnitDeterminants/A.md) · [Lean components](C.lean) · [Finite controls](CCheck.py)
