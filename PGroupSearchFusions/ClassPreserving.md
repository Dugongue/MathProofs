# Class-preserving search and exact counting for finite p-groups

This informal proof strengthens the [same-prime search and counting reduction](https://github.com/Dugongue/MathProofs/blob/main/GroupIsomorphismAndEpimorphisms/AllPGroupsSearchCounting.md). The old construction recognized a marker through the order of one new element. Here a gap in the rank of the graded commutator recognizes it. This allows the query groups to stay in the original nilpotency class, lower exponent-\(p\) class, and exponent simultaneously.

## Theorem

Given Cayley tables of finite \(p\)-groups, finding an isomorphism, counting isomorphisms exactly, and generating the automorphism group have deterministic polynomial-time reductions to ordinary \(p\)-group isomorphism at the same prime. For a nonabelian input group \(G\), every augmented group made from \(G\) has the same nilpotency class, the same lower exponent-\(p\) class, and the same exponent as \(G\). Its order is at most \(|G|^{18}\). More precisely, the two series are unchanged from their third terms onward under the embedded copy of \(G\). All these assertions hold uniformly in the prime, including \(p=2\).

The reductions may therefore use any fixed simultaneous upper bounds on the two classes and exponent as an oracle promise. Finite nilpotent groups admit the corresponding Sylow-by-Sylow reductions. In particular, the new class-two decision bound in [Faster Isomorphism for Groups of Class 2](https://arxiv.org/abs/2611.05920v1) also yields deterministic search, exact counting, and automorphism generation in time \(N^{O((\log N)^{25/26}\log\log N)}\) for **all finite groups of class at most two**, in the same explicit table model. The reduction incurs a fixed power of \(N\) in the query orders and in the number of queries, so the exponent scale is unchanged. Abelian groups require no oracle calls.

## 1. The marked bilinear space

Let \(|G|=p^b>1\), let \(V=G/\Phi(G)\) have dimension \(d\), and let \(P_3(G)=\Phi(G)^p[\Phi(G),G]\). Write \(w=\dim_{\mathbb F_p}(\Phi(G)/P_3(G))\), so \(w\le b-d\). We give a decision query for transport of any prescribed ordered family of \(k\le d\) independent covector lines. On a pair of groups of unequal orders, different primes, or different values of \(w\), the original comparison is already negative. We therefore assume these numerical parameters agree when comparing marked inputs. There is nothing to add for \(k=0\).

Use the rigid bipartite graph of the [same-prime marker proof](https://github.com/Dugongue/MathProofs/blob/main/GroupIsomorphismAndEpimorphisms/SamePrimePGroupMarkers.md#a-linear-size-ordered-marker). Each left vertex is fixed by every part-preserving automorphism, and its right neighborhood is incomparable with every other left neighborhood. One construction for \(k\ge7\) uses a tree with three distinct branch lengths \(1,2,k-4\), a right vertex per tree edge, and a private right vertex per left vertex. For \(k\le6\), use disjoint stars with distinct degrees \(1,\dots,k\). The right space \(A_0\) and edge space \(D\) have dimensions at most \(4k\). With fixed coordinate covectors \(z_j\) of \(A_0\), define

\[
M(v,a)=\sum_{(i,j)\text{ an edge}}\ell_i(v) z_j(a)e_{ij}\in D .
\]

Its values span \(D\), since the \(\ell_i\) are independent and each edge coefficient can be isolated using a right basis vector. A change of coordinates preserving this pairing with an arbitrary invertible output map carries the ordered covector lines to their counterparts. Indeed the dual image in \(V^*\otimes A_0^*\) is the edge support space. Any equivalence of edge support spaces identifies the two contraction supports. Permutations selecting nonzero determinant terms in its two restricted mode maps carry edges to edges. They give a graph automorphism, so the left permutation is the identity. If one column of the left map has a nonzero entry in a different row, the edge condition forces containment of the corresponding distinct neighborhoods. This is excluded. Conversely a map respecting the lines extends by scaling the corresponding edge coordinates. The argument still applies if the right space has extra directions on which \(M\) is zero, since its contraction support on the right is intrinsic.

## 2. Replacing an element-order marker by a rank gap

Put \(z=\dim D\) and \(L=\max(\dim A_0,w+z+2)\). Enlarge \(A_0\) by trivial directions to a vector space \(A\) of dimension \(L\), extend \(M\) by zero on those directions, and take a copy \(C\) of \(A\) with identification \(\iota:A\to C\). Use the elementary cyclic group \(B=\mathbb F_p^+\). Form

\[
K_G=(A\oplus D\oplus C)\rtimes(G\times B)
\]

with product

\[
(a,u,c,g,t)(a',u',c',g',t')
= (a+a',u+u'+M(\bar g,a'),c+c'+t\iota(a'),gg',t+t').
\]

The actions commute because their corrections have values in the fixed direct summands \(D,C\). Thus the formula defines a group, and it is valid in characteristic two. Their commutators generate the full \(D,C\) by the spanning property of \(M\) and by the identification \(\iota\). Directly,

\[
\begin{aligned}
[K_G,K_G]&=[G,G]\times D\times C,\\
\Phi(K_G)&=\Phi(G)\times D\times C,\\
P_3(K_G)&=P_3(G).
\end{aligned}
\]

For the middle identity use the \(p\)-th powers in the abelianization. For the last identity, \(\Phi(G)\) acts trivially on \(A\), and \(D,C\) are central of exponent \(p\). In particular, \(K_G/\Phi(K_G)=V\oplus A\oplus B\), and its graded commutator takes values in \((\Phi(G)/P_3(G))\oplus D\oplus C\). It is an alternating bilinear map because \(\Phi(K_G)\) becomes central of exponent \(p\) after quotienting by \(P_3(K_G)\).

For a vector \(x\) in this first graded layer, measure the rank of the linear map \(y\mapsto[x,y]\) into the second layer. If \(x\) has zero \(B\)-coordinate, its commutator image has dimension at most \(w+z+1\). The original part lies in dimension \(w\), the marker part lies in \(D\), and the \(C\)-part is a multiple of the single vector \(\iota(a_x)\) through the \(B\)-coordinate of \(y\). If \(x\) has nonzero \(B\)-coordinate, its commutator with the copy of \(A\) surjects onto \(C\) after projecting to that summand, giving rank at least \(L\). The two rank ranges are disjoint. Therefore the subgroup

\[
T=(A\oplus D\oplus C)\rtimes G
\]

is recovered as the preimage of the rank-\(<L\) set. In both constructed groups the threshold is the same, since the specified graph and \(w\) agree. Any isomorphism must transport this subgroup.

The second subgroup needed by the old argument is recovered by

\[
U=\{x\in T:[x,K_G]\subseteq[T,T]\}=G\times D\times C.
\]

Indeed \([T,T]=[G,G]\times D\), and the extra \(C\)-commutator between \(x\in T\) and the generator of \(B\) is its \(A\)-coordinate carried by \(\iota\), up to sign. Thus \(T/U=A\), \(U/\Phi(K_G)=V\), \([U,U]=[G,G]\), and \([U,T]/[U,U]=D\). On these intrinsic factors the commutator pairing is exactly \(M\). An isomorphism between the augmented groups therefore respects the line constraints. Its restriction to the embedded input \(G\), followed by projection from the target \(U\) to the target input \(H\), induces the same invertible Frattini quotient map. Its image is all of \(H\) since it generates the Frattini quotient. Equal input orders make it an isomorphism. Conversely a line-respecting isomorphism of the input groups extends to the augmented groups by the edge-coordinate scaling, the identity on \(A,C,B\), and the displayed product rule.

## 3. Preserving both series and the exponent

For the ordinary lower central series, the derived subgroup formula yields \(\gamma_3(K_G)=\gamma_3(G)\), since \(D,C\) are central and \([G,G]\subseteq\Phi(G)\) acts trivially on the new additive modes. Induction gives identity of the subsequent terms. For the lower exponent-\(p\) central series the same conclusion starts at \(P_3\) by the identities above and continues because every such subgroup acts trivially on the auxiliary modes. In nonabelian groups both original series have a nontrivial second term. So whether the third term is trivial or nontrivial, the class of each series is preserved exactly.

For a positive integer \(j\), the \(j\)-th power of a coordinate tuple has its \(A,B\) coordinates multiplied by \(j\), its group coordinate equal to \(g^j\), and its two fixed module coordinates equal to

\[
ju+\binom j2 M(\bar g,a),\qquad jc+\binom j2t\iota(a).
\]

This follows by induction from the product. For odd \(p\), \(\binom{p^e}{2}\) is divisible by \(p\) for \(e\ge1\). For \(p=2\) it is even when \(e\ge2\), and every nonabelian 2-group has exponent at least four. Taking \(p^e=\exp(G)\) therefore kills every element of \(K_G\). The embedded input gives the reverse divisibility, so the exponent is preserved.

Finally \(L\le4b+2\) and \(z\le4b\), since \(k\le d\le b\) and \(w\le b-d\). Thus \(\log_p|K_G|=b+2L+z+1\le13b+5\le18b\). Constructing the multiplication tables uses polynomial time in the raw input, uniformly in the prime. The construction depends only on field arithmetic, subgroups available by elementary table generation, and the elementary coordinate formula.

## 4. Search, exact counting, and the scope of the improvement

In the [all-\(p\)-group search theorem](https://github.com/Dugongue/MathProofs/blob/main/GroupIsomorphismAndEpimorphisms/AllPGroupsSearchCounting.md#4-search-counting-and-automorphism-generators), the only augmented decision queries ask whether an isomorphism respecting a specified partial independent dual frame exists. Replace them by the construction above. The exact lift after specifying a full Frattini quotient map still uses the central-extension and subspace transporter algorithm, without further oracle queries. The stabilizer chain produces counts and generators with precisely the same query constraints. Since its subgroup orders are computed on the actual Frattini automorphism image and kernel, there is no need to count automorphisms of the new marker groups themselves. Finite nilpotent groups split into characteristic Sylow factors. Their independent witnesses and generators assemble, and their exact counts multiply.

For completeness, the abelian prime-power factors can be handled directly. Use the additive presentation on the table elements with relations \(x_g+x_h=x_{gh}\). Its Smith normal form yields invariant-factor coordinates and an explicit cyclic basis, by the integer transformation matrices. Matching invariant factors gives an actual isomorphism. If the cyclic orders are \(p^{a_i}\) in nondecreasing order, the image of the automorphism group in the Frattini quotient is the block upper-triangular parabolic with blocks of equal exponent. In fact, a coefficient from exponent \(a_i\) into a larger exponent \(a_j\) must be divisible by \(p\). Every invertible matrix obeying those zeros lifts to a homomorphism by choosing its allowed coefficients in the cyclic basis. The map is surjective by the Frattini property and hence invertible. Generators of this parabolic are the allowed elementary transvections and the nonzero diagonal scales, obtained by block Gaussian elimination. Its order is the product of the block general linear orders times \(p\) raised to the number of strictly upper off-diagonal entries between different blocks. Lift these generators, and adjoin and count the oracle-free Frattini kernel from the linked lifting theorem. This gives all three tasks in polynomial time for abelian factors, including exponent two.

The old class-two exponent-\(p\) and Frattini-class-two reductions already treat those respective subfamilies. The rank-gap device preserves both classes simultaneously even when one of the two classes is arbitrarily large and the other is small. In particular it applies to class-two groups of arbitrarily large exponent, which need not have Frattini class two. The result is in the Cayley-table model and addresses a restricted family of the general search and counting question. [Grochow–Qiao, class-two exponent-\(p\) reduction](https://arxiv.org/abs/2306.16317) · [Arvind–Torán, Problem 16](https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/beatcs/column86.pdf)

## 5. Parallel queries and marked Sylow factors

The [parallel lifting theorem](ParallelLifting.md) only uses the marked comparison through its table compiler. Sections 1 and 2 give a logspace-uniform NC compiler as well. The Frattini and third-layer subgroups are computed by subgroup reachability with generators listed by powers and commutators, and their orders give \(d,w\). The output entry rule then uses parallel table lookups and field-coordinate operations across all entries. Thus the same parallel reduction has one nonadaptive counting batch with order bound \(N^{18}\) and queries preserving the stated group parameters.

The marker for [normal Sylow towers](SylowTowers.md) replaces the rank-one input covectors by ordered direct-sum simple submodules. The rank-gap calculation depends only on the dimension of the edge output and its spanning property, so it applies to that pairing as well. All new padding directions, the copy \(C\), and the cyclic coordinate \(B\) carry the trivial complement action. The old edge output carries the induced complement action. Consequently the product formula is equivariant for the complement and the retraction to the original Sylow subgroup remains equivariant. The same reflection and extension arguments then apply at each step of the tower. Here \(\dim D\le6d\), \(\dim A_0\le4d\), and \(L\le6b+2\), so the per-factor order bound is \(p^{19b+5}\le |G|^{24}\). The combined query keeps the tower and preserves all three numerical parameters on every nonabelian Sylow factor. An abelian Sylow factor may rise to class two, with exponent at most the maximum of its original exponent and four at the prime two. This gives a joint same-class refinement of the tower reduction on towers whose marked Sylow factors are nonabelian.

Exact counting on those towers also uses one nonadaptive batch of polynomially many decision queries. First fix one nested choice of complements and one full ordered list of module marks in the given group. Use one query per potential image of the next mark under the subgroup fixing its predecessors. All these self-comparison queries have known prefixes, so they are simultaneous. The product of the number of successful images at each step times the order of the fully marked stabilizer gives the order of the subgroup preserving the chosen tower of complements. The marked-order calculation uses the polynomial-time lift on the given group against itself and needs no decision queries. To recover the full automorphism order, multiply by the number of nested complement choices. At each step \(P\rtimes C\) the complements are conjugate by \(P\), and an element of \(P\) normalizes \(C\) exactly when it centralizes \(C\), since it induces the identity on the quotient and the projection on \(C\) is injective. Thus that step contributes \(|P|/|C_P(C)|\). Each complement is isomorphic to the chosen one, so multiplication over successive steps counts the full set of choices. The inner-alignment proof makes this whole set one automorphism orbit. The count for two groups is zero on a negative decision query and is this order on a positive decision query. The same argument works with a fixed bounded-generator terminal quotient, using its marked-order procedure from the tower proof.

## 6. Parallel canonization with bounded flag width

Combine the [Frattini-flag canonization theorem](FrattiniFlagCanonization.md), Sections 1–3, with the cohomology dimension and uniform NC linear algebra in [Parallel lifting](ParallelLifting.md). In the canonization recursion each vector normalization along a fixed flag chooses the least attainable coordinate from at most \(p\) candidates. It can be carried out in the same parallel stage that tests vector transport and computes its stabilizer. The fixed-line quotient recursion then canonizes subspaces in polylogarithmically many NC stages, since its cohomology dimension is \(O(\log^2 N)\). The canonical cocycle representative is found by deterministic elimination with fixed-order pivots, also in uniform NC. Every central layer constructs its entire output table and explicit witness, and the number of layers is at most logarithmic. These are all the additional operations required to make the framed canonical-table construction uniform NC.

For the unframing step, it suffices to enumerate all candidate ordered bases on each original graded block, allowing repetitions of the same refinement. If the width is at most a fixed \(B\), the total space of candidate basis matrices is bounded by \(p^{\sum_i b_i^2}\le p^{Bd}\le N^B\). Run the framed computations in parallel on the nonsingular choices and select the least resulting table, including matching flag and witness. The coordinates of the intrinsic flag given by the images of the subgroups generated by elements killed by each power of \(p\) use parallel table powers and elimination. This yields uniform NC canonical tables and witnesses also on the corresponding raw bounded-width groups. The same enumeration bound applies to the unmarked small-rank regime \(d^2\le C\log_p N\) for fixed \(C\).
