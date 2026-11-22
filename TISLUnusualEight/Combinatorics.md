# Determinant-one transport of graph incidence tensors

Let $G=(L,R,E)$ be a finite simple bipartite graph with two named parts, at least one edge, and ordered bases of the parts and edge space. Assign a nonzero weight $w_e\in k^\times$ to each edge, over an arbitrary field $k$. Its tensor is
$$
 T_{G,w}=\sum_{(i,j)\in E}w_{ij}\,e_i\otimes f_j\otimes g_{ij}.
$$
The edge-coordinate presentations are part of the input. All three maps of a tensor transporter may be arbitrary invertible matrices. Put $\omega_G=\prod_{e\in E}w_e$, and let $g(G)$ be the gcd of the degree differences **within** the two parts, with gcd zero when both parts have constant degree. Write $(k^\times)^0=\{1\}$.

**Theorem.**

1. If $g(G)=1$, ordinary tensor isomorphism and determinant-one tensor isomorphism coincide on these weighted tensors. A supplied ordinary transporter can be corrected constructively over the same field. Both problems are GI-complete on the $g=1$ family of unweighted vertex–edge incidence tensors of simple graphs.
2. There is a deterministic polynomial-size many-one reduction from determinant-one tensor isomorphism to ordinary tensor isomorphism over the same field in each of these cases.
   - The two graphs have odd $g$, or $k$ has characteristic two.
   - The two graphs are vertex–edge incidence graphs of bipartite graphs all of whose vertex degrees are even. This includes $g=0$ and weighted inputs, with arbitrary ordering of the incidence coordinates.

   The reduction converts witnesses in both directions without a root-finding oracle. It is polynomial in the explicit representations over finite fields and over $\mathbb Q$, and uses polynomially many field operations over an arbitrary field.

The proof also gives all attainable third determinants after normalizing the first two to one, and exact finite-field transporter factors. It applies to isolated vertices and identical neighborhoods.

## 1. From arbitrary linear transporters to neighborhood inclusion

Let $\mathcal S_G=\operatorname{span}\{e_i\otimes f_j:(i,j)\in E\}$ and let $F_G$ be the injective map from the dual of the edge-mode space to $\mathcal S_G$ with columns $w_{ij}e_i\otimes f_j$. For a transporter $(P,Q,C)$ from $T_{G,w}$ to $T_{H,w'}$,
$$
 (P\otimes Q) F_G C^{\mathsf T}=F_H .
 \tag{1}
$$
Thus $(P\otimes Q)\mathcal S_G=\mathcal S_H$. Conversely this equality uniquely determines an invertible $C$ by (1).

Choose permutations $\sigma,\tau$ from nonzero determinant terms of $P,Q$, so $P_{\sigma(i),i}$ and $Q_{\tau(j),j}$ are nonzero for all $i,j$. They can be found by perfect matching in the nonzero patterns. For every edge $(i,j)$ of $G$, the coefficient of $(\sigma(i),\tau(j))$ in $Pe_i\otimes Qf_j$ is nonzero, so it must be supported on $H$. Equal edge counts imply that $\sigma,\tau$ give a part-preserving graph isomorphism. This is the rectangular version of the graphical-space support argument of Li, Qiao, A. Wigderson, Y. Wigderson and Zhang, Proposition 6.2. In particular ordinary TI here is exactly part-preserving graph isomorphism. [Connections between graphs and matrix spaces, Proposition 6.2](https://arxiv.org/html/2206.04815#S6.SS1)

Remove the selected permutations, writing $P=P_\sigma P_0$, $Q=P_\tau Q_0$. Both residual matrices have nonzero diagonals. If entry $(i',i)$ of $P_0$ is nonzero, then for every neighbor $j$ of $i$ the coefficient of $(i',j)$ in $P_0e_i\otimes Q_0f_j$ is nonzero. Hence $N(i)\subseteq N(i')$. On the right similarly $Q_{0,j',j}\ne0$ requires $N(j)\subseteq N(j')$. Conversely these two conditions on invertible matrices suffice to preserve the edge space. For an original edge, moving its first endpoint to a larger neighborhood preserves the edge, and then so does moving the second endpoint to a larger neighborhood. Inclusion of the spaces is equality by dimension.

Group vertices in each part into classes with identical neighborhoods. These classes are ordered by strict neighborhood inclusion. In any linear extension, the corresponding matrices are triangular by classes, with arbitrary invertible diagonal blocks and free entries in off-diagonal blocks allowed by strict inclusion. Write $a_X$ for the determinant on a left class $X$ and $b_Y$ for the determinant on a right class $Y$. The determinant of their action on $\mathcal S_G$ is
$$
 \prod_X a_X^{\deg X}\prod_Y b_Y^{\deg Y}.
 \tag{2}
$$
Indeed an adjacent pair of classes contributes a complete rectangular block to the edge space. The block action on that rectangle is the tensor product of the two diagonal blocks. Its determinant is $a_X^{|Y|} b_Y^{|X|}$, and the action on all rectangles is triangular in product order. Multiplying the block determinants gives (2). Isolated vertices cause no exception, since their degrees are zero.

Let $\pi_E$ be the induced bijection on ordered edge bases. Fix one degree $d_L$ in the left part and one degree $d_R$ in the right part. Equation (1) and (2), with $\det P=\det Q=1$, give exactly the following set of third determinants for the chosen graph isomorphism:
$$
 \frac{\omega_H}{\omega_G}\,
 \underbrace{\operatorname{sgn}(\pi_E)\operatorname{sgn}(\sigma)^{d_L}
                       \operatorname{sgn}(\tau)^{d_R}}_{\epsilon(\sigma,\tau)}
 \,(k^\times)^{g(G)} .
 \tag{3}
$$
In detail, first fix $\prod_X a_X=\operatorname{sgn}(\sigma)$ and $\prod_Y b_Y=\operatorname{sgn}(\tau)$. Eliminating the two reference determinants leaves the exponents $\deg X-d_L,\deg Y-d_R$ multiplying independent class determinants. Their image is $(k^\times)^g$, by integer Bézout and the common divisibility of the exponents. Every class determinant can be prescribed using a diagonal block. The weighted columns in (1) contribute exactly $\omega_H/\omega_G$. Signs are interpreted in $k$, where they are trivial in characteristic two.

Thus for any graph isomorphism write $\chi=(\omega_H/\omega_G)\epsilon(\sigma,\tau)$. It admits a determinant-one lift precisely when $\chi\in(k^\times)^g$, including equality to one for $g=0$. Given a root $r^g=\chi$ for $g>0$, set the free class determinants to $r^{c_X},r^{c_Y}$ for Bézout coefficients for the degree differences, then set the two reference determinants to give determinant one in modes one and two. The resulting third determinant is one. Conversely, an actual determinant-one lift gives the root
$$
 r=\prod_X a_X^{(\deg X-d_L)/g}\prod_Y b_Y^{(\deg Y-d_R)/g}.
 \tag{4}
$$
These calculations do not enumerate the field. The Bézout coefficients can even be taken of polynomial magnitude. Use a nonzero degree difference $b$ as modulus, find a shortest path from $0$ to the residue of $g$ in the additive graph modulo $|b|$ generated by the other signed differences, and correct the resulting integer sum using $b$. This gives polynomial exponents, including for bit complexity over $\mathbb Q$. For $g=1$ one simply uses $\chi$ itself as the root.

## 2. Two ways to remove the unknown graph-isomorphism sign

If $g$ is odd, both signs are $g$-th powers, with the sign itself as its root. The same conclusion holds in characteristic two for all $g>0$. Therefore the test is graph isomorphism and the single arithmetic test $\omega_H/\omega_G\in(k^\times)^g$. In characteristic two and $g=0$ it is graph isomorphism and equality of the weight products. If a transporter or root is given, multiply the root by the corresponding sign when converting between (3) and the arithmetic test.

A different mechanism works for weighted vertex–edge incidence tensors of bipartite graphs of even degrees. Let the base graph be $B$, so $G$ has all vertices of $B$ in its left part and all edges of $B$ in its right part. The edges of $G$ are the incidence pairs of $B$. Choose a bipartition of each connected component of $B$ by two-coloring. Regroup the ordered incidence pairs into consecutive pairs indexed by edges of $B$, with the first endpoint taken from the first color part. Record the sign $\eta_G$ of this regrouping permutation.

Every isomorphism of such base graphs becomes an even permutation on the regrouped incidence coordinates. Permuting two-element blocks has sign one. Within an edge block, a flip occurs exactly when the component isomorphism exchanges the chosen bipartitions. In every connected component the number of edges is even, since it is the sum of the even degrees over one color part. Thus component flips also contribute total sign one. This includes isolated vertices, which contribute no incidence coordinates. It follows that the original edge-mode sign is $\eta_H\eta_G$ for **every** graph isomorphism. Also both reference degrees in (3) are even, since right incidence degree is two. The desired arithmetic condition is consequently
$$
 \frac{\eta_H\omega_H}{\eta_G\omega_G}\ \in\ (k^\times)^{g(G)} .
 \tag{5}
$$
All quantities on the left are computable from the two inputs before a graph isomorphism is found. The same grouping proves independence from the chosen component bipartitions.

For example, two squares sharing one vertex form a bipartite base graph with degrees two and four, hence $g=2$. With normalized pair order, changing one incidence weight by $t$ over $k=\mathbb F_2(t)$ gives a TI-equivalent tensor and changes its SL answer, since $t$ is not a square. The reduction below retains this inseparable power condition. With the same graph and weight change by $4$ over $\mathbb Q$, the arithmetic condition instead holds.

## 3. A one-query compiler that retains the arithmetic test

For $g=0$, test the explicit equality on the left of (5), or the equality of weight products in characteristic two. In the unequal case return a fixed ordinary-TI NO pair. Otherwise use ordinary TI on the original tensors. The two possible cases have matching formats, and format mismatch is also a fixed NO case.

For $g>0$, let $c$ denote the required ratio, either $\omega_H/\omega_G$ or the ratio in (5). The two commutative finite algebras
$$
 K_c=k[X]/(X^g-c),\qquad K_1=k[X]/(X^g-1)
$$
are isomorphic exactly when $c\in(k^\times)^g$. A root gives the isomorphism by scaling $X$. In the reverse direction, transport evaluation at $X=1$ from $K_1$ to $K_c$. The image of $X$ is the required root. This works with multiple roots and over imperfect fields. The basis of powers of $X$ gives explicit multiplication tables without factoring either polynomial. The same Kummer root test was used in the project's earlier single-nilpotent-block pencil setting. The graph calculations above supply its parameter from weighted incidence data. [Prior special-linear pencil result](https://github.com/Dugongue/MathProofs/tree/main/TISLPencilsAndOrbits)

To combine graph isomorphism and this arithmetic condition in **one** output pair, form a graph algebra $A_G=k1\oplus I$, where $I=U\oplus V\oplus W$ has the two vertex spaces and the edge space. Give $I$ the product $uv=g_{ij}$ for a left $u=e_i$ and right $v=f_j$ on an edge, with all other radical products zero. Unitize by $1$. The algebra is associative since every triple product in $I$ vanishes. It is local since $I$ is nilpotent and the quotient is $k$; the elements outside $I$ are units. The augmentation ideal is intrinsic. Restricting products to it gives a bimap whose two contraction radicals and output image recover the supported graph bimap on $U,V,W$. More explicitly, quotient $I$ by its left contraction radical in the first argument and by its right contraction radical in the second and take $I^2$ as target. Matching ambient dimensions allow the three supported maps to be extended independently over the unused complements. This proves $A_G\cong A_H$ exactly when $G,H$ are part-preservingly isomorphic, by (1). The forward implication and its reflection can be implemented using linear algebra and the determinant-term matchings. [Grochow–Qiao, tensor-to-algebra reductions](https://arxiv.org/html/1907.00309)

Now use the ordinary multiplication tensors of $A_G\times K_1$ and $A_H\times K_c$. The local factor $A_G$ has dimension greater than $g$, since $g$ is at most the larger part size. It is the unique primitive central direct factor of dimension greater than $g$. Every factor in the Kummer algebra has dimension at most $g$. Algebra isomorphism therefore tests both factors separately. This separation is intrinsic even if the Kummer polynomial is inseparable.

A transporter of multiplication tensors of unital associative algebras normalizes to a unital algebra isomorphism. Write its equation as $h(xy)=f(x)g(y)$, in bimap convention, and put $a=f(1),b=g(1)$. They are units since their left and right multiplication maps are bijective. Substitution shows $x\mapsto a^{-1}h(x)b^{-1}$ is a unital algebra isomorphism. This gives a witness on the two direct factors. Recover the graph isomorphism from the first and the root by evaluation at one on the second, and then construct the determinant-one lift by (3). Conversely a determinant-one witness gives the graph isomorphism by matchings, and the root by (4) and the indicated sign correction. These give an algebra isomorphism of the products and hence a tensor transporter. All dimensions and arithmetic costs have the asserted polynomial bounds. [Albert, associative isotopy](https://doi.org/10.2307/1968960)

## 4. GI completeness in the $g=1$ family

Given a simple graph $B$ on $n\ge3$ vertices, add two new universal vertices adjacent to one another and to every old vertex. Append as a disjoint component the diamond $K_4$ with one edge deleted. Call the resulting graph $B^+$. Its large connected component has $n+2\ge5$ vertices and is identified by its size. Removing any two universal vertices there recovers an isomorphic copy of $B$, because any universal vertices of that component may be permuted among themselves. Thus graph isomorphism is preserved and reflected by $B\mapsto B^+$. Smaller $n$ can be handled by fixed outputs.

In the vertex–edge incidence graph of $B^+$, the right degrees are two and the left degrees include both two and three from the diamond. Hence $g=1$. Its two parts are the vertex and edge modes, so a part-preserving isomorphism of the incidence graph induces precisely a base graph isomorphism. This gives GI-hardness for the ordinary and special-linear problems in the stated family. For their reverse reductions, forget the weights and use the colored bipartite graph, as (3) imposes no extra condition. For the reduction to ordinary GI, let $\Delta$ be a common upper bound on the two colored graphs' maximum degrees. Attach $\Delta+2$ or $2(\Delta+2)$ fresh leaves at each vertex according to its color. Original vertices are exactly those of degree greater than one, and the colors occupy disjoint degree intervals.

## 5. Exact finite-field transporter factors

Over $\mathbb F_q$, let $c_L,c_R$ be the numbers of neighborhood classes in the two parts. The number of choices of a residual matrix with every block determinant prescribed, on one part, is
$$
 q^{\sum_{X<Y}|X||Y|}\prod_X |\mathrm{SL}_{|X|}(\mathbb F_q)|.
$$
Here $X<Y$ means strict neighborhood inclusion and the free off-diagonal blocks have the indicated total dimension. Let $K$ be the product of these factors for the two parts. Every tensor transporter determines a unique graph isomorphism on the quotient by neighborhood classes, preserving the two parts, class sizes and adjacency. Indeed any two choices of support permutation for a residual matrix differ within the classes. A supported permutation in the inclusion order can only follow equality of neighborhoods, by following each of its cycles around. Conversely, after fixing one representative graph isomorphism for the quotient, the residual descriptions count all transporters inducing that quotient map exactly once.

For each feasible quotient map, the ordinary count is $K(q-1)^{c_L+c_R}$. The SL count is zero when (3) omits one. Otherwise it is
$$
 K\,\frac{(q-1)^{c_L+c_R-2}}{|(\mathbb F_q^\times)^g|}.
$$
The two first determinants remove one free scalar in each part. The third determinant quotient is a surjective homomorphism onto the displayed power subgroup, so all its fibers have equal size. Its order is $(q-1)/\gcd(q-1,g)$, including $g=0$. Any changes of graph representative within a neighborhood class can be absorbed in the corresponding class block, so they do not change feasibility or the count. In the two compiler cases of Section 2 every quotient map is feasible once the arithmetic test passes.

An exhaustive control over $\mathbb F_3$ enumerates the 48 invertible $2\times2$ matrices in each of the first two modes, retains pairs preserving the edge space, and obtains the unique third map from (1). On the three-edge support of $K_{2,2}$ with one deleted edge, this gives 144 ordinary and 18 determinant-one transporters, with the determinant-one count also 18 after negating one edge weight in the target. On all of $K_{2,2}$, the three counts are 2,304, 576 and zero, respectively. Enumerating vertex permutations of the seven-vertex graph made from two squares sharing a vertex gives eight automorphisms. Each induces an even permutation of the 16 grouped incidence coordinates.

## Relation to earlier work

Li, Qiao, Wigderson, Wigderson and Zhang already extract graph permutations from determinant support. Earlier project work on graph-indexed Kronecker slice spaces computes a determinant coset by identifying a normalization line and canceling the contributions of oppositely directed Hom blocks. The single-seed approach to split determinants over $\mathbb F_3$ instead uses matrix substitutions to recover a sign. Here the neighborhood-inclusion blocks give a degree-difference lattice for the weighted edge-coordinate family over arbitrary fields. The bipartite even-degree condition fixes the relative incidence sign from the input orders. It then allows the Kummer algebra to retain a field power test within one ordinary tensor isomorphism instance. The Kronecker result also supplies intrinsic recognition for its family. This theorem takes the edge-coordinate presentations as input. The unrestricted reverse reduction remains open in this work. The proof is in prose, and publication priority remains unverified. [Li, Qiao, Wigderson, Wigderson and Zhang](https://arxiv.org/html/2206.04815) · [Graph-complex incidence signs](https://arxiv.org/abs/2405.04190) · [Grochow–Qiao IV](https://arxiv.org/abs/2306.16317)
