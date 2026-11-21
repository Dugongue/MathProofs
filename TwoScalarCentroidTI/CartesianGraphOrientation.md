# Intrinsic Cartesian graph frames for ternary cube-zero orientation

Work over \(F=\mathbb F_3\). A transporter of based symmetric bimaps is a pair \((g,h)\) satisfying \(h\beta(x,y)=\beta'(gx,gy)\). The cube-zero character is \(\det(g)\det(h)\). For a connected simple graph \(G\) with a marked vertex \(v_*\), define its bimap \(\beta_G:X\times X\to Z\) on vertex vectors \(x_v\). Use independent labels \(z_{vw}\) for edges and \(z_v\) for all vertices other than \(v_*\). Set
\[
 \beta_G(x_v,x_w)=z_{vw}\quad(vw\in E(G)),\qquad
 \beta_G(x_v,x_v)=z_v\quad(v\ne v_*),
\]
and make every remaining basis product zero. The raw bimap is supplied in arbitrary bases, with no graph, factorization or frame supplied.

**Theorem.** Suppose the recovered graph is a connected Cartesian product with at least three even-order nontrivial prime factors and with every vertex degree odd. Then the sign-prescribed comparison for \(\beta_G,\beta_{G'}\) reduces in deterministic polynomial time to one ordinary three-tensor isomorphism instance over \(F\). Both the bimap and the dual relation bimap have scalar centroid and zero common radical. The relation space has full contraction support. Moreover \(\dim X\) is even and \(\dim Z\) is odd, so these are instances of the two-scalar-centroid cube-zero sign problem.

With at least four even-order prime factors, the character of every ordinary transporter is fixed by an endpoint frame ratio computable before the query. Thus this case needs one unpinned ordinary guard after calibration. With exactly three even-order prime factors, at most six branches of intrinsic factor-layer pins suffice, and their ordinary disjunction gives the single output. The class is polynomial-time recognizable in arbitrary bases. It contains a subfamily to which arbitrary graph isomorphism reduces, even with the prescribed positive sign. [Cube-zero orientation and the exact cubic bridge](ExactCubicOrientationSeed.md) · [Both-scalar relation normal form](DualRelationOrientationSeed.md)

## 1. The graph and its marked vertex from the raw bimap

For any connected Cartesian graph with at least three nontrivial factors, the following condition holds. For distinct vertices \(u,v\), there is a neighbor \(w\) of \(v\) which differs from \(u\) in at least two coordinates. If \(u,v\) differ in one or two coordinates, move from \(v\) in a third or other unchanged coordinate. If they differ in at least three, any single move leaves at least two differences. In particular \(uw\) is a nonedge and \(w\ne u,v\).

Compute the projection to the input operators of the solution space of
\[
 B\beta(x,y)=\beta(Ax,y)+\beta(x,Ay).
 \tag{1}
\]
It is the full diagonal algebra in the vertex frame. To see this, for \(u\ne v\) take \(w\) as above and evaluate (1) on the zero product \(\beta(x_u,x_w)\). The coefficient of \(z_{vw}\) comes only from the entry \(A_{vu}\). Products in the second term all use the vertex \(u\), different from both \(v,w\). Hence \(A_{vu}=0\). Conversely every diagonal \(A\) extends to \(B\) by the sum of endpoint entries on an edge label and twice the entry on a square label. The missing square causes no constraint. The projected algebra in (1) is covariant under the actual \(g\) by conjugation.

Recover its primitive idempotents by refining with \(1-(A-aI)^2\), \(a\in F\), for a basis of the algebra. On a promised input these are the distinct coordinate projections. Choose one nonzero representative \(x_v\) of each recovered line. Recover the graph from the nonzero products on distinct lines, and \(v_*\) as the unique zero square. These steps do not guess a graph or a base change. For a raw recognizer, check that the projected space is an algebra, the refinement gives \(\dim X\) rank-one projections summing to the identity, and the products on the marked square and the graph lines have precisely the asserted vanishing and independence. Test connectedness and factorization on the recovered graph. All steps use polynomial linear algebra and graph operations.

The bimap has no common radical because every vertex has an incident edge: for any nonzero coefficient at \(v\) in \(x\), multiplying by a neighbor \(x_w\) detects it in the \(z_{vw}\) coordinate. The outputs span by construction. Its centroid is scalar even without the square labels. More generally, for any graph with independent edge labels and minimum degree at least two, the centroid equation \(\beta(Ax_u,x_w)=\beta(x_u,Ax_w)\) forces \(A_{vu}=0\) for \(v\ne u\), using a neighbor \(w\) of \(v\) different from \(u\) and the independent label \(z_{vw}\). This argument permits any extra independent square labels. Diagonal entries agree at the endpoints of every edge, so a connected graph gives the same scalar everywhere. The scalar on the label mode is forced by spanning.

The relation space \(K\subseteq\operatorname{Sym}^2 X\) has basis the nonedge monomials and \(x_{v_*}^2\). Its dual bimap on \(X^*\) is therefore the complement graph bimap with a square at \(v_*\) alone, up to nonzero label normalization. The complement is connected and has minimum degree at least two. Indeed write \(n_i\ge2\) for all nontrivial Cartesian factor orders and \(n=\prod_i n_i\). The maximum degree of the product is at most \(\sum_i(n_i-1)\le n/2-1\) if there are at least three factors. The inequality follows by putting all \(n_i=2\) and noting that each increase in one \(n_i\) increases the right side by at least twice as much as the left. The complement has minimum degree at least \(n/2\), which also forces connectedness. The same edge-label argument gives scalar centroid, full image and zero common radical in the relation bimap. In particular \(K\) has full contraction support.

Every transporter matches the recovered vertex lines by a graph isomorphism \(\pi\) preserving the marked vertex, and scales the chosen representatives by units \(\lambda_v\in F^\times\). Conversely any such graph isomorphism and vertex scalars lift by the values on the displayed product labels. Put the marked vertex first in the vertex frame, and place the square labels in the remaining vertex order. The permutation on the square labels has the same determinant sign as the vertex permutation, so those signs cancel in the combined character. Each edge label contributes its two endpoint scalars and each square contributes a square scalar. All degrees are odd, so in these adapted frames
\[
 \det(g)\det(h)=\operatorname{sgn}(\pi_E)\prod_v\lambda_v^{1+\deg(v)}
             =\operatorname{sgn}(\pi_E). \tag{2}
\]
The ratio of target to source determinants of the two adapted-to-raw frames supplies the exact raw calibration.

The total vertex count is even. Every edge layer has size \(|E_i|\prod_{j\ne i}n_j\), which is even because at least three factor orders are even. Thus \(\dim Z=n-1+|E(G)|\) is odd. The multiplication algebra \(F1\oplus X\oplus Z\) is commutative unital with \(J^3=0\), and its total dimension is even. Its algebra isomorphisms have determinant exactly the combined character on the two radical grades, independently of the lifts. Hence the exact ternary cubic bridge applies to these comparisons as well. [Prior relation orientation](DualRelationOrientationSeed.md)

## 2. Edge parity in Cartesian product frames

Use the polynomial-time Cartesian prime factorization with its intrinsic prime edge classes. An isomorphism matches those classes. In product coordinates this is a factor permutation followed by individual factor isomorphisms. For example, after matching the edge directions, varying any one coordinate leaves every other target coordinate fixed, by following paths using only its direction. Hence each target coordinate depends only on the matched source coordinate. [Feigenbaum–Hershberger–Schäffer, prime factorization of Cartesian products](https://www.cs.yale.edu/homes/jf/FHS-DAM85.pdf)

Order the factor slots by the descriptors \((n_i,m_i)=(|V_i|,|E_i|)\), using arbitrary choices inside equal descriptors. Choose arbitrary vertex and edge orders within each factor. Use the resulting lexicographic edge list for the product, organized first by edge layer \(i\), then by \(E_i\) and the fixed vertex coordinates in the other slots. If the two descriptor lists disagree, no graph isomorphism is possible. Otherwise these give compatible abstract edge coordinate sets on the two sides. Record the chosen edge orders in the label frames used for (2).

Consider a within-factor isomorphism in slot \(s\), with the other slots fixed. Its sign on its own edge layer is the sign on \(E_s\) raised to the power \(\prod_{j\ne s}n_j\). On layer \(i\ne s\) the sign is the sign on \(V_s\) raised to \(m_i\prod_{j\notin\{i,s\}}n_j\). Each exponent is even when there are at least three even orders. Thus the edge action of every such factor map has sign one in the corresponding product edge frames. This statement does not require the maps on factor vertices or edges to be determined.

It therefore suffices to compute the sign of a permutation of the equal-descriptor slots. For a transposition of slots \(s,t\) of equal descriptor \((n,m)\), this sign is \((-1)^d\) with
\[
 d=mn\prod_{j\notin\{s,t\}}n_j
   +\binom n2 \sum_{i\notin\{s,t\}}m_i\prod_{j\notin\{i,s,t\}}n_j .
 \tag{3}
\]
Indeed layers \(s,t\) exchange by inverse bijections of \(mn\prod_{j\notin\{s,t\}}n_j\) coordinates. Every other layer swaps two \(n\)-valued vertex coordinates, which transposes \(n(n-1)/2\) entries for every fixed other tuple and every fixed edge of that layer. This is a statement about the pure coordinate permutation, so it also holds when the equal-descriptor slots represent different graphs. For an actual isomorphism any subsequent individual graph maps have already been accounted for.

With at least four even-order factors, every term on the right of (3) is even. The second term has at least one even spectator even after omitting \(i,s,t\), and the first either includes its even \(n\) or still has an even spectator. Consequently every isomorphism has edge sign one in these product frames. If there are exactly three even-order factors, every swap of odd-order slots is still even by (3). Thus only the bijection of the three even slots matters. Its effect is computable by (3), or directly by explicitly permuting the polynomial-size list of abstract edge positions and computing its inversion parity.

## 3. One ordinary instance

For at least four even factors compare the prescribed raw sign to the frame ratio in (2). A mismatch yields a fixed negative instance. If it agrees, use the ordinary bimap comparison as the guard, with the same map on its two equal input places.

For exactly three even-order factors enumerate their at most six bijections respecting descriptors. In each branch compute the sign of its coordinate permutation on the product edge list and keep the branch only if that sign multiplied by the raw calibration is the desired sign. Impose the proposed mapping of each even edge layer by marking the inclusion of the span of its edge labels into the actual \(Z\)-role. This is an ordinary linear record. Since actual label maps permute the individual edge lines, each inclusion forces exactly the designated layer match. Conversely a transporter inducing that match extends to the inclusion records. Odd-order factor permutations are unconstrained and contribute sign one. Thus each retained branch is an ordinary typed comparison on the same raw maps, and its sign is the required one. Every requested signed witness appears in one retained branch.

There are at most three such marks, in addition to the bimap and its shared input slots. A constant-size tensor system of order at most three compiles to one ordinary TI instance. The disjunction over the constant number of branches is an ordinary TI disjunction. One explicit OR for two pairs compares the products encoding \(\{(A,C),(B,D)\}\) and \(\{(A,D),(B,C)\}\), with each ordered pair represented as a marked combined tensor and then as a connected triangular multiplication algebra. Its primitive central factors must match, giving exactly \(A\cong B\) or \(C\cong D\). Multiplication tensors of unital associative algebras compare their algebra isomorphism types by unit normalization. The ordered-pair and triangular-algebra constructions have linear side overhead, so this preserves the polynomial bound. [Tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4) · [Linear-length reductions and ordinary Boolean packing](https://arxiv.org/abs/2306.16317)

## 4. An unbounded graph-isomorphism subfamily

Given any nonempty finite simple graph \(H\), add a new marked root \(r\) adjacent to every original vertex. Replace every edge of this rooted connected graph by two disjoint length-two paths with new internal vertices, producing \(D(H)\). It is a connected simple bipartite graph, and every vertex has even degree: each original degree doubles and each added vertex has degree two. A rooted isomorphism of \(D(H)\) preserves the bipartition since its root lies on the original-vertex side. Restricting to that side and reading adjacency by length-two connections recovers the original rooted graph. Conversely a rooted isomorphism of the original graphs extends to these subdivided paths. Thus \(D(H)\) with its root exactly represents the original unrooted graph isomorphism problem.

Take the Cartesian product
\[
 G(H)=D(H)\ \square\ K_2^{\square5}
\]
and mark the vertex consisting of the root and the zero corner of the five-cube. All graph degrees are odd, and at least five Cartesian prime factors have even order. The preceding recognition and scalar-centroid results apply. A rooted graph isomorphism of these products matches their rooted prime factors, since the root coordinate on each factor is carried to the corresponding root coordinate. Cancel the five equal rooted \(K_2\)'s from the two multisets of rooted prime factors. This leaves a rooted isomorphism of the \(D(H)\)'s, even when either \(D(H)\) already has extra \(K_2\) factors. The converse is obtained by multiplying the rooted map with the identity on the five-cube. Consequently the graph products, and hence their associated bimaps, are ordinarily equivalent exactly when the original graphs are isomorphic.

Output the bimaps in the calibrated product edge frames, with the marked vertex first. Every ordinary transporter then has positive combined sign. This gives a polynomial-time reduction of arbitrary graph isomorphism to the signed problem on the stated recognizable class. For any one of these examples, reflecting one target label basis vector instead produces ordinary YES and positive-sign NO against the original source. Thus the endpoint sign calibration is necessary. There is no restriction on the number or parity of the graph automorphisms; for example the five equal cube factors already permit a symmetric group action fixing the marked corner.

These are written proofs for the specified both-scalar-centroid class. They use an intrinsic Cartesian frame and do not supply a frame for arbitrary scalar-centroid cube-zero bimaps.
