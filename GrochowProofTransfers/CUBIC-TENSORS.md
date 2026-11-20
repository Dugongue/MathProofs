# Isomorphism of weighted three-edge-coloured cubic graph tensors

Let \(G\) be a connected simple cubic graph properly edge-coloured by three labelled colours \(A,B,C\). The three vector spaces over a field \(K\) have bases indexed by edges of the respective colours. At a vertex \(v\) write \(a(v),b(v),c(v)\) for its incident edges. Given \(w:V(G)\to K^\times\), define
\[
T(G,w)=\sum_v w(v)e_{a(v)}\otimes e_{b(v)}\otimes e_{c(v)}.
\]
Isomorphism allows arbitrary invertible linear maps on the three labelled factors. The input graphs are given in their displayed bases.

## Theorem

1. The graph has no four-cycle if and only if, for every weighting, the nonzero rank-at-most-two contractions in each factor are exactly the nonzero vectors on its dual coordinate lines. Each such contraction has rank two. A four-cycle forces a rank-at-most-two contraction using two coordinates in some factor for every weighting.
2. For graphs \(G,H\) without four-cycles, every tensor isomorphism is monomial in all three factors. Its permutations are induced by a colour-preserving graph isomorphism \(\phi:G\to H\). With \(r(v)=z(\phi(v))/w(v)\), the possible scalars are exactly the solutions of \(\prod_{e\ni v}\lambda_e=r(v)\). For fixed \(\phi\), the equations are solvable in the bipartite case precisely when the products of the \(r(v)\) on the two parts are equal. In the nonbipartite case the test is that the product of all \(r(v)\) is a square.
3. Over \(\mathbb F_q\) each passing \(\phi\) lifts to exactly \((q-1)^{|E|-|V|+1}\) isomorphisms in the bipartite case and \(\gcd(2,q-1)(q-1)^{|E|-|V|}\) in the nonbipartite case.

## Rank certificate

Fix colour \(A\). The support of contraction by \(x\in K^{E_A}\) is a bipartite graph with rows the \(B\)-edges and columns the \(C\)-edges. The contributing vertices are the endpoints of selected \(A\)-edges, and each contributes the nonzero entry \(x_{a(v)}w(v)\) at \((b(v),c(v))\). An entry cannot be repeated in a simple graph. Two contributing entries meet precisely when their vertices are joined by a \(B\)- or \(C\)-edge. The support has degree at most two, so its nontrivial components are paths and cycles and the block ranks add.

A path with \(m\) edges has rank \(\lceil m/2\rceil\). A largest matching gives a minor with a unique supported perfect matching, since distinct perfect matchings would give an alternating cycle. Its determinant is nonzero over every field, and the smaller side has size \(\lceil m/2\rceil\). A cycle of \(2k\) edges has rank at least \(k-1\) by deleting adjacent row and column vertices and using a perfect matching in the remaining path. One selected \(A\)-edge gives two disjoint entries by simplicity, hence rank two.

Suppose the graph has no four-cycle. A four-cycle in the matrix support would give a two-colour four-cycle in \(G\), so the support cycles have length at least six.

- At least four selected \(A\)-edges give at least eight matrix edges. Every path of size \(m\) contributes rank at least \(m/2\), and a cycle of size \(m\ge 6\) contributes at least \(m/2-1\ge m/3\). The total rank is at least three.
- Three selected \(A\)-edges give six matrix edges. A forest gives rank at least three. Otherwise the support is one six-cycle, corresponding to a two-colour six-cycle in \(G\). The selected \(A\)-edges would be a perfect matching of chords. Consecutive endpoints are excluded by simplicity and opposite endpoints would give a four-cycle. The remaining chords have cyclic distance two and stay in one of two parity classes of odd size. They cannot form a perfect matching.
- Two selected \(A\)-edges give four matrix edges in paths. Rank at most two forces every component size to be even, by the path rank formula. For two paths of size two, their two \(B,C\) adjacencies form a perfect matching disjoint from the selected \(A\) matching. Their union is a four-cycle. For one path of size four, number the original vertices \(1,2,3,4\) in path order. The only perfect matching disjoint from the path edges is \(\{13,24\}\), giving a four-cycle \(1,2,4,3,1\).

Conversely, a four-cycle has a colour on two opposite edges, since adjoining edges have different colours. Call the repeated colour \(A\) and select those two coordinates with nonzero coefficients. The other two cycle edges pair off the four contributing vertices. Each pair gives two entries in a single matrix row or column. The sum of the two resulting matrices has rank at most two. This proves the sharp criterion.

## Isomorphism recovery

A tensor isomorphism transports contractions by the dual change of basis in one factor and invertible left and right multiplication in the other factors. It therefore preserves contraction ranks and carries the union of coordinate lines to the corresponding union for the target. Each invertible map with that property is monomial. This holds for all three factors.

A monomial isomorphism transports support triples, which identify the graph vertices. Two vertices meet in an edge of a given colour exactly when their triples agree in that coordinate. Thus the permutations carrying one support to the other are exactly the colour-preserving graph isomorphisms. Equating coefficients at those triples gives the vertex product equations.

A colour-preserving isomorphism is determined by the image of one starting vertex. Propagate along the unique edge of each colour, checking consistency and bijectivity. At most \(|V(H)|\) candidate maps need checking. The scalar tests below give deterministic polynomial-time decision over an explicitly represented finite field, using \(u^{(q-1)/2}=1\) for the square test in odd characteristic. In even characteristic every nonzero element is a square.

## Solving and counting the scalar lifts

Choose a rooted spanning tree and let \(\epsilon(v)=(-1)^{d(v)}\), with \(d(v)\) the tree distance to the root. Put \(P(r)=\prod_v r(v)^{\epsilon(v)}\). Choose a nonzero scalar \(t_{uv}\) for each chord and divide the demands at the two ends by it. At every nonroot vertex, process the leaves upward. The remaining demand determines the scalar on the parent edge, whose factor is then divided out at the parent. The tree-edge contributions cancel in the alternating product. The last demand is one exactly when
\[
P(r)=\prod_{uv\text{ chord}} t_{uv}^{\epsilon(u)+\epsilon(v)}.
\]

In the bipartite case all chord exponents vanish, giving the test and leaving all chord scalars free. Otherwise an equal-sign chord exists, since the signs would bipartition the graph in its absence. Its exponent is \(2\) or \(-2\). Fix the other chord scalars arbitrarily. The designated chord can satisfy the equation exactly when \(P(r)\) is a square. Inverting a factor changes a product by a square, proving the unsigned test. There are \(|E|-|V|+1\) chords and the squaring kernel in \(\mathbb F_q^\times\) has order \(\gcd(2,q-1)\), giving the counts and all witness lifts.

## Examples and verification

An infinite connected bipartite family uses two copies of \(\mathbb Z/N\) for \(N\ge7\), with colours the shifts \(0,1,3\). Their six ordered nonzero differences are distinct modulo \(N\), ruling out four-cycles. The shifts \(0,1\) ensure connectivity. Triangles are compatible with the theorem. Replace every vertex of a properly edge-coloured simple cubic graph by a triangle of its three ports. Attach every original edge to its own colour port and colour each triangle edge by the third colour. A simple cycle meeting multiple triangles uses at least three original edges and three triangle edges. Truncating the three-edge-coloured \(K_4\) gives a 12-vertex nonbipartite example without four-cycles.

The orbit classification, algorithm and witness count have written proofs. The Python replay checks concrete prime-field instances. The Lean companion covers the unique-matching minor test and the rank bound from two rank-one summands.

## Provenance

[Grochow and Qiao](https://arxiv.org/abs/1907.00309) use rank to restrict change-of-basis matrices in reductions for tensor isomorphism. The graph itself forces monomiality here. The proof adapts the short local obstruction strategy of Davis and Astra’s [Haralambis proof](https://github.com/1337isnot1337/solved-conjectures/tree/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/haralambis-three-differences) and the spanning-tree normalization in their [abelian-cover proof](https://github.com/1337isnot1337/solved-conjectures/tree/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/erdos-gyarfas-abelian-covers).
