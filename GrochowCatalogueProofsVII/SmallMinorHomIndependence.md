# Small forbidden minors whose own homomorphism counts are independent

## GP-0823

For every nonempty connected graph $H$ on at most four vertices, there are explicit simple graphs $G,G'$ such that all $H$-minor-free source graphs have equal homomorphism counts into $G,G'$, but $H$ does not. In particular every connected graph witnessing the count dependence asked in GP-0823 has at least five vertices. The proof includes the paw and diamond, for which testing only ordinary degree data is insufficient. [Known excluded-minor examples of count dependence](https://arxiv.org/html/2610.03550v2)

Homomorphism counts multiply across source components, so throughout it suffices to consider connected tests. Write $P_j,C_j,K_j$ for the path, cycle, and complete graph of order $j$.

### Orders at most three

For $H=K_1$ the only permitted source is empty, so take $K_1,K_2$ as targets. For $H=K_2$ the sources are edgeless, so take $K_2$ and two isolated vertices. For $H=P_3$, each permitted component is $K_1$ or $K_2$. The targets $P_3\sqcup K_1$ and $K_2\sqcup K_2$ have the same order and edge count, but their $P_3$ counts are respectively 6 and 4, from the sum of squared degrees. For $H=K_3$, the permitted connected tests are trees, which have target count $n d^{|E(T)|}$ in every $d$-regular target on $n$ points, by successively extending along tree edges. The targets $C_6$ and $K_3\sqcup K_3$ differ on triangles.

### The claw, the four-vertex path, and the four-cycle

For the claw, an allowed source has maximum degree at most two because any vertex of degree three gives a claw by edge deletions. Use the once-subdivided claw and $C_6\sqcup K_1$ as targets. To see that these have equal path and cycle counts, present the subdivided claw on independent sets $X=\{x_0,x_1,x_2,x_3\}$ and $Y=\{y_1,y_2,y_3\}$ with each $y_i$ adjacent to $x_0,x_i$. On $X$ use the orthogonal matrix $J_4/2-I_4$ and on $Y$ use the identity. Conjugating the adjacency matrix complements each two-element column into $X$, so gives the other target. The conjugating matrix fixes the all-ones vector. Therefore the traces $\operatorname{tr}(A^j)$ and total walk counts $\mathbf 1^{\mathsf T}A^j\mathbf 1$ agree. The claw counts $\sum_v d(v)^3$ are 54 and 48.

Any connected $P_4$-minor-free source is a star or a triangle. A tree containing no $P_4$ has diameter at most two. A cycle of length at least four contains a $P_4$ as a subgraph, and a triangle joined to any additional vertex in its component also gives a $P_4$. Use two trees of degree sequence $(3,2,2,1,1,1)$, as follows. In the first, join the degree-three vertex to the two degree-two vertices and to one leaf, and attach one leaf to each degree-two vertex. In the second, join the degree-three vertex to two leaves and to the first degree-two vertex, then join the two degree-two vertices and attach the remaining leaf to the second. The degree multiset determines all star counts, and both targets have zero triangle count. Yet $\operatorname{hom}(P_4,\cdot)=2\sum_{uv\in E}d(u)d(v)$ gives 38 and 36.

A $C_4$-minor-free graph has no cycle of length at least four, since such a cycle contracts to $C_4$. Use $C_8$ and $C_4\sqcup C_4$ as targets. Any source with a triangle has zero count into both targets, which are triangle-free. Remaining allowed connected sources are trees, and the equal sizes and degrees give agreement on them. The $C_4$ counts are 48 and 64. Indeed on each cycle one has six closed walks of length four per starting vertex from two steps in each direction, and $C_4$ has two additional walks per starting vertex that completely wind around it.

### The paw

The paw is a triangle with a pendant edge. Every connected paw-minor-free source is either a tree or a cycle. If a cycle leaves out a vertex of the connected graph, a path out of the cycle gives an edge to a vertex outside it. Contract the cycle to a triangle retaining the attachment vertex and delete unwanted edges. This gives a paw. If a cycle spans and has a chord, the chord and one arc give a smaller cycle to which the argument applies.

Let $X=C_6$, $Y=K_3\sqcup K_3$. Take $G$ to be the cone over $X$, disjoint union with $Y$, and $G'$ the cone over $Y$, disjoint union with $X$. The partition into the six cone-base vertices, the six other vertices, and one apex gives the same sizes and per-cell neighbor numbers in both graphs. Counts of homomorphisms from a rooted tree with root assigned to a vertex depend only on its cell, by multiplying the independent neighbor sums for its children. Thus all tree counts agree. The adjacency matrices have the same spectrum. On the zero-sum subspaces of the two six-point cells they give the nonconstant eigenvalues of $X,Y$ together in either order, since the apex link is uniform. Their actions on the span of the three cell indicators have the same quotient matrix. Thus cycle counts agree as well. For the paw the count is $\sum_v d(v)(A^3)_{vv}$. The $12$ directed closed triangle walks internal to $Y$ are weighted by 2 in $G$ and by 3 in $G'$. All triangle walks involving the apex contribute the same on both sides, because the two regular base graphs have the same number of edges. The paw counts differ by $12$.

### The diamond

The diamond is $K_4$ minus one edge. Every block of a diamond-minor-free graph is an edge or a cycle. In fact a 2-connected block containing more than a given cycle has a chord of that cycle or an ear with distinct endpoints on it, by 2-connectivity. The chord or ear and the two cycle arcs make three internally disjoint paths with the same ends. At most one path has length one in a simple graph, so contract the paths to lengths $1,2,2$ to obtain a diamond minor.

Into vertex-transitive cospectral targets of equal order, all such sources have equal counts. For a connected source peel its leaf blocks, each touching the remainder at one cut vertex. Holding the cut vertex's image fixed, a leaf edge has extension count equal to the target degree, and a leaf cycle $C_j$ has extension count $(A^j)_{vv}=\operatorname{tr}(A^j)/n$, independent of $v$ by transitivity. The last block likewise has a count determined by the degree and traces.

Use the two circulants on $\mathbb Z/20$ with step sets $D=\{\pm1,\pm3,\pm4,\pm6\}$ and $D'=\{\pm1,\pm4,\pm6,\pm7\}$. Their common characteristic polynomial is
$$
x^3(x-8)(x^2-5)^2(x^2+4x-1)^2(x^4-10x^2+5)^2.
$$
One exact check of the identity uses $u_0(j)=[j=0]$ on $\mathbb Z/20$, $u_{i+1}(j)=\sum_{d\in D}u_i(j-d)$, and similarly for $D'$. For each step set, setting $c_0=1$ and $c_k=-\sum_{i=1}^k c_{k-i}\,20u_i(0)/k$ produces the coefficients of the displayed polynomial by Newton's identities. For the diamond, assign images to its adjacent degree-three vertices and independently choose a common neighbor for each degree-two vertex. Its count is $20\sum_{d\in D}|D\cap(d+D)|^2$. The common-neighbor counts at the positive steps $1,3,4,6$ are $2,4,2,1$; at $1,4,6,7$ for the other set they are $2,0,3,4$. The negative steps repeat these counts. Thus the diamond counts are 1000 and 1160.

### The complete graph on four vertices

A $K_4$-minor-free graph has treewidth at most two, by the characterization of partial 2-trees. Use the $4\times4$ rook graph and the Shrikhande graph as targets. Both are strongly regular with parameters $(16,6,2,2)$, and graphs with the same strongly regular parameters are indistinguishable by 2-WL. Indeed pair colors are equality, adjacency, and nonadjacency, and the number of common neighbors and the other extension counts for a pair depend only on its color and the parameters. By the treewidth characterization of 2-WL, the two targets have equal counts from every graph of treewidth at most two. The rook graph contains a $K_4$ in each row, while the Shrikhande graph has no $K_4$ since the graph on the neighbors of any vertex is a six-cycle. [Bounded-treewidth homomorphism characterization](https://arxiv.org/abs/1802.08876) · [The common parameters and the distinct neighborhoods](https://github.com/Dugongue/MathProofs/blob/53ffa5dcacaca5757e11adca8df99ba0d38f8bc5/GrochowCatalogueProofsVI/CoherentExponentiationAndFusions.md)

These cases exhaust the connected isomorphism types through order four.
