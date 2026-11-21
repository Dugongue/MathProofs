# Quantum isomorphism reduces to classical transport across matching-linked color cells

## GP-0953

For an $n$-vertex graph with adjacency matrix $A$, seed vertex color refinement with the vectors $((A^j)_{vv})_{0\le j<n}$. Let $X$ be a source graph for which the resulting stable cells induce cliques or independent sets. Suppose each pair of distinct cells has a complete or empty bipartite block, or two equally sized cells joined by a perfect matching or its bipartite complement. On the graph of cells, retain a link exactly for the blocks that are neither complete nor empty. The resulting link graph may contain arbitrary cycles. Then $X$ is quantum isomorphic to an arbitrary target $Y$ if and only if $X$ and $Y$ are ordinarily isomorphic, and an isomorphism can be found deterministically in polynomial time. This applies in particular to classically compact sources satisfying the hypotheses. [Baptista et al., compact graphs and quantum automorphisms](https://arxiv.org/abs/2606.13928)

## Invariance of the cells

For clarity, use a magic unitary $U$ with entries in a nonzero unital $C^*$-algebra and $UA_Y=A_XU$. Such a unitary is required by the corresponding quantum isomorphism models; a classical isomorphism supplies a scalar one. If the orders disagree the algorithm rejects immediately. For each $j$, $UA_Y^jU^*=A_X^j$. Row orthogonality gives
$$
(A_X^j)_{xx}1=\sum_y (A_Y^j)_{yy}u_{xy}.
$$
Multiplying by $u_{xy}$ forces agreement of the two seed vectors whenever $u_{xy}\ne 0$. Run refinement on the disjoint union so that colors have common names. Once $U$ preserves a color, it takes its indicator on $Y$ to the indicator on $X$. Intertwining implies the same equality for the two corresponding neighbor-count vectors. Multiplying the relevant equality by $u_{xy}$ forces equality of their counts whenever $u_{xy}\ne 0$. Induction shows the stable cells are preserved. Summing entries in a color block by rows and by columns shows the class sizes match. Neighbor counts between every matched pair also agree. [Atserias et al., quantum and non-signalling graph isomorphisms](https://arxiv.org/abs/1611.09837)

An algorithm can first reject mismatching class sizes or quotient counts. The joint refinement restricts to the separate stable partition on each side, since the successive splits restricted to either component are the same counts to its own cells, up to renaming and zero coordinates. The matching quotient data imply that $Y$ has the same clique, empty, complete, matching and complement-of-matching block types. For example, when both side sizes are $m$, degree one on both sides gives a perfect matching, and degree $m-1$ on both sides gives its complement. Use the matching convention when both interpretations apply.

## Transport along links and across all remaining cycle constraints

In one connected component of the link graph, all cells have the same size $m$. For a directed link $i,j$, let $M^X_{ij}$ and $M^Y_{ij}$ be the permutation matrices of its designated matching, with rows in $i$ and columns in $j$. Writing $U_i$ for the corresponding magic block, the adjacency equation gives
$$
U_iM^Y_{ij}=M^X_{ij}U_j.
$$
For a complement block this follows by subtracting the all-ones matrix, which absorbs magic matrices on both sides. Choose a root and a spanning tree in the link component. In each graph, identify every cell's coordinates with the root coordinates by transport along the tree matchings. In these coordinates the tree matchings are identities, so all blocks $U_i$ become the same magic matrix $W$. Each off-tree link, oriented once, gives a pair of permutation matrices $P^X_i,P^Y_i$ satisfying $WP^Y_i=P^X_iW$.

Let $F$ be the free group on the off-tree links, acting in the two root coordinate sets by their associated permutations. The equations also hold for inverses and products, so for every word $g\in F$,
$$
P^X(g)=WP^Y(g)W^*.
$$
By row orthogonality the diagonal indicator of a vertex being fixed by $g$ agrees at $x,y$ whenever $w_{xy}\ne 0$. Thus any such pair has identical stabilizers in $F$. The map $g\cdot x\mapsto g\cdot y$ is then a well-defined equivariant bijection between their two transitive orbits. In particular, $W$ only links vertices lying in orbits of the same equivariant isomorphism type. For any one orbit type, summing the entries of $W$ over its rows and columns counts the corresponding vertices in $X$ and $Y$, so the counts agree. All orbits of a given type have the same size, hence both sides have the same number of them. Pair equivalent orbits to obtain an ordinary root bijection intertwining all off-tree permutations simultaneously. Its transports across the spanning tree preserve every matching and complement block. Components can be processed independently because the blocks between them are complete or empty.

There is no need to enumerate words of $F$. Compute generator orbits by graph search using the permutations and their inverses. To test if two orbits are isomorphic, fix a starting vertex on the first and try every starting vertex on the second. In each trial, propagate the forced pairing under the generators and inverses. Reject if propagation ever violates functionality or injectivity. Otherwise transitivity visits all vertices on both sides and the result is an equivariant bijection. Apply this procedure to classify orbits, compare the multiplicities and construct the paired bijections. This algorithm, together with the walk counts and refinement, is deterministic polynomial time. The largest walk-count integers have $O(n\log n)$ bits. Discrete and twin-class partitions are included, as are cells linked by arbitrarily many matching cycles. The compact-graph application is restricted to the displayed block hypotheses.
