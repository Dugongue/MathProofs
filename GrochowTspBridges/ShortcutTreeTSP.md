# Exact TSP queries after editing a few shortcuts on a tree

A fixed set of shortcut endpoints is enough to compress a weighted tree into a small exact optimization problem. The compression works for closed tours, fixed-endpoint walks, subset TSP, and rooted prize-collecting walks. It retains a constant-size cost table per path, including the cost of visiting from both ends without connecting them. In the all-cities case, a query with $h$ shortcuts needs only $2^h$ parity cases and minimum spanning trees. This gives an exact edit oracle for the shortest-path metric even when one added edge changes many pairwise distances.

The construction reuses the shared-boundary idea behind the graph edit profiles motivated by Grochow–Urisman. Here the host is a tree metric under sparse edits, and the interface records parity and connectivity of a route. The same boundary reduction gives a finite routing table where the profile theorem used homomorphism moments. [Grochow–Urisman, Geometric Complexity Theory and Graph Isomorphism](https://arxiv.org/html/2606.26244v2)

## Statement

Let $T$ be a tree with $n$ vertices, nonnegative rational edge weights, and nonnegative vertex penalties $\pi_v$. Fix a nonempty set $A$ of $r$ anchors. A query supplies $h$ undirected shortcut edges whose endpoints are anchors, with nonnegative rational weights. Parallel shortcut edges are allowed. The query also specifies $s,t\in A$. The objective is the weight of an $s$-to-$t$ walk in the edited graph plus the penalties of all unvisited vertices. Set $s=t$ for a rooted closed walk. The original tree is fixed across queries.

There is an $O(n)$-arithmetic-operation preprocessing algorithm that computes tables with $O(r)$ scalar entries. Write $b$ for the number of vertices in the compressed tree. Then $b\le 2r-2$ for $r\ge 2$, and $b=1$ for $r=1$. The optimum for any query can be computed using

$$
O\bigl(2^{b-|\{s,t\}|+h}(b+h)\log(2+b+h)\bigr)
$$

arithmetic operations and comparisons. An optimum walk can be recovered by retaining the local choices. If every vertex is required instead of having a penalty, all $b$ compressed vertices are forced and the factor $2^{b-|\{s,t\}|}$ disappears. Required subsets and finite penalties can also coexist. Assign each required vertex an additional penalty greater than $2w(T)$, since a walk that visits all vertices costs at most $2w(T)$ for either endpoint convention. An optimum then visits every required vertex.

For the all-cities and subset objectives, the optimum is also that of metric TSP (or metric path TSP) on the required set, under shortest-path distances in the edited graph. Zero weights are allowed, giving the same statement for shortest-path pseudometrics. Expand metric route edges to shortest paths for one inequality. For the other, list required vertices in their order of first visit, with the specified final endpoint reserved for the last position in the open case. Shortcutting by the triangle inequality never increases route weight. With finite penalties, minimize also over the chosen set of visited metric cities. Expanding shortest paths can visit bonus cities for free, which only reduces penalties. Conversely, recording the actual visited set of any graphical walk and shortcutting preserves the penalty and gives the reverse bound.

## Proof

**Normalize multiplicities.** Represent a walk by its connected edge multiset, on its visited vertices, with odd-degree vertices exactly $\{s,t\}$ when $s\ne t$ and none when $s=t$. The singleton $s=t$ walk is allowed. The Euler trail criterion gives the converse. If any edge has multiplicity at least three, delete two copies. This preserves its positive support, leaves all parities unchanged, and does not increase cost. We can therefore use multiplicities $0,1,2$.

**Find the tree that connects the anchors.** Let $K$ be the minimal subtree of $T$ containing $A$. Keep the anchors and the vertices of degree at least three in $K$, suppress the other vertices of $K$, and retain the resulting paths $P$ as distinct edges of a compressed tree. A tree whose leaves lie in $A$ has at most $r-2$ non-anchor branching vertices if $r\ge2$. Rooting the original tree at any anchor identifies $K$ and its paths by one traversal. Every off-$K$ subtree attaches to a unique vertex of $K$.

**Summarize the off-tree branches.** For $v\in K$, let $U_v$ be the cost of paying every penalty in its hanging branches and at $v$. Let $V_v$ be the optimal branch cost conditional on visiting $v$, including penalties for vertices skipped in the branches. A branch edge is a bridge whose passage has even multiplicity, since both route endpoints lie on $K$. If a child subtree rooted at $u$ is attached by edge $vu$, the contribution when $v$ is visited is $\min(U_u,2w(vu)+V_u)$. Here $U_u$ sums all penalties in the child's rooted tree and $V_u$ is defined by the same recursion. When $v$ is skipped, all its branches are skipped. Summing these terms gives the two scalars for each vertex of $K$ by bottom-up computation.

**Summarize each suppressed path.** Let the path be $v_0,\ldots,v_m$, with interior vertices $v_1,\ldots,v_{m-1}$ and length $L$. The fees $U_{v_i},V_{v_i}$ for interior vertices only belong to the path. Endpoint fees are counted at compressed vertices. There are six relevant entries.

| Endpoints visited in the full walk | Connection through the path | Optimal local cost |
|---|---|---|
| Neither | None | Pay the skipping costs of all interior vertices. |
| Left only | None | Best doubled prefix from the left endpoint, with visit fees on that prefix and skip fees elsewhere. |
| Right only | None | Best doubled suffix from the right endpoint, with the corresponding fees. |
| Both | None | Best disjoint doubled prefix and doubled suffix with at least one missing edge. |
| Both | Odd | Traverse every edge once and pay the interior visit fees. |
| Both | Even | Traverse every edge twice and pay the interior visit fees. |

An interior vertex has even degree, and its branch traversals have even multiplicity. Its two path-edge multiplicities therefore have the same parity. At odd parity the entire path has multiplicity one. At even parity any positive part has multiplicity two. A positive stretch that reaches neither endpoint would form a component disjoint from the walk containing $s$; hence the even case is fully covered by the table. A prefix or suffix may have length zero.

All entries can be computed in $O(m)$ arithmetic operations. Write $d_i$ for distance from $v_0$, $L=d_m$, and $D_a=\sum_{i=1}^{a}(V_{v_i}-U_{v_i})$ for $0\le a\le m-1$. Define left increments $\ell_a=2d_a+D_a$ for $0\le a<m$ and right increments $r_j=2(L-d_j)+D_{m-1}-D_{j-1}$ for $1\le j\le m$. With the sum of all interior skip fees as a baseline, one-sided entries use the minimum of the relevant increments. The split entry uses $\min_{a<j}(\ell_a+r_j)$, evaluated by maintaining the minimum eligible left increment as $j$ increases. The odd and even entries use $L$ and $2L$, respectively, plus $\sum_{i=1}^{m-1}V_{v_i}$. Since the paths and branches partition the original tree edges, all tables take linear time.

**Choose active compressed vertices and odd edges.** For each set $X$ of visited compressed vertices containing $s,t$, pay the corresponding $U_v$ or $V_v$. Use the corresponding no-connection entry when at most one endpoint is in $X$. If both are in $X$, use the split entry as a baseline and form a potential connection on $X$. Give that edge an odd surcharge equal to the odd entry minus the split entry and an even surcharge equal to the even entry minus the split entry. Add available shortcuts between vertices of $X$ as potential connections with baseline zero and surcharges $w$ and $2w$. A shortcut incident to an inactive vertex cannot be used.

Every even surcharge is nonnegative. For an ordinary path, remove one edge from the doubled full path and visit all interior vertices from the two endpoints. This provides one candidate for the split of no greater cost. An odd surcharge may be negative.

Call the potential connection graph $H_X$. Reject $X$ if $H_X$ is disconnected, with a singleton treated as connected. Choose an odd-edge set $F$ in $H_X$ whose degree-parity boundary is $\{s,t\}$ when $s\ne t$, or empty when $s=t$. All other potential connections are either doubled or absent. The odd sets with the prescribed boundary form an affine coset of the cycle space. Choose their non-spanning-tree edges freely, then determine the tree-edge choices from the leaves inward by matching parity. The final root equation follows from the even cardinality of the prescribed boundary. There are at most $2^h$ possibilities, because the non-shortcut edges of $H_X$ form a forest.

**Complete each parity choice by an MST.** Pay the odd surcharges for $F$ and contract its components, including isolated vertices of $X$. Every potential edge outside $F$ is available at its even surcharge. Additional doubled edges have no parity effect. Thus among all feasible doubled choices the cheapest connects the contracted components by a minimum spanning tree, since the even surcharges are nonnegative. Concrete paths and branch choices expand that solution to a connected multigraph with the prescribed degrees. Its Euler walk realizes the computed cost. Conversely, every normalized optimum determines $X,F$, and its local costs and doubled choices are at least the respective minima. Enumerating the activation sets and parity cases and applying Kruskal's algorithm gives the stated bound.

## All-cities queries with changing anchor sets

In the all-cities case a branch off $K$ must be doubled. Its contribution can be summed as $2(w(T)-w(K))$. For each compressed path of total length $L$ and largest individual edge weight $M$, the odd, doubled, and split entries are $L,2L,2(L-M)$, respectively. Visiting every interior vertex permits a split to omit at most one edge. Omitting a heaviest edge attains its minimum. This special-case rule is already present in the kernelization literature.

For queries that change the anchors themselves, root the original tree once and store depth-first entry times and binary-lifting tables for lowest common ancestors, path sums and maxima. Sort each query's anchors by entry time and add the lowest common ancestors of consecutive anchors, which include all branching vertices of the minimal anchored tree. In the resulting list, connect each vertex to its closest ancestor in the list using a stack. Its compressed edges partition $K$. The list has at most $2r-1$ vertices and permits extraction of all path sums and maxima in $O(r\log r+r\log n)$ time. Keeping an extra non-anchor degree-two vertex is harmless. The total value-query time after $O(n\log n)$ preprocessing is

$$
O\bigl(r\log r+r\log n+2^h(r+h)\log(2+r+h)\bigr).
$$

One can therefore change the shortcut endpoints and start and finish cities without rescanning the original tree or materializing the complete metric. Expanding the original walk takes additional output time. [Baumann et al., Low-Depth Spatial Tree Algorithms, on virtual trees](https://htor.inf.ethz.ch/publications/img/luczynski-gianinazzi-ipdps-2024.pdf)

The maximum edge is essential to this summary. Take a four-vertex tree path with weights $1,1,4$, and add a shortcut of weight $1$ joining the path endpoints. The cheapest all-city closed walk costs $6$: omit the weight-$4$ edge, double the other tree edges and double the shortcut. Replace the tree weights by $2,2,2$, so the original endpoint distance stays $6$. Now the cheapest closed walk costs $7$, taking the cycle once. The two instances have the same anchor distances before editing and different exact TSP values after the same edit.

## Literature and scope

Blažej, Choudhary, Knop, Schierreich, Suchý and Valla give feedback-edge-set kernels for TSP and waypoint routing. Their Reduction Rule 7 already uses a heaviest edge to encode the case in which a compulsory degree-two path is visited from both ends. The result above builds on that structural fact. Its particular additions are tables for penalties and optional compressed vertices, the explicit odd-coset plus MST optimizer, and exact repeated value queries with changeable shortcut endpoints in the all-cities case. Rank-based connectivity algorithms already give a single-exponential bound in treewidth. The theorem here exploits the tree-plus-edits representation and its preprocessing. The literature checks did not establish priority for the combined statements. [On Polynomial Kernels for Traveling Salesperson Problem and its Generalizations](https://arxiv.org/html/2207.01109) · [Bodlaender–Cygan–Kratsch–Nederlof](https://arxiv.org/abs/1211.1505)

Landete, Plana, Sainz-Pardo and Sanchis study jointly choosing cost upgrades under a budget and a graphical TSP walk. They develop a branch-and-cut formulation. The queries here optimize the walk **given** shortcut edits. This lets their model and other upgrade or network-design searches use the exact oracle whenever the base network and candidate shortcuts have the stated form. Selecting edits under a budget requires an outer optimization. [Upgrading edges in the Graphical TSP](https://doi.org/10.1016/j.cor.2023.106321)

The general algorithm has a mathematical proof. [The control program](check_shortcuts.py) compares the table algorithm to separate shortest-path and Held–Karp computations on small instances, covering closed and open variants, optional vertices, zero weights, parallel shortcuts and selected repeat queries.

The variant allowing penalties for skipped cities follows the penalty-only formulation of prize-collecting TSP. Its open path version is also called Prize-Collecting Stroll. The exact algorithm above exploits the edited tree representation. General metric prize-collecting algorithms address a broader input class with approximation guarantees. [Bienstock–Goemans–Simchi-Levi–Williamson](https://math.mit.edu/~goemans/PAPERS/BienstockGSW-1993-PrizeCollecting.pdf) · [Blauth–Klein–Nägele](https://arxiv.org/abs/2308.06254)
