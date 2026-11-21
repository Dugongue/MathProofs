# Approximating hypergraphic matroid intersections by one permanent

For two explicitly presented unions of hypergraphic matroids on a common ground set, one monotone substitution into the permanent produces a polytope that approximates their common independence polytope. The error is controlled by the shortest incidence cycle in the input hypergraphs. A separate two-order construction gives an optimal-size quadratic max-plus formula for factor-two approximation of maximum spanning tree.

## One permanent and an incidence-girth guarantee

Let \(E\) be a finite set of labels, \(m=|E|\). On each side \(b=1,2\), let a finite collection of hypergraphs \(H_{bi}\) represent matroids on \(E\). The hyperedge \(H_{bi}(e)\) is a subset of a vertex set \(V_{bi}\). Repeated hyperedges are permitted, with distinct labels. An absent label, or a hyperedge of size at most one, acts as a loop in the corresponding matroid. An independent set of a hypergraphic matroid has a *forest shrinking*, which replaces each of its hyperedges by a labeled pair of distinct vertices in that hyperedge so that the resulting graph has no cycle. Two parallel pairs count as a cycle of length two. This is the forest representation of the Lorea–Lovász hypergraphic matroid. Use disjoint tagged copies of \(V_{bi}\), even when the vertex sets in different hypergraphs have names in common. [Forest characterization and original references](https://doi.org/10.1112/jlms.70668)

An independent set of the union on side \(b\) can be partitioned among the \(H_{bi}\), with a forest shrinking in each. Let \(\mathcal I\) be the sets independent in both unions and \(P=\operatorname{conv}\{\mathbf1_I:I\in\mathcal I\}\). A side-\(b\) *allocation* injectively assigns each element \(e\) of a subset of \(E\) to a slot \((i,v)\) with \(v\in H_{bi}(e)\) and \(|H_{bi}(e)|\ge 2\). Let \(Q\) be the convex hull of the incidence vectors of the subsets admitting allocations on both sides.

The incidence graph of \(H_{bi}\) has vertex nodes \(v\in V_{bi}\), distinct hyperedge nodes \(e\), and edges for the incidences \(v\in H_{bi}(e)\). Suppose none of these graphs contains a cycle of length less than \(2g\), where \(g\ge 2\) is an integer. Set \(\alpha=1-1/g\). Then
\[
          \alpha Q\ \subseteq\ P\ \subseteq\ Q .
\]
Both inclusions hold for the same \(Q\). Its vertices are exactly the exponent vectors of the monomials in a monotone substitution into a single permanent of width \(m+\sum_{b,i}|V_{bi}|\). Its sparse LP extension uses \(O(m+\sum_{b,i}|V_{bi}|+\sum_{b,i,e}|H_{bi}(e)|)\) inequalities. In particular, for every real weight vector \(w\), one max-plus permanent computes \(U=h_Q(w)\) and
\[
   (1-1/g)U\le \max_{I\in\mathcal I} w(I)\le U .
\]
Thus the assignment values give a factor \(g/(g-1)\) approximation. Every ordinary hypergraph meets the \(g=2\) hypothesis. Simple graphs meet it for \(g=3\), and graph girth at least \(g\) also suffices. Acyclic incidence graphs give \(P=Q\).

### The assignment and its support

Write \(L\) and \(R\) for the sets of slots on the first and second side. Make a square matrix with both indices in \(L\sqcup E\sqcup R\). Put \(1\) on the diagonal. Put \(x_e\) on \(l\to e\) when \(l\) is eligible for \(e\), and \(1\) on \(e\to r\) when \(r\) is eligible. Put \(1\) on all \(R\to L\) entries and \(0\) elsewhere.

A nonzero permutation term is a directed cycle cover using the indicated edges. An element \(e\) is either a loop or appears in a segment \(l\to e\to r\). The active elements occupy distinct left and right slots. Conversely, simultaneous allocations can be completed by using \(r\to l\) to close each active segment, and using loops at the unused indices. The exponent vector of the term is the indicator of the active set. This proves the support assertion over the nonnegative reals and the formal Boolean semiring, and gives the max-plus value identity under \(1\mapsto 0\), \(0\mapsto-\infty\), \(x_e\mapsto w_e\). Multiple allocation witnesses can yield the same monomial.

Equivalently, \(Q\) projects from a face of the Birkhoff polytope by summing the allowed entries \(l\to e\) for each \(e\). A sparse extension sends circulation around
\[
s\longrightarrow L\longrightarrow E^-\longrightarrow E^+\longrightarrow R
\longrightarrow t\longrightarrow s .
\]
The \(L\to E^-\) and \(E^+\to R\) arcs encode eligibility. Use one unit-capacity \(e^-\to e^+\) arc per ground element, unit capacities out of \(s\) and into \(t\), and return capacity \(m\). Eligibility arcs can also have unit capacity. Project onto the flow on each \(e^-\to e^+\). Integral circulations give allocations and every pair of allocations extends to a circulation. The directed incidence matrix gives integrality. The matrix construction exhibits an explicit positive case of Grochow’s Newton-polytope mechanism. His main lemma transfers exact projection lower bounds through faces of Newton polytopes. Here the two-sided sandwich specifies when the same permanent produces a small approximate formulation. [Grochow, *Monotone Projection Lower Bounds from Extended Formulation Lower Bounds*, Main Lemma 3.1](https://theoryofcomputing.org/articles/v013a018/)

### Repair on both sides at once

For an independent set on either side, root each component of its chosen forest shrinking and orient its pairs toward the root. The tails are distinct in each tagged vertex set. Assigning elements to these tails gives the desired allocation. Applying this to both sides proves \(P\subseteq Q\).

Conversely, take a set \(S\) admitting allocations on both sides and fix a pair of allocations. On each side shrink every allocated hyperedge \(e\) to a pair directed from the assigned slot to any other vertex in \(H_{bi}(e)\). Every tagged vertex has outdegree at most one. A weak component with \(k\) vertices thus has at most \(k\) edges and at most one undirected cycle. Each such cycle of length \(d\), alternating its vertices with its distinct hyperedge labels, gives a length-\(2d\) incidence cycle in \(H_{bi}\). Hence \(d\ge g\).

List the cycles on both sides. Let \(B\) be the matrix whose rows are these cycles and whose columns are selected elements \(e\in S\), with \(B_{Ce}=1\) if \(e\in C\). Every column has at most one \(1\) in each of the two row classes. Negating the rows on the second side makes \(B\) a submatrix of a directed node–arc incidence matrix. One may supply a dummy node for columns with a single nonzero entry. Consequently \(B\) is totally unimodular, and
\[
       \{z\in[0,1]^S : Bz\ge\mathbf1\}
\]
is the convex hull of integral deletion vectors that meet all cycles. The constant vector \(z_e=1/g\) is feasible. Choose a convex decomposition of that vector into integral deletions. Every retained set is in \(\mathcal I\), since its shrunk graphs are forests on both sides. Its expected incidence vector is \((1-1/g)\mathbf1_S\), proving the inner inclusion on each generator of \(Q\) and hence on all of \(Q\). If there are no incidence cycles, no deletions are needed.

For a solution-returning algorithm, choose optimizing allocations for the assignment and then minimize \(w\cdot z\) over the displayed integral covering polytope. This gives a common independent set with weight at least \((1-1/g)U\). The scalar \((1-1/g)\) times the assignment value itself is a certified lower approximation requiring just one assignment gate and one positive rational scaling, or one assignment with the input weights scaled by that constant. The raw max-plus permanent supplies the upper value without scaling. A unit-weight cycle of length \(g\), represented on both sides by the same simple graph for \(g\ge 3\), attains equality: \(U=g\) while the optimum is \(g-1\). Two parallel hyperedges on a pair attain equality for \(g=2\).

## Feasible supports from two orders and pure max-plus formulas

Fix an order on the vertices in each constituent hypergraph. Restrict an element to a slot when that vertex has some strictly earlier vertex in the same hyperedge. Every allocation now shrinks to a forest by directing each pair from the slot to an earlier vertex. If its underlying graph contained a cycle, the greatest vertex on that cycle would have two outgoing edges, contrary to the slot constraint.

For a single union, compute the best allocation under these orders and under their simultaneous reversal. The optimum forest shrinkings, oriented toward roots, split into two groups according to whether their directed pairs decrease in their local orders. The original tail allocation on each group certifies eligibility in its respective system. At least one group has half the optimum weight. This gives two monotone permanent substitutions with feasible supports for the single union. For the two-union intersection, take the maximum of the four substitutions obtained by independently reversing either side. The same proof splits an optimum common set into four groups, one for each pair of directions. The one-permanent girth construction gives a stronger value guarantee, using scaling or repair. The ordered substitutions certify feasibility term by term before evaluation.

On an ordinary simple graph, each edge has only one possible slot after imposing the vertex order: its later endpoint. Hence the best ordered allocation is the max-plus formula
\[
   F_\prec(w)=\sum_v \max\bigl(\{0\}\cup\{w_{uv}:u\prec v,\ uv\in E(G)\}\bigr).
\]
The maximum of this formula and its reverse has \(O(|V|+|E(G)|)\) binary gates. If \(G\) is connected, nonnegative weights let any forest extend to a spanning tree without lowering its weight. Thus on \(K_n\) this is a size-\(O(n^2)\) factor-two approximation to the maximum spanning-tree value on all nonnegative real inputs. Any finite-factor binary circuit needs at least \(\binom n2-1\) binary gates: every edge variable must reach the output, witnessed by making just that edge positive, and a connected fan-in-two output cone with \(N\) different variable inputs needs at least \(N-1\) binary gates. This gives an affirmative answer to the maximization half of Jukna’s posted spanning-tree approximation question. [Jukna’s Problem 3](https://web.vu.lt/mif/s.jukna/tropical/problem-setA4.html)

For a complete bidirected host and a designated root, the same size and factor hold for a maximum in-arborescence. Exclude outgoing arcs from the root, and give each other vertex the choice of its best available outgoing arc to an earlier neighbor or zero. The selected arcs form a directed forest, with the designated root as its own component’s sink. Add one arc from each other component’s sink to the root. The initial forest was found by the two-order argument on the oriented arcs of an optimum in-arborescence. Reversing all arcs gives the out-arborescence version. Hertrich and Stargalla prove exponential scalar-tropical size for *exact* maximum directed spanning tree and exact bipartite perfect matching. The approximate directed formula above uses just max and addition. [Hertrich and Stargalla, *Tropical Circuits with Scalar Multiplication Gates*](https://arxiv.org/abs/2607.11540)

## Literature and verification scope

- Matchability to slots is the classical transversal-matroid construction, and endpoint allocation in a graph gives the classical bicircular matroid. The result here uses those objects to obtain a girth-dependent sandwich for **two unions**, with a simultaneous repair certificate preserving every selected coordinate with the same marginal. The classical weighted matroid algorithms already provide exact optimization on the respective independence problems. The guarantee concerns the restricted representation by a single permanent and a sparse extension. [Edmonds and Fulkerson, *Transversals and Matroid Partition*](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf) · [Matthews, *Bicircular Matroids*](https://doi.org/10.1093/qmath/28.2.213)
- Jukna and Seiwert’s exact spanning-tree and approximate pure-dynamic-programming lower bounds are the closest circuit results checked. The quadratic formula uses nonnegative maximization and allows returning the weight of a forest extendible to a spanning tree. The minimization half of the posted question is outside the theorem. The permanent statement gives formal supports and value approximations. It leaves coefficient-one generating polynomials and priority for the exact constructions to further checking. [Exact spanning-tree lower bounds](https://eccc.weizmann.ac.il/report/2018/049/) · [Approximation limitations](https://doi.org/10.1137/18M1196339)
- The discovery source was the project module TropicalMatrixAlgebra_20260908, whose sign-free permutation formula and extended-real assignment convention supplied the oracle representation. The argument here proves its needed assignment facts directly and uses none of that module’s axiomatic entries. The proof is a self-contained mathematical argument with no Lean kernel receipt. OptimizationBridge.py independently enumerates 256 permanent supports, 29,160 graph weight cases, 972 hypergraph weight cases, and 729 spanning-tree weight cases. Its overlapping-cycle control has a unique optimum repair deleting one shared edge of weight 3, while the separate lightest-edge deletions cost 4.

