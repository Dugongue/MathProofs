# Four bridges from combinatorial algorithms to Grochow's work

Four workers examined graph counting, algebraic isomorphism, combinatorial optimization, and constraint satisfaction. Each bridge turns existing machinery into a sufficient theorem with an explicit construction. The proofs establish the claims in their stated models. Publication priority remains unverified.

| Bridge | What follows from the sufficient conditions | Where it changes the algorithm |
|---|---|---|
| [Guarded optimizers and permanent oracles](GuardedOptimization.md) | Monotone arithmetic circuits with permanent oracle gates yield extended formulations of their Newton polytopes. This gives exponential charged size for Hamiltonian-cycle, perfect-matching, and cut polynomials at every depth, in the formal support model stated in the proof. A second theorem compiles finite affine decision trees whose leaves are assignment or max-plus optimizers. | Use an assignment solver inside a reduction when the objective structure permits it. The theorem gives a quantitative bound on how much the finite branch structure and leaf solvers must cost when the target has a hard polytope. |
| [Tensor blocks and gain graphs](TensorBlocks.md) | Compute one-sided stabilizer algebras and primitive idempotents. Bounded recovered blocks reduce tensor equivalence to Graph Isomorphism, with a fixed-parameter algorithm for bounded support treewidth. Forest supports of invertible matrix lines admit a polynomial algorithm even for unbounded block dimensions. | Replace a search over all ambient bases by a graph matching and consistent local linear maps. On forests, a root choice propagates all gains. |
| [Cuts that certify cover contraction](CoverContraction.md) | Trivial holonomy and saturating anchor flows suffice to contract a weighted Unique Games instance exactly. A signed-parity condition gives a one-min-cut formula for the sharp worst-case loss of the specific rounding map. | Use synchronization or partition heuristics to propose regions, check a flow, and solve the smaller quotient. A positive loss bound still lifts a valid optimum interval. |
| [Graph-edit decks and symmetric circuits](GraphEditDecks.md) | A joint profile of treewidth-$t$ graph homomorphism scores after edits supported on $r$ ordered vertices is determined by $(t + r)$-WL. An explicit square-symmetric arithmetic circuit computes an exact multiset encoding. A one-vertex-deletion example attains the extra dimension at $t = 1$. | Use cheap invariant moments to reject isomorphism or compute the whole profile for certified edit optimization. One shared anchor bag bounds the treewidth even for high-order joint moments. |

## Algorithm and complexity map

| Problem class | Method and the distinction that matters |
|---|---|
| Path and small-subgraph detection | Color-coding isolates injective witnesses. Tree-decomposition dynamic programming handles the colorful problem and perfect hash families replace random colors. |
| Exact subgraph and induced-motif counting | Convert to the homomorphism basis. The treewidth of the resulting support controls the relevant parameterized complexity. Matchings demonstrate the gap between detection and exact counting. |
| Graph reconstruction and isomorphism | Graph decks support polynomial invariants. The edit result works with a prescribed motif profile of each card and supplies an explicit WL budget for the joint distribution. |
| Subgraph learning | Node-marked and node-deleted views motivate edit panels. WL expressivity bounds and exact invariant moments give a reference point for approximate learned profiles. |
| Group, algebra, and tensor isomorphism | Grochow–Qiao reductions carry complexity and algorithmic consequences across the problems. Intrinsic primitive-block rank gives a tractable parameter in the tensor promise classes treated here. |
| Hamming and rank-metric code equivalence | Support splitting can guide search; one-sided stabilizer algebras supply exact algebraic data. Basis-compatibility relations retain the two-sided constraints. |
| Gain-graph switching | A spanning tree transports switches. Fundamental cycles impose a simultaneous conjugacy condition. In the forest case every aligned support is feasible. |
| Assignment and general matching | Assignment has a compact polytope. General matching has a polynomial algorithm and exponential extension complexity. The gap limits both permanent-oracle polynomials and the guarded assignment model via different reductions. |
| Hamiltonian cycles, cuts, and metric TSP | Newton polytopes transfer formal support complexity. Objective recession cones also transfer exact metric TSP lower bounds in the guarded optimization model. |
| Independent sets and knapsack | Stable-set extension lower bounds apply to the guarded model on appropriate graphs. Capacity-indexed knapsack dynamic programming is a positive example at pseudopolynomial size. |
| Unique Games and signed Ising | Label transport makes trivial patches internally uniform. Anchor-flow certificates and one-cut loss evaluation apply under explicit hypotheses, while expansion-based algorithms and persistency methods address complementary promises. |
| Synchronization and cohomology decoding | Holonomy checks all sheets of the cover. Abelian label shifts turn a weighted disagreement objective into support minimization in a coboundary coset. |

The four arguments use different kinds of local data. On tensor support trees, local witnesses propagate to a global isomorphism. In graph covers, capacity is sufficient to replace local labels by one representative. In edit decks, repeated factors share anchors so higher moments retain bounded width. In guarded optimization, unbounded objective directions let compact local formulations recover a common global support function. Each theorem identifies a checkable condition under which a familiar heuristic can be replaced by a certificate or an exact algorithm.

## Verification

The four main results have written mathematical proofs. [check_controls.py](check_controls.py) independently checks small examples using only the Python standard library. It checks two pairs of graph edit decks, projective switching on a tree and its four-cycle completion, a piecewise affine guarded objective, a nested permanent oracle, and all 224 binary and ternary cross-permutation choices in the cover fixture. Run it with Python 3.10 or later. The finite checks are examples of the stated mechanisms.

[EditDeckEncoding.lean](EditDeckEncoding.lean) checks the auxiliary algebraic step that a product of linear root factors determines the multiset, including multiplicities. It imports Mathlib. The kernel and transitive axiom audit admitted the standard axioms propext, Classical.choice, and Quot.sound. This auxiliary result is the extent of the Lean coverage.
