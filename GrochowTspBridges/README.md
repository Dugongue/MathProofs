# Four TSP results from Grochow's combinatorial framework

The four routes extend earlier work on extended formulations, tensor stabilizers, graph covers, and graph edits. Each result has a mathematical proof and an explicit scope. Priority for the combinations remains unverified.

| Earlier method | TSP variant | Result |
|---|---|---|
| Grochow's Newton-polytope transfer and guarded assignment | Symmetric metric TSP and high-dimensional Euclidean TSP | For $\varepsilon_N\to0$, fixed shared LP relaxations for factor $1+\varepsilon_N$ need $2^{\Omega(\min\{N,1/\varepsilon_N\})}$ inequalities even for distances in $\{1,2\}$. A separate bounded-domain theorem compiles affine-guarded assignment leaves to one LP over a box of metrics. [Proof](MetricFormulations.md) |
| Grochow–Qiao tensor equivalence and gain switching | Asymmetric TSP on projective lifts | Recover a succinct lift from primitive tensor blocks, then combine assignment duality with a fixed-point test for a splice. A successful certificate proves a global optimum among all lifted tours, including tours with different choices on different sheets. [Proof](TensorLiftATSP.md) |
| Grochow–Tucker-Foltz covers and certified contraction | Rural Postman with prescribed binary holonomy | A metric inequality at each boundary limits an optimum to $2r - 2 + \rho$ crossings across $r$ flat mandatory regions, where $\rho$ is the quotient cycle-voltage rank. The proof gives a bounded additive loss when the inequality has slack, and a $T$-join completion algorithm. [Proof](FlatPatchRuralPostman.md) |
| Shared boundaries in the Grochow–Urisman graph edit route | Graphical TSP, path TSP, subset TSP and prize-collecting walks | Compress a tree under sparse shortcut edits to a table of size linear in the number of anchor vertices. In the all-cities case $h$ shortcuts give at most $2^h$ parity choices followed by minimum spanning trees, with fast repeat queries even when the anchors change. [Proof](ShortcutTreeTSP.md) |

The metric lower bound concerns a single projected relaxation shared across cost objectives. The other routes give exact algorithms or certificates under their stated structural hypotheses. The large-dimension Euclidean construction uses distance-vector objectives. The semidefinite corollary in the metric note explicitly depends on a shifted-matching preprint theorem.

## Reproducible checks

Run the controls from this directory with Python 3.10 or later.

    python -B check_shortcuts.py
    python -B check_tsp_controls.py

The shortcut control compares 229 closed and 131 open queries with an independent shortest-path and Held–Karp computation. The second control checks single and replicated metric matching hosts, 528 squared Euclidean distances, both 24-vertex lifted ATSP instances, and the exact Rural Postman fixtures. The files explain the proofs and comparisons with the primary literature.

[PathParity.lean](PathParity.lean) formalizes the auxiliary fact that even internal degrees force a common parity of path-edge multiplicities. Its independent Lean kernel and transitive-axiom audit passed with propext and Quot.sound. The four main results have informal proofs.
