# Four algorithmic results on pencils, groups, channels, and designs

Four independent informal research tracks build on earlier results in MathProofs. Each proof states its hypotheses and includes a small reproducible control. Priority has not been established for the new formulations.

| # | Result | Scope |
| --- | --- | --- |
| 1 | [Rational binary-pencil isomorphism](PENCILS.md) | Deterministic polynomial-bit-time transporters for ordinary TI on every rational two-slice pencil and for determinant-one TI on every split rational two-slice pencil, including rectangular and singular inputs. The general determinant-one decision reduces to explicit weighted number-field norm tests. |
| 2 | [Group Weisfeiler–Leman and rank-metric graphs](GROUP-WL.md) | Stable 3-dimensional Version II group refinement detects full rank histograms of center cosets and separates explicit outputs of the earlier tensor-to-group construction. An intrinsic quotient graph recovers the underlying rank-metric code up to equivalence when its minimum distance is at least four. |
| 3 | [Noise-robust recovery of isospectral Choi matrices](QUANTUM.md) | Nonisomorphic graph encodings have local-unitary orbit separation of order at least $n^{-6}$. At a smaller inverse-polynomial noise tolerance, deterministic polynomial-bit-time reconstruction recovers the graph from an explicit noisy matrix in unknown local bases. |
| 4 | [Vectorial bent functions from unlabeled designs](DESIGN.md) | Deterministic polynomial-time recognition and reconstruction from a block list. For a given vectorial bent function and a specified subdesign, the algorithm decides whether added coordinates realize the subdesign and returns such coordinates on acceptance. In the 16-point case all six Steiner subdesigns are realizable. |

The design algorithm is directly runnable on explicit block lists. The pencil implementation handles the one- and two-rational-root square regular branch and checks the returned transporters exactly. The group compiler outputs cospectral implicit graphs with polynomial-time adjacency and potentially exponentially many vertices. Their isomorphism relation exactly reflects fixed-prime-field TI. The quantum result uses an explicitly given Choi matrix.

The proofs are informal. The design result addresses the realization of a supplied subdesign in the setting of Meidl–Polujan–Pott’s problem. The earlier counterexample to universal realization is credited in the proof. The work here gives no general search algorithm for an appropriate subdesign and claims no closure of unrestricted tensor isomorphism versus determinant-one tensor isomorphism. [Meidl–Polujan–Pott](https://arxiv.org/abs/2012.06866)
