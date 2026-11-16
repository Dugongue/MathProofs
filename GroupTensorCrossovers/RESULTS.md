# Four crossovers in group and tensor isomorphism

These manuscripts contain AI-assisted informal proofs. The statements distinguish exact literature questions from new algorithmic bounds and reductions. Publication priority for the new proofs has not been established.

| Result | Exact conclusion |
| --- | --- |
| [Chief and composition series in FOLL](groups.md) | Polynomial-size Boolean circuits of depth $O(\log\log n)$ construct both series on raw Cayley tables of arbitrary finite groups. The same depth decides membership at every level of the alternating radical–socle tower. A conjugation-invariant generating set admits polynomial-logarithmic-length straight-line programs using at most seven registers. |
| [Transversals for permutation groups in NC](NCTransversal.md) | Answer to Levet's Question 8.2 under its polynomial-index promise. Reingold's traversal word can be generated independently of the permutations, then evaluated and deduplicated in parallel. Kantor–Luks–Mark announced an unrestricted-group extension earlier. This manuscript supplies an independent proof. |
| [Tensor isomorphism and derived equivalence](derived-dense.md) | An explicit polynomial-time reduction over every field to derived equivalence of split basic algebras with three simples and global dimension at most three, even sharing a Cartan matrix within each tensor format. A separate [quiver reduction](tensors.md) fixes the acyclic quiver and all quadratic relations, and varies only coefficients of cubic relations. |
| [Characteristic-two matrix tuple isometry](SquareZeroTupleIsometry.md) | Las Vegas polynomial-time decision when the Jacobson radical of the adjoint algebra squares to zero. The theorem allows arbitrary residue-field extensions and arbitrary first-order twists. |

The chief-series circuit selects its series using the input labels. The derived-equivalence result with a dense multiplication table and the directed-quiver result impose different hypotheses on the output algebra. The matrix-tuple theorem concerns ordered tuples and a square-zero adjoint radical.
