# Minimum group generation in deterministic logspace

This Lean 4.33 bundle contains verified components of the informal answer to Collins–Grochow–Levet–Weiß Question 8.1. The unrestricted search claim is stated as `Mathproof.MinimumGeneration.CayleyMinimumGeneratorSearch` in a finite-control model with read-only input and write-only output. The existence of a machine satisfying that claim remains to be proved in Lean. [Question 8.1](https://arxiv.org/html/2402.00133#S8)

| Module | Checked content |
|---|---|
| `MinimumGenerationProblem` | Binary table and generator encodings, finite-control transducer semantics, an append-only output law, and existence of an abstract minimum generating list. |
| `MinimumGenerationCayley` | A Cayley edge gives an actual signed generator, and reachable vertices from the identity are precisely the generated subgroup. |
| `MinimumGenerationChief` | A strict normal-closure scan step has no intermediate normal subgroup under the prefix invariant. A proper supplement meets an abelian minimal normal subgroup trivially. |
| `MinimumGenerationGaschutz` | The reused finite Gaschütz theorem and its application to a prescribed quotient generating tuple. |
| `MinimumGenerationRadical` | Frattini subgroups of normal subgroups lie in the ambient Frattini subgroup. Quotienting by such a kernel reflects generation. |
| `MinimumGenerationAbelianLift` | The section boundary is linear. Split parameters form a submodule, and the row-independence criterion is expressed modulo the image of evaluated derivations. |
| `MinimumGenerationResidual` | Solvable and semisimple residuals, exact quotient criteria, perfect normal generation by one element, and the faithful socle action used for the order bound. |
| `MinimumGenerationTowerReplay` | Executable ordinal replay, termination and correctness against the supplied residual lists, bounds on the controller's encoded register width, and shrink bounds for the two quotient towers. |
| `MinimumGenerationSemisimple` | Signed Schreier stabilizer loops, factorization through stabilizer quotients, diagonal tests for products of simple groups, and a finite selector for sufficient distinct orbit keys. |
| `MinimumGenerationSpaceAccounting` | The aggregate width of kernel labels is at most the logarithm of the original order, with a separate bound for per-frame index overhead. |

The remaining connections include production of the residual lists from the raw Cayley input in a bounded machine, the finite-field rank and minimum-generator-number algorithms, the full abelian and nonabelian lift execution, and an end-to-end workspace audit for the single machine. The matching Reingold decision proof in Complexitylib targets Lean 4.36 and is outside this bundle. [Complexitylib](https://github.com/cslib-community/complexitylib)

Run `lake build` from the bundle directory with Lean 4.33.0 to build the modules. The Gaschütz proof is reused from the TrureTuring snapshot identified in its source header. Its Apache 2.0 license is included. The bundle also includes the two MathProofs multitape support modules used by the statement.
