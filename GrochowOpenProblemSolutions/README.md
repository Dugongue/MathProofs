# Six answers from the Grochow open-problem catalog

Written proofs and finite replays, 20 November 2026. This status update uses the [catalog's stable problem IDs](../GrochowOpenProblems/README.md).

| ID | Answer | Proof |
| --- | --- | --- |
| GP030 | Recognize simplicity of Cayley-table groups in uniform FOLL. The same circuits compute all minimal normal subgroups and the socle. | [Group algorithms](CAYLEY-TABLE-ALGORITHMS.md#gp030-simplicity-minimal-normal-subgroups-and-the-socle-in-foll) |
| GP049 | Decide epimorphism from an arbitrary Cayley-table source onto a Fitting-free target in uniform AC³. Find a witness and count all epimorphisms in deterministic polynomial time. | [Group algorithms](CAYLEY-TABLE-ALGORITHMS.md#gp049-epimorphisms-to-a-fitting-free-target) |
| GP101 | Prove the sharp upper bound $\lceil p/\lceil m/2\rceil\rceil$ on degrees of polynomial generators of prime-cyclic rational invariant fields with $m$ distinct nontrivial characters. | [Cyclic invariants](CYCLIC-INVARIANTS.md) |
| GP139 | Restriction and degeneration have the same limiting GHZ assistance rate per edge on complete uniform tensor networks, including Christandl's subexponential allowance. | [Tensor networks](TENSOR-NETWORKS.md) |
| GP177 | Refute exact determinant extraction of the requested order in polynomial-size, bounded-depth, division-free oracle circuits in fixed positive characteristic. | [Ideal extraction](IDEAL-EXTRACTION.md#gp177--a-fixed-characteristic-counterexample) |
| GP178 | Reduce the determinant of order $\Theta(r^{1/3})$ exactly to any nonzero polynomial of degree $d$ in the symmetric $r$-minor ideal in characteristic zero, using constant depth and size polynomial in matrix dimension and $d$. | [Ideal extraction](IDEAL-EXTRACTION.md#gp178--symmetric-determinantal-ideals) |

## Verification

The six conclusions are written proofs. A fresh Lean 4.33.0 run checked [three supporting matrix and ideal lemmas](IdealTransfers.lean), and a second run checked the fixed Frobenius statement independently. The [axiom audit](IdealTransfersAudit.json) records the exact checked source hash and Mathlib revision.

- [Group replay](check_group_foll.py) checks ten Cayley tables through order 240 against independent normal-subgroup and derived-series enumeration.
- [Invariant replay](check_invariants.py) checks integer lattice indices on 70,735 exhaustive supports, 650 sampled supports, and 223 sharpness controls.
- [Tensor replay](check_tensor_packings.py) checks complete and multipartite hypergraph packings and synchronous interpolation on overlapping tensor networks.
- [Ideal replay](check_ideal_transfers.py) checks 20,195 matrix cases and 108 nested oracle replacements in quotient rings.

GP139 uses GHZ dimension subexponential in the number of edges. GP177 concerns formal polynomial equality and leaves Frobenius-power extraction available. The papers that posed the questions and the earlier theorems used in the proofs are linked in the individual notes.
