# Four results from the November Lean intake

The order below is our assessment of reach and relevance to Grochow's work.

| Rank | Result | What the intake contributed |
| ---: | --- | --- |
| 1 | [Polynomial-time canonization of Fitting-free Cayley tables](FittingFreeCanonization.md). An algorithm outputs a canonical multiplication table and a relabeling witness for every finite group with trivial solvable radical. | The CFSG and two-generation sources identify the simple-group facts used to canonicalize the socle. The logarithmic-degree outer action allows application of Wiebking's canonizer restricted to the allowed coordinate changes. |
| 2 | [VNP completeness for degree-nine negative 2-CNF prefixes in canonical IPS](CanonicalIPS.md). Over every field with more than two elements, the first-false-clause certificates are VNP-complete under p-projections even with a maximum-degree-nine negative binary prefix followed by contradictory units. Width-one certificates have explicit polynomial-size formulas. | CompPoly provides a formal polynomial substitution interface. The reduction uses signed cancellation in a bounded-degree graph, with every projection specified on the formal polynomial. |
| 3 | [Special-linear isomorphism for weighted cubic graph tensors](DeterminantResolvedGraphTensors.md). Exact decision and counting over finite fields take deterministic polynomial time. Each graph isomorphism leaves at most two nontrivial scalar power tests, and examples require both. The proof also gives an explicit GL-equivalent pair with distinct SL orbits. | The Hex Berlekamp and factorization certificate interfaces apply to the remaining prime-field witness equations. |
| 4 | [Symbolic subgraph circuits on weighted hosts of bounded cut rank](SubgraphCircuits.md). The circuit has linear host-size dependence at fixed pattern and rank, handles induced copies, and works on independent symbolic cut factors. | TNLean's graph contraction gives the boundary-index representation used for the merge. |

These are AI-assisted informal proofs. The group algorithm combines named published results with an explicit reduction, with publication priority undetermined. The IPS result strengthens the width restriction in the earlier result. The tensor theorem is for the stated connected, properly edge-coloured, four-cycle-free cubic family. The symbolic subgraph theorem assumes supplied cut factors.

The companion scripts passed 48 IPS coefficient checks, 408 cubic tensor count comparisons, and 144 subgraph recurrence checks. The Lean sources verify the two indicated algebraic identities with Lean 4.33.0 and Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, with transitive axioms in the standard Lean allowlist. The intake declarations cited in the proofs have source-level evidence.

- [Crossing-edge contraction expansion](CutContraction.lean)
- [Negative clause cancellation](NegativeClauseCancellation.lean)
