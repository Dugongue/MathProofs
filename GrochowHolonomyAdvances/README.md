# Four advances on tensor isomorphism from holonomy

The previous reduction recovered invertible matrix-line blocks and used short cycles with commuting semisimple holonomy. Four results extend its reach. The placements are editorial estimates against the existing Grochow top-30 briefing, based on proximity to the tensor questions, breadth, and strength of the algorithmic conclusion.

| Proposed band | Result | What advances |
|---|---|---|
| **11–16** | [Higher-dimensional field-multiple edge spaces](FieldTorsorBlocks.md) | The tensor's intrinsic stabilizers recover edge spaces of arbitrarily large dimension, each consisting of all finite-field multiples of an invertible map. The stated class is GI-complete. A GI oracle also counts **all** tensor isomorphisms, including maps that move the recovered blocks and maps on a nontrivial contraction kernel. The proof includes a 64,800-automorphism check on a small example. |
| **12–17** | [Noncommutative semisimple holonomy](NoncommutativeHolonomy.md) | Reduced traces and determinant–norm normalization recover unknown support alignments through a graph encoding. Matrix factor sizes, residue field degrees, factor counts and module multiplicities can grow. A genuinely noncommutative subclass is GI-hard. The upper reduction uses a bounded-eccentricity root, a bounded word-span length, and a bounded number of factors for scalar normalization. |
| **14–19** | [Commuting holonomy with nilpotent radicals](RadicalHolonomy.md) | The graph reduction allows unbounded nilpotency depth and arbitrary represented modules when the local dimensions of $J/J^2$ are bounded and an equivariant cycle list is available as specified. With the support alignment supplied, it tests all commuting holonomy in polynomial expected time. The comparison of extended charts assembles an actual transporter. |
| **15–21** | [Unbounded cycle length and a cactus GI-completeness theorem](CycleRankHolonomy.md) | A bound on cycle rank per biconnected block replaces the short-cycle requirement over arbitrary finite fields. Split holonomy over $\mathbb F_3$ already makes the problem GI-complete on long-cycle bouquets. A separate fixed-parameter algorithm in the total cycle rank handles semisimple holonomy, including the noncommutative case, without a GI oracle. |

I would lead with the higher-dimensional edge theorem for its exact counting result, followed by the noncommutative theorem for the extension to full matrix factors. The cactus result is a useful companion because it shows that a simple support alone does not eliminate the isomorphism difficulty. The local radical theorem identifies a separate source of tractability even with deep nilpotence.

Three of the advances combine explicitly. The local chart argument for radicals can use the shared-base-field ratios for field-multiple edge spaces and the cycle list from bounded-rank biconnected blocks. This gives one class allowing larger edge spaces, nilpotent radicals and arbitrarily long cycles together. [Combined theorem](RadicalHolonomy.md#combining-higher-dimensional-edges-radicals-and-long-cycles)

## Verification

The four main results have mathematical proofs with the cited inputs and documented finite controls. The reproducible radical control tests every matrix in $\operatorname{GL}_3(2)$ across all 12 alignments of its small support, plus a five-dimensional local algebra. Run it with Python 3.10 or later.

    python -B check_radical_holonomy.py

The independent kernel and axiom audit of [ChartAgreement.lean](ChartAgreement.lean) verifies the auxiliary fact that one map agreeing on the marked algebra generators also agrees on every generated query. The audit uses propext, Classical.choice and Quot.sound. Priority for the combined results remains unverified.
