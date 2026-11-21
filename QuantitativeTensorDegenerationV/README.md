# Quantitative tensor degeneration V

Four written proofs give exact diagonal orders, optimal algebra catalysts, sharp terminal-cap clearing bounds, and a quantitative transfer to cubic forms.

| Proof | Result |
| --- | --- |
| [Diagonal orders in every characteristic](DiagonalGrowth.md) | The displayed mixed-parameter family has diagonal-source order \(3r\), Loewy degree \(2r\), and minimal border rank \(11^r\). The construction works over every field with a parameter outside \(\{0,1\}\), including every algebraically closed field. |
| [Optimal algebra catalysts](OptimalCatalysts.md) | Shortest paths on thin Peirce profiles and a matching formula give the exact cap threshold over all finite-dimensional unital associative algebra catalysts for the stated types. One intermediate algebra gives examples with exponentially smaller optimal order and arbitrarily large improvement ratios. |
| [Terminal-cap pole and clearing orders](TerminalOrders.md) | With \(d=2^{m-1}\), the fiber contacts are positive multiples of \(d\) and their sum \(C\) gives exact total cap \(\lceil C/2\rceil\). Fixed coordinate arcs have exact ramification and prime-by-prime polynomial clearing criteria. |
| [Sparse cubic degenerations](SparseCubicDegenerations.md) | Over fields of characteristic different from two, including characteristic three, explicit sparse cubics have exact power and ramification conditions and exponential same-field Laurent complexity under arbitrary linear substitutions. |

The [sparse seed](SparseSeed.md), [contact-lattice construction](ContactSeed.md), [power extraction](PowerSeed.md), [cycle-mean formula](PowerOrderSeed.md), [initial-cap orders](ExactSparseOrders.md), [nonsemisimple catalyst reduction](CatalystSeed.md), [universal single-deletion cancellation](UniversalCatalystCancellation.md), and [adjoint-block calculation](AdjointSeed.md) are included as prerequisites.

Lean independently checks [three supporting statements](CubicRecovery.lean) for Hessian kernels and symmetric adjoint blocks. The [audit](CubicRecoveryAudit.json) records the checked source hash, Lean and Mathlib versions, and transitive axioms. The four main results are written proofs. Publication priority remains unverified.
