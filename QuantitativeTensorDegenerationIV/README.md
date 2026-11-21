# Quantitative tensor degeneration IV

Four written theorems give sharp diagonal orders, explicit pole costs, catalyst cancellation, and a transfer to two-step nilpotent Lie algebras. All Laurent valuations use the indicated uniformizer.

| Proof | Result |
| --- | --- |
| [Growing diagonal-source gap](DiagonalGrowth.md) | An explicit family of dimension \(11^r\) has diagonal-source order \(3r\) and Loewy degree \(2r\) over every algebraically closed field of characteristic two. The proof gives a mixed-factor additivity criterion using Frobenius twists. |
| [Exact powers and contacts](ExactSparseOrders.md) | The exact least order is \(\lceil r/2\rceil\) for the cap alone and \(\lceil r2^{m-1}/3\rceil\) for the telescope with \(m\ge2\). Monomial witnesses attain the least order with normalized image degree \(r\). Prescribed positive contacts have an explicit sharp budget as well. |
| [Unrestricted algebra catalysts](UniversalCatalystCancellation.md) | Every nonzero finite-dimensional unital associative algebra catalyst preserves the entire three-mode forward-pole region of every displayed sparse power, even when the basis changes mix catalyst and sparse coordinates. The original tensors require no padding. |
| [Two-step nilpotent Lie laws](TwoStepLieDegenerations.md) | Explicit sparse laws in every characteristic require exponential ramification to lift a degree-one geometric orbit arc. Every polynomial image arc with a Laurent lift over the original Laurent field has exponential degree, and the least symmetric pole depth is exponential. |

The [sparse seed](SparseSeed.md), [power extraction](PowerSeed.md), [power optimization precursor](PowerOrderSeed.md), [earlier catalyst proof](CatalystSeed.md), and [contact lattices](ContactSeed.md) are included as prerequisites. The diagonal theorem uses the rank-\(n\) diagonal tensor. The other comparisons use their specified sparse relative sources. [Bläser–Lysikov](https://arxiv.org/abs/1606.04253) · [Ganesh–Koiran–Oliveira](https://arxiv.org/abs/2608.10179) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)

Lean independently certifies [three adjoint-slot identities](HeisenbergAdjoint.lean). The [receipt](HeisenbergAdjointAudit.json) lists the verified source hash, toolchain, and transitive axioms. The main results are written proofs. Publication priority remains unverified.
