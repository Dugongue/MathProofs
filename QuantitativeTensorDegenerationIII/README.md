# Quantitative tensor degeneration III

Four written proofs extend the conductor, sparse-power, and contact-lattice constructions.

| Proof | Result |
| --- | --- |
| [Diagonal orders](DiagonalOrders.md) | An explicit 11-dimensional algebra in characteristic two has diagonal-source order \(3\) and Loewy degree \(2\). Its tensor powers still exceed the Loewy bound for the stated parameter. The order of every monomial local algebra is computed over any field, including an exact \(q\)-dependent formula over \(\mathbb F_q\). |
| [Exact power orders](ExactPowerOrders.md) | A finite cycle-mean optimization on the base graph gives an exact order \(\lceil r\lambda_m\rceil\) for the \(r\)-th tensor power and determines the full forward pole-cap region. The explicit \(m=1\) example has order \(\lceil r/2\rceil\). |
| [Catalyst cancellation](CatalystCancellation.md) | Every fixed finite-dimensional unital associative catalyst cancels on sufficiently large members of the sparse family. At any starting size, appending at most \(\lfloor\log_2\dim B\rfloor\) vertices preserves the full pole-cap region and permits exact cancellation of the prescribed catalyst \(B\). |
| [Sparse Lie degenerations](SparseLieDegenerations.md) | Sparse solvable Lie laws in every characteristic realize the contact lattices. A degree-one geometric orbit arc requires exponential ramification, and every polynomial image arc lifting over the original Laurent field has exponential degree. |

The [sparse seed](SparseSeed.md), [power extraction proof](PowerSeed.md), and [contact-lattice proof](ContactSeed.md) are included as prerequisites. Diagonal order uses a fixed diagonal rank source. The power, catalyst, and Lie results use their specified relative sources. [Bläser–Lysikov](https://arxiv.org/abs/1606.04253) · [Ganesh–Koiran–Oliveira](https://arxiv.org/abs/2608.10179) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)

Lean independently checks [three supporting statements](QuantitativeLie.lean) about edge weights and the Vandermonde tag matrix. The [audit receipt](QuantitativeLieAudit.json) specifies the exact source hash, toolchain, and standard axioms. The main proofs are written. Publication priority remains open.
