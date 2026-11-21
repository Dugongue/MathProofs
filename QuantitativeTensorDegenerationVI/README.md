# Quantitative tensor degeneration VI

Four written proofs give a sharp catalyst-size tradeoff, complexity bounds for finding optimal witnesses, an exact diagonal-order classification, and exponential cubic complexity in characteristic two.

| Proof | Result |
| --- | --- |
| [Catalyst size and order](CatalystTradeoff.md) | For an explicit sparse family of side \(N_m=\Theta(m)\), catalysts of dimension at most \(N_m^{s-1}\) give best order \(\Theta(s(2^{m/s}-1))\). For the common-type thin profile class, catalytic order \(P\) implies unamplified order at most \(2^P-1\). |
| [Witness circuits and optimization](WitnessCircuits.md) | A feasible thin degeneration has a compact witness and a uniform coefficient circuit computable in polynomial time. Deciding a fixed pole budget is NP-complete, and optimal witness generation is tractable when the number of integral cochain coordinates is fixed. |
| [Exact multiplication pencil orders](PencilClassification.md) | For regular semisimple pencils of Hilbert function \((1,e,2)\) over algebraically closed fields of characteristic different from two, the diagonal-source order is \(2\) exactly when repeated eigen-directions number at most the simple ones plus \(3\). It is \(3\) otherwise. These orders add under tensor products. |
| [Characteristic-two cubics and alternating forms](CharacteristicTwoCubics.md) | Explicit sparse cubics and their alternating polarizations have degree-one geometric orbit arcs requiring exponential ramification in characteristic two. Every same-parameter Laurent lift of a polynomial image arc has exponential image degree. |

Local prerequisites reproduce the sparse, contact, power, catalyst, and cubic proofs used in this release. The multiplication pencil result uses diagonal rank sources. The other theorems compare the indicated relative sources. [Grochow–Mulmuley–Qiao](https://arxiv.org/abs/1605.02815) · [Bläser–Lysikov](https://arxiv.org/abs/1606.04253)

Lean independently checks [three supporting statements](CharacteristicTwoCubic.lean) for characteristic-two recovery. The [receipt](CharacteristicTwoCubicAudit.json) records the source hash, toolchain and transitive axioms. The four main results are written proofs. Publication priority remains unverified.
