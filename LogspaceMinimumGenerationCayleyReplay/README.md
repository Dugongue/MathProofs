# Physical Cayley queries and ordinal generator replay

These Lean 4.33 files verify physical components of the logspace search proof for Collins–Grochow–Levet–Weiß Question 8.1. The question asks for an actual smallest generating set from an arbitrary finite group's Cayley table in deterministic logarithmic space. The unrestricted search theorem remains informal. [Question 8.1](https://arxiv.org/html/2402.00133#S8)

The physical matrix decoder subtracts the unary header offset and computes the two coordinates using bounded binary division subroutines. The side decoder identifies the two oriented labels for a cross-side query. A width-controlled tape sweep installs the narrow endpoint words. The live Cayley-table lookup computes the unique right quotient and hands the actual quotient register to the next predicate machine. This handoff retains the protected tape banks. [Division](Mathproof/MinimumGenerationCayleyQueryDispatchDivision.lean) · [Side and endpoint decoding](Mathproof/MinimumGenerationCayleyQueryDispatch.lean) · [Quotient handoff](Mathproof/MinimumGenerationOuterCayleyQuery.lean)

The physical replay controller clears the label cursor, calls the greedy scan, and decrements the requested ordinal on each accepted label. It returns the exact requested generator or the exhaustion sentinel. The raw-label specialization supplies the constant-eligibility callback. Its per-candidate prefix-subgroup test still requires a physical Reingold call. The addressed Reingold evaluator already gives the exact mathematical answer on the two-copy graph. [Replay](Mathproof/MinimumGenerationPhysicalGreedyTape.lean) · [Raw-label specialization](Mathproof/MinimumGenerationPhysicalGreedyRaw.lean) · [Two-copy query correctness](Mathproof/MinimumGenerationBipartiteRawQuery.lean)

A callback with a certified native execution can return its verdict through finite control with a uniform bound on every physical prefix. The suspended caller's banks and output are preserved. For subgroup connectivity over a whole greedy prefix, querying the same prefix of all eligible labels gives the same result. Individual ordinal queries still need replay. [Verdict adapter](Mathproof/MinimumGenerationVirtualVerdict.lean) · [Equivalent prefix queries](Mathproof/MinimumGenerationOuterGreedyCut.lean)

The remaining connectivity work is to install the complete physical address reader and connect it to a concrete finite Reingold machine with its termination and workspace proof. The included Berkowitz files verify component routines for rank and retain their separate grid-driver and arithmetic contracts.

## Build and attribution

Build with `lake build` on Lean 4.33. The included modules carry the attributions for the CSLib/Complexitylib frontier port, LeanCanny, OpenAI Problem 336, TrureTuring, and the selected Problem 1.8 modules adapted from Lax submissions 13 and 51. Their source and license notices are shipped with the bundle. [LeanCanny](https://github.com/edemaine/lean-canny/tree/af8d9dc4284a3e8724ef71bfc1de506baea23f08) · [OpenAI proof](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a) · [Apache 2.0 license](LICENSE-APACHE-2.0.txt)

[Native Reingold closure and attribution](REINGOLD-PORT.md)
