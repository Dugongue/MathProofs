# Eight answers in tensor isomorphism and invariant theory

The catalog IDs refer to [Grochow Open Problems](https://github.com/Dugongue/MathProofs/tree/main/GrochowOpenProblems). Claims are tied to the field, input, action, and resource measure shown here.

| Problem | Answer | Proof |
|---|---|---|
| GP153 · Published PC+INV tensor-isomorphism conjecture | False under unrestricted polynomial substitution. The exact worst-case proof-line degree is 3 over every field, for geometric infeasibility. | [Inversion rule](inversion.md) |
| GP154 · Modular counting in PC+INV | The proposed growing degree bound is false. The systems have degree at most 2, sharp for \(n\ge q+1\) and \(q\nmid n\). | [Inversion rule](inversion.md) |
| GP013 · Binary matrix-tuple isometry | Deterministic polynomial-time search for ordered symmetric tuples, including degenerate tuples. | [Binary and mixed-characteristic isometry](structures.md) |
| GP014 · Binary quadratic-tuple isometry | Deterministic polynomial-time search for all ordered tuples via an exact compiler to symmetric matrix tuples modulo 4. | [Binary and mixed-characteristic isometry](structures.md) |
| GP015 · Odd-residue local principal ideal rings | Deterministic bit-polynomial decision for ordered isometry, uniform in the residue prime, in the stated explicit ring models. | [Odd-residue isometry](odd-rings.md) |
| GP066 · Single-tensor null-cone equations | An explicit \(0/1\) tensor forces degree at least \(n2^{n-1}\) for set-theoretic invariant equations over \(\mathbb C\). | [Single-object degree bounds](null-cone.md) |
| GP067 · Single-cubic null-cone equations | An explicit coefficient-one cubic forces degree at least \(n2^{n-1}/3\) in the same sense. | [Single-object degree bounds](null-cone.md) |
| Grochow–Qiao · Appendix A | Exact degree raising over every field. The direct construction adds four variables for source degree at least four and \(O(n)\) variables for source degree three. Degrees one and two use separate reductions. | [Degree raising](forms.md) · [Bare-map audit](appendix-audit.md) |

The two null-cone results establish the exponential **lower-bound** side. Matching upper bounds of \(2^{O(n)}\) are outside the results. The tensor argument relates to an earlier free-support construction of Kravtsov reproduced by Franks–Reichenbach, and the cubic uses the classical chain support. Priority for the specific invariant-degree consequences is unestablished.

The original Appendix A formula is fully classified by its effect on scalar powers. Over \(\mathbb R\), negating the added variable identifies the lifted \(x^4\) and \(-x^4\) for target degree 5. The marked reduction removes this ambiguity. The [companion audit](appendix-audit.md) also gives a functor on all covariant tensor homomorphisms for one tensor-to-algebra reduction, a separate clause of Grochow–Qiao's functoriality question.

## Verification

Lean independently checked the [matrix identity used by the inversion rule](InversionIdealConsequence.lean), including a bridge to its separately fixed statement and an axiom audit. [Verification record](Verification.json). The proof-system consequences, isometry algorithms, invariant arguments, and degree-raising reductions are paper proofs. The PC+INV result concerns the degree of proof lines and leaves the complexity of finding and encoding the substitution certificates open.
