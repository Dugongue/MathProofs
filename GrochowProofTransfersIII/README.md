# Four proof transfers in tensor isomorphism, group isomorphism, and algebraic complexity

The four written proofs draw on methods from the pinned [Cinna Davis and GPT-6.2 Astra collection](https://github.com/1337isnot1337/solved-conjectures/tree/892c04046aadc8731dd510bb9c9b3ca1a086bae1). Each proof names the source technique and the mathematical literature it builds on.

| Result | What the proof establishes |
| --- | --- |
| [Tensor isomorphism universality](UNIVERSAL-TENSOR-ISOMORPHISM.md) | Answers Grochow–Qiao’s Open Question 7.4 for basis-explicit linear models. Arbitrary fixed mixed signatures reduce to ordinary 3-tensor isomorphism over the same field. The low-arity intermediate model preserves isomorphisms bijectively. |
| [Class-two group isomorphism](CLASS-TWO-GROUP-ISOMORPHISM.md) | Refines Sun’s algorithm to $N^{O((\log N)^{19/20}(1+\log\log N)^{1/10})}$ on Cayley tables, including 2-groups of arbitrary exponent. |
| [Modular symmetric IPS](MODULAR-SYMMETRIC-IPS.md) | The exact minimum degree in non-grid placeholders on a finite grid is determined by Sylow orbit sizes. For the Boolean pigeonhole system in characteristic $p>0$, it is the largest power of $p$ at most the number of pigeons. |
| [Border separators](TWO-SCALE-SEPARATORS.md) | A construction of triple-product sets of size at least $q^{n^2/3}$ in $U_n$ and $\mathrm{GL}_n(\mathbb R)$ with border-separating polynomial degree $O_n(q)$. It gives the exact minimum degree for the corresponding diagonal-torus grids. The result concerns the finite support and degree tradeoff. |

## Verification

The four notes contain the complete written arguments at their stated scopes. The accompanying receipts identify the supporting declarations checked in Lean 4.33.0 with [Mathlib db584cd6](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). The Python scripts replay exact finite controls. The full theorem arguments have written proofs, and publication priority and external review remain open.
