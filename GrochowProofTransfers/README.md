# Four proof transfers for Grochow-style isomorphism problems

These results use local packing bounds, translation characters, cycle normalization and incidence records from the pinned [Cinna Davis and GPT-6.2 Astra collection](https://github.com/1337isnot1337/solved-conjectures/tree/892c04046aadc8731dd510bb9c9b3ca1a086bae1). The ambient problems come from [Grochow and Qiao’s tensor-isomorphism program](https://arxiv.org/abs/1907.00309) and related questions on additive codes, alternating maps and matrix pencils. Each result settles a stated family. The general tensor isomorphism and general additive-code questions remain open.

| Result | Scope |
| --- | --- |
| [Cubic graph tensors](CUBIC-TENSORS.md) | Four-cycle-free, properly three-edge-coloured cubic graphs over any field. Rank-two contractions recover all three frames. The resulting reduction to coloured graph isomorphism and scalar tests gives polynomial-time decision over finite fields and counts every lift. |
| [Additive codes](ADDITIVE-CODES.txt) | A sufficient condition beyond MDS for equivalence to force additive equivalence, including singular blocks. A separate coordinate-kernel criterion covers an explicit family with no systematic information set. Invertible systematic blocks also admit a cycle-based classification of all fixed-coordinate witnesses. |
| [Cyclic packing groups](CYCLIC-PACKING.txt) | Exact counts and normal forms for maximum abelian subgroups in graphical class-two groups from four-point cyclic packings. In the odd-step family the subgroup count is the sharp hole period, and the maximum subgroups recover the pseudo-isometries. |
| [Split linear matrix pencils](HYPERPLANE-CRITERION.txt) | Exact hyperplane and intersection nullity conditions force a fixed simultaneous diagonal form. Finite rank tests recover the decomposition and the change-of-basis maps. |

## Verification

The text files give complete written arguments for their stated families. The Lean files cover the scoped claims in their statements. The appendix receipts bind their source bytes to Lean 4.33.0 checks and transitive axiom audits. The Mathlib revision was [db584cd6](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). The Python scripts replay exact finite controls. Related prior results and the upstream proof methods are credited in each note. Priority for the new family-level conclusions remains provisional.

To run the finite controls, use Python 3.10 or newer with assertions enabled. Each script documents its own scope.
