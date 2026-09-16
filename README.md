Lean proofs obtained and formalized with use of AI models, namely some combination of Claude Opus 5, Claude Fable 5/5.1, GPT-5.6 Sol and GPT-6 Astra.
I've tried to assert the novelty of these proofs: all are pending comprehensive human validation and formal writeups.

-------------------------------------------

PolujanPottV1.lean - An affirmative answer to Polujan-Pott (2021) Open Problem V.1: "Can two vectorial bent functions have isomorphic graph translation designs without being EA-equivalent?"

Polujan365.lean - An affirmative answer to Polujan’s (2021) Open Problem 3.65: “For every even \(n\), are two vectorial bent functions EA-equivalent exactly when their vanishing-flat designs are isomorphic?” Here it is proved that vanishing-flat design isomorphism is equivalent to EA-equivalence for all vectorial bent functions in the admissible Nyberg range.

BentAffineOrbit.lean - An affirmative answer to Kudin, Pasalic, Polujan, and Zhang’s (2025) Open Problem 2: “Can one construct EA-inequivalent bent concatenations outside the completed Maiorana–McFarland class using affine rearrangements of one fixed seed?”; here an explicit pair is formally verified in every even dimension N ≥ 8, with distinct linearity indices N/2 − 2 and N/2 − 1, together with an exact rank formula for concatenations from rigid seeds.

BentDesignRank.lean - A refutation of Hyun, Kwon, Wang, and Wu’s (2026) Open Problem 7: “Do the designs D_{g,h} and TD_h in Theorem 10 always have equal binary ranks?”; here an explicit eight-variable counterexample is formally verified in Lean, satisfying every bent-function and duality hypothesis, with binary ranks 29 and 30 respectively.

TIEqTISp.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)'s Open Question 8: "Which, if any, of TI_O, TI_U, TI_Sp are equal to TI?"; here it is proved that TI = TI_Sp.

TIParStandalone.lean - Resolves the maximal-parabolic case of Chen, Grochow, Qiao, Tang, and Zhang’s (2024) research direction in §1.5: “What are the tensor-isomorphism complexity classes associated with other matrix groups, including parabolic subgroups?”; here TI = TI_Par is proved for the maximal parabolic family P_(n,n) over every field, under coordinate-projection reductions with polynomial output-size bounds. This addresses an explicitly proposed research direction, rather than a numbered open question.

FormTI.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)’s Open Question 1.11: “What is the complexity of tensor isomorphism restricted to other form-preserving groups, including mixed orthogonal groups and groups preserving forms that are neither symmetric nor skew-symmetric?”; here TI-completeness is proved for seven form-isometry families, including O(n,n), O(3n,n), and families preserving nonsymmetric or degenerate bilinear forms, under coordinate-projection reductions with polynomial output-size bounds.

FangCounterexample.lean - A refutation of Fang’s (2017) Conjecture 2.9: “Does identical collapse tomography at every vertex imply that a graph is vertex-transitive?”; here a ten-vertex counterexample is formally verified in Lean. The classical Tutte 12-cage also refutes the conjecture, as noted in the file; priority for the explicit refutation remains unverified.

CFR525.lean - An affirmative answer to the CFR(5,25) open instance listed by Rosin’s CPro1 (2025), originating from the Handbook of Combinatorial Designs, §VI.62: “Does a 5 × 25 circular Florentine rectangle exist?” Here an explicit witness is formally verified in Lean, proving F_c(25) ≥ 5. This resolves the existence instance, not the exact value of F_c(25).

-------------------------------------------

Pending formalizations:
* Chizewer, Everett, Mithal, and Qiao (2026) [https://arxiv.org/html/2603.27128v1] — Open Problem 4: “Can average-case polynomial-time algorithms be devised for tensor orthogonal and unitary isomorphism over finite fields?”; also Li, Li, Qiao, Tao, and Wang (2026) [https://arxiv.org/html/2604.00591v1] — Problem 1.8: “Can average-case polynomial-time algorithms be devised for 3-tensor isomorphism over finite fields under orthogonal and unitary group actions?” — Here answered affirmatively for cubical tensors under the standard matrix-isometry actions.
