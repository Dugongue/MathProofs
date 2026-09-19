Lean proofs obtained and formalized with use of AI models, namely some combination of Claude Opus 5, Claude Fable 5/5.1, GPT-5.6 Sol and GPT-6 Astra.
I've tried to assert the novelty of these proofs: all are pending comprehensive human validation and formal writeups.

-------------------------------------------

PolujanPottV1.lean - An affirmative answer to Polujan-Pott (2021) Open Problem V.1 / Polujan's (2021) Open Problem 3.64: "Can two vectorial bent functions have isomorphic graph translation designs without being EA-equivalent?"

Polujan365.lean - An affirmative answer to Polujan’s (2021) Open Problem 3.65: “For every even \(n\), are two vectorial bent functions EA-equivalent exactly when their vanishing-flat designs are isomorphic?” Here it is proved that vanishing-flat design isomorphism is equivalent to EA-equivalence for all vectorial bent functions in the admissible Nyberg range.

Polujan369.lean - A negative answer to the realizability question in Polujan’s (2021) Open Problem 3.69: “Must a subdesign of a vectorial bent function’s vanishing-flat design, with the parameters expected of an extension, itself arise from such an extension?” Here a six-variable vectorial bent function F: F₂⁶ → F₂² and a 2-(64,4,3) subdesign of VF(F) are formally verified in Lean, together with the impossibility of realizing that subdesign as VF((F,g)) for any Boolean coordinate g. This resolves the realizability question within the admissible Nyberg range; the separate subdesign-existence question is not addressed.

BentAffineOrbit.lean - An affirmative answer to Kudin, Pasalic, Polujan, and Zhang’s (2025) Open Problem 2: “Can one construct EA-inequivalent bent concatenations outside the completed Maiorana–McFarland class using affine rearrangements of one fixed seed?”; here an explicit pair is formally verified in every even dimension N ≥ 8, with distinct linearity indices N/2 − 2 and N/2 − 1, together with an exact rank formula for concatenations from rigid seeds.

BentDesignRank.lean - A refutation of Hyun, Kwon, Wang, and Wu’s (2026) Open Problem 7: “Do the designs D_{g,h} and TD_h in Theorem 10 always have equal binary ranks?”; here an explicit eight-variable counterexample is formally verified in Lean, satisfying every bent-function and duality hypothesis, with binary ranks 29 and 30 respectively.

MetricRegularBent.lean - An affirmative answer to Meidl, Polujan, and Pott’s (2023) Question 5.16: “Can the set C_F for some (n,m)-bent function F be metrically regular?” Here the code C_q = RM(4,1) + ⟨q⟩ for q = x₁x₂ + x₃x₄ is formally proved equal to its double metric complement. The formalization also verifies that q is extendable by exhibiting g such that q, g, and q + g are all bent. This establishes the requested existence for an extendable (4,1)-bent function; literature priority remains unverified.

DMT17.lean - An affirmative answer to Ding, Munemasa, and Tonchev’s (2019) Conjecture 17: “For each fixed admissible output dimension, does the number of inequivalent codes obtained from vectorial bent functions grow exponentially, with the proportion admitting a two-transitive automorphism group tending to zero?” Here both assertions are formally proved, with the stronger conclusion that even the proportion admitting a transitive automorphism group tends to zero, and quantitative bounds uniform across all admissible output dimensions.

JouxNarayanan54.lean - An affirmative answer to Joux–Narayanan’s Question 5.4: “Does ordinary tensor isomorphism reduce to tensor isomorphism under special-linear transformations?” Here zero-padding each mode from dimension n to 2n is formally proved to preserve and reflect equivalence over every field, for arbitrary input tensors. The proof certifies an explicit coordinate projection with exactly eight times as many output entries, establishing TI ≤ TI_SL.

TIEqTISp.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)'s Open Question 8: "Which, if any, of TI_O, TI_U, TI_Sp are equal to TI?"; here it is proved that TI = TI_Sp.

TIParStandalone.lean - Resolves the maximal-parabolic case of Chen, Grochow, Qiao, Tang, and Zhang’s (2024) research direction in §1.5: “What are the tensor-isomorphism complexity classes associated with other matrix groups, including parabolic subgroups?”; here TI = TI_Par is proved for the maximal parabolic family P_(n,n) over every field, under coordinate-projection reductions with polynomial output-size bounds. This addresses an explicitly proposed research direction, rather than a numbered open question.

FormTI.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)’s Open Question 1.11: “What is the complexity of tensor isomorphism restricted to other form-preserving groups, including mixed orthogonal groups and groups preserving forms that are neither symmetric nor skew-symmetric?”; here TI-completeness is proved for seven form-isometry families, including O(n,n), O(3n,n), and families preserving nonsymmetric or degenerate bilinear forms, under coordinate-projection reductions with polynomial output-size bounds.

TStarUnimodality.lean - A complete answer to Iršič, Klavžar, Rus, and Tuite’s (2024) Problem 5.2: “Which thick grids have unimodal general-position polynomials?” For m = min(r,a) and n = max(r,a), non-unimodality holds exactly when m = 2 and n = 8; m = 3 and 11 ≤ n ≤ 17; or m ≥ 4 and 2m + 4 ≤ n ≤ m + (m + 1)(1 + (m − 1)!). The classification is formally verified in Lean for all positive parameters, including the graph-counting formula and every exceptional case; literature priority remains unverified.

BalancedOrdinaryReduction.lean - Addresses Grochow and Qiao’s Open Question 10.8 on near-optimal reduction from d-tensor isomorphism to three-tensor isomorphism. Over every field, exact isomorphism equivalence and total output dimension O(n^⌈d/3⌉) are formally verified for arbitrary ordered shapes with d ≥ 3 and factor dimensions bounded by n ≥ 2, with an absolute implied constant. This achieves the requested exponent asymptotically as d grows and the counting-bound exponent when 3 divides d; the polynomial-time construction remains a written argument rather than a formally verified running-time theorem.

FangCounterexample.lean - A refutation of Fang’s (2017) Conjecture 2.9: “Does identical collapse tomography at every vertex imply that a graph is vertex-transitive?”; here a ten-vertex counterexample is formally verified in Lean. The classical Tutte 12-cage also refutes the conjecture, as noted in the file; priority for the explicit refutation remains unverified.

CFR525.lean - An affirmative answer to the CFR(5,25) open instance listed by Rosin’s CPro1 (2025), originating from the Handbook of Combinatorial Designs, §VI.62: “Does a 5 × 25 circular Florentine rectangle exist?” Here an explicit witness is formally verified in Lean, proving F_c(25) ≥ 5. This resolves the existence instance, not the exact value of F_c(25).

-------------------------------------------

Pending formalizations:
* Chizewer, Everett, Mithal, and Qiao (2026) [https://arxiv.org/html/2603.27128v1] — Open Problem 4: “Can average-case polynomial-time algorithms be devised for tensor orthogonal and unitary isomorphism over finite fields?”; also Li, Li, Qiao, Tao, and Wang (2026) [https://arxiv.org/html/2604.00591v1] — Problem 1.8: “Can average-case polynomial-time algorithms be devised for 3-tensor isomorphism over finite fields under orthogonal and unitary group actions?” — Here answered affirmatively for cubical tensors under the standard matrix-isometry actions.
