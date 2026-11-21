# Follow-up results on Grochow's open problems

This report keeps the fields, input models, and requested outputs of the [Grochow catalog](https://github.com/Dugongue/MathProofs/tree/main/GrochowOpenProblems) explicit. The constructions below extend a different set of questions from the preceding eight-result report.

## Complete answers and explicit branches

| Question | Result | Proof |
| --- | --- | --- |
| **GP010. Same-prime class reduction at the Lazard boundary** | For every odd \(p\), reducible in polynomial Cayley-table time from exponent dividing \(p\), class at most \(p\), to class at most two at the same prime, with polynomial output order and a witness decoder. | [Group results](groups.md) |
| **GP011. A compositional, surjective decoder for mixed exponents** | Impossible with polynomial output order. The cyclic inputs \(C_{p^e}\) force output order at least \(p^{p^{e-2}+1}\). The decision-only question is distinct. | [Group results](groups.md) |
| **GP157. Positive-characteristic matrix conjugacy in ordinary PC** | The worst-case refutation degree is \(\Theta_p(N)\) for each fixed prime \(p\). Two-sided rectangular inverse systems have matching upper and lower estimates within a constant factor even in high \(p\)-adic strata. Exact constants are open. | [Proof complexity](complexity.md) |
| **GGPS Question 7.3. Matrix congruence** | Sharp degree \(\Theta_p(N)\) for symmetric matrices in every fixed positive characteristic and arbitrary matrices or simultaneous tuples in odd characteristic, over the algebraic closure. | [Congruence](congruence.md) |
| **Original FGS rank markers. Reverse PC simulation** | A constant-degree reverse simulation is impossible in every fixed positive characteristic. Original partition erasure can change degree at most six into linear degree, including with fixed finite-field equations. | [Original FGS construction](fgs-obstruction.md) |
| **GP100. Specified-class obstruction** | The natural skew-edge orbit-moment model gives exactly the fractional relaxation. Every Horn spectral-sum lift for the complete-graph perfect-matching polytope requires exponential size. The convex hull of supported skew-unitary weights gives an exact compact nonlinear model. | [Matching and graph invariants](invariants.md) |

## Further exact results with restricted scope

| Question | Scope and result | Proof |
| --- | --- | --- |
| **GP070–072. Graphs characterized by symmetry** | Exact general criterion using the orbits on unordered pairs. Polynomial-time recognition and promised isomorphism at prime order. Cycle-index distinction up to complementation at prime order and for all self-complementary inputs. The seven-cycle refutes the rank-three premise in the source. | [Orbital criterion](invariants.md) · [Prime order](invariants-prime.md) · [Self-complementary case](invariants-selfcomp.md) |
| **GP076. Recognizing forms characterized by symmetry** | Reduces to existential complex feasibility in polynomial time, giving PSPACE and AM under GRH. The connected fixed space is computable in deterministic polynomial time. | [Proof complexity](complexity.md#recognizing-characterization-by-linear-symmetries) |
| **GP103. Subcubic homomorphism indistinguishability** | Dense rational weighted indistinguishability is polynomial-time equivalent to real orthogonal equivalence of one rational cubic. The reverse reduction can use rational positive-semidefinite edge weights. The GI-versus-TOCI endpoint remains open. | [Homomorphism evaluations](invariants-hom.md) |
| **GP140. Laminar quantum functionals** | Upper and lower functionals agree on every complex tensor of border rank at most two, in arbitrary order. The W-state formula is an explicit optimization over one simplex. | [Tensor results](tensors.md) |
| **Christandl Open Problem 3. Random tensor networks** | Restriction and degeneration have the same limiting GHZ assistance rate almost surely for binomial uniform hosts at constant or subpolynomially decaying density, with symmetry or all edge orientations. The common rate equals that of the complete hosts. | [Tensor results](tensors.md) |

The unrestricted graph, invariant, and network versions extend beyond these scopes. The FGS obstruction leaves the comparison of the two specific graph routes in GP159 open. The linear proof degree results use a rectangle lower bound from Riis's 2026 preprint.

## Verification

The main results are paper proofs. Lean checked the finite-dimensional prime-power matrix order bound used in GP011 and the odd skew-matrix determinant implication used in GP100. [Lean source](ResearchBounds.lean) · [Hash and axiom audit](Verification.json)
