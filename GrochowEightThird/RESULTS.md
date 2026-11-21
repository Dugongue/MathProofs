# Nine answers to open questions

These are proof drafts. The [Lean records](Verification.json) cover a finite counterexample and three supporting identities. The remaining arguments are mathematical proofs in prose.

| Question | Answer |
| --- | --- |
| Polynomial-index permutation-group TRANSVERSAL | Deterministic logspace-uniform NC for arbitrary ambient permutation groups, given generators for the subgroup and ambient group. As a consequence, minimum-degree faithful permutation representations of Fitting-free permutation groups can be constructed in deterministic NC. [Proof](groups.md#4-deterministic-parallel-transversals) |
| Linear symmetric IPS for the CFI equations | Linear-size placeholder-linear certificates over F₂ under the original edge-flip group, excluding an exponential separation on these instances. [Proof](cfi-ips.md) |
| Blum-Smith–Garcia–Hidalgo–Rodriguez Question 5.4 | For each fixed number of weights and sufficiently large prime, the only extremal supports for polynomial invariant field generators are the stated signed intervals and their one-point deletions. [Proof](invariants.md) |
| Blum-Smith–Garcia–Hidalgo–Rodriguez Question 5.14 | Degree at least three is necessary for a transcendence basis if any irreducible constituent is other than a one-dimensional character of order dividing two. This is an exact characterization of when degree at most two suffices. [Proof](invariants.md) |
| Colbrook's signed support question | Inverse-trace supermodularity for every positive definite realization holds exactly for antibalanced signed graphs. The converse holds with arbitrarily small relative off-diagonal row sums. [Proof](nystrom.md) |
| Colbrook's strict diagonal-dominance question | An explicit submodularity ratio of at least 1−ρ, where ρ is the largest relative off-diagonal row sum, gives a greedy approximation theorem. [Proof](nystrom.md) |
| Simons Workshop Problem 6.4 | Least-squares residuals need not equioscillate. Explicit counterexamples cover both continuous and discrete norms. [Proof](sign.md) |
| Maleki–Razafimahatratra Problem 1.4 | Canonical uniqueness fails on triples of a six-element set. There is also a classification whenever the standard constituent occurs. [Proof](invariants.md) |
| Blum-Smith–Garcia–Hidalgo–Rodriguez Question 5.15 | For an odd prime p and m distinct nontrivial weights in nonmodular characteristic, the least degree of a transcendence basis is at least ceil(p^(1/m)+1). [Proof](invariants.md) |

## Additional results

- [A depth-four reduction](complexity.md) gives orbit size n^O(√(kd)) for matrix-symmetric circuits with support bound k and degree d. The same note gives an equivalence between Grochow–Urisman Open Question 1.11 in the unrestricted symbolic setting and the parameterized clique circuit question.
- [A spectral tightness bound](volume.md) answers Simons Workshop Problem 4.7 with universal relative bounds, equality cases, and a quadratic-order gap realized by a family of spectra.
- [An exact cubic composition recurrence](sign.md) gives the same-budget asymptotic separation requested by Simons Workshop Problem 6.5. A four-product degree-nine polynomial yields a faster rate, and the stage count needed to match an unrestricted budget m has order m for fixed δ.
- [A modular symmetric IPS criterion](modular-ips.md) characterizes existence via fixed loci and gives an exact finite-characteristic pigeonhole classification. The note credits the authors' earlier polynomial-size announcement in characteristic zero.
- [An epimorphism reduction](groups.md) takes Cayley-table groups of odd prime exponent p and class at most p to class-two groups. It supplies a constructive decoder for surjective witnesses. The unrestricted finite-group epimorphism and tensor isomorphism problems remain open here.
