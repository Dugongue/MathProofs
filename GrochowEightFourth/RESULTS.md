# Ten answers to open questions

The proofs are written in prose. [Independent Lean verification](Verification.json) covers the exact rounded two-state residual transition and a supporting finite weighted-variance identity.

| Question | Answer |
| --- | --- |
| Dawar–Wilsenach’s odd-characteristic square-symmetry question | Square-symmetric permanent circuits have exponential orbit size over every odd characteristic, already on zero-one square inputs. [Proof](complexity.md#square-symmetric-permanent-lower-bounds-in-all-odd-characteristics) |
| Johnson–Levet–Vojtěchovský–Widholm, Remark 1.4 | The fixed-dimensional WL bounds extend to groups with unique Remak decompositions and a bounded number of generators per direct factor. [Proof](groups.md) |
| Blum-Smith et al., Question 5.5 | The prime-order extremizer classification fails for infinitely many composite orders, even for three weights. [Proof](invariants.md) |
| Blum-Smith et al., Question 5.9 | Explicit faithful modular representations have an unbounded gap between the separating degree and the invariant-field generation degree. [Proof](invariants.md) |
| Blum-Smith et al., Question 5.12 | The two-weight upper bound survives composite order. The stated equality criterion fails. [Proof](invariants.md) |
| Blum-Smith et al., Question 5.13 | The prime-order bound fails for infinitely many composite orders, even for two faithful noninverse weights. [Proof](invariants.md) |
| Blum-Smith et al., Question 5.16 | For two distinct nontrivial weights of a prime cyclic group, the Hilbert series determines the unordered weights up to group automorphism and the entire graded invariant ring. [Proof](invariants.md) |
| Simons Workshop, Problem 2.15 | A binary64 steepest-descent iteration on a positive definite two-dimensional diagonal system has a constant-norm residual cycle. [Proof](steepest-descent.md) |
| Simons Workshop, query question following Problem 2.8 | For Gaussian matrices, the exact matrix-vector query fraction for fixed relative residual ε has threshold 1−ε². Bernoulli and Rademacher input can be recovered by one unrestricted exact query. [Proof](gaussian-queries.md) |
| Simons Workshop, volume-sampling variance question | Diagonal orientations maximize every convex statistic of the trace error at fixed spectrum. The paper gives the exact maximum variance and a quantitative deficit bound. [Proof](volume-variance.md) |

## Further results

- [An exact modular IPS degree formula](complexity.md) characterizes every bounded placeholder degree via fixed loci. For the symmetric pigeonhole system its minimum equals the largest p-power q with N mod q ≤ m.
- [Cyclic and abelian separating degrees](invariants.md) give high-density sufficient conditions for strict gaps and examples with no absolute support-size cutoff, addressing Questions 5.6 and 5.7 in the specified settings.
