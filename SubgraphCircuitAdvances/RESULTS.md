# Four symbolic subgraph circuit results

1. [Ordinary path circuits and weighted clique over every field](ordinary-paths.md). The ordinary reading of Grochow–Urisman Question 1.11 is equivalent to fixed-parameter-size weighted clique circuits over the same field, even if restricted to paths of treewidth one. The signed reduction uses paths of length quadratic in the clique parameter.
2. [Sharp symmetric path complexity](symmetric-paths.md). With a fixed positive fraction of host vertices outside the path, the optimal orbit size is \(2^{\Theta(m\log(1+N/m))}\) in every characteristic. This gives a quantitative negative answer to the symmetric reading of Question 1.11 even over finite fields.
3. [The characteristic split for symbolic matchings](matching-characteristics.md). Ordinary matching circuits are equivalent to weighted clique circuits for fixed-parameter size over every field of characteristic different from two. Matching coefficients in characteristic two have polynomial-size division-free circuits.
4. [Characteristic-two circuits at bounded matching-split number](matching-split.md). For a pattern with \(h\) vertices and split number \(s\), symbolic subgraph circuits have size \(f(h)n^{3s+O(1)}\). An invariant splitting set can always be taken with at most \(3s\) vertices, and the factor is attained.

The four principal statements have written proofs. [Lean](SubgraphCircuitAdvances.lean) checks auxiliary identities. [Verification](Verification.json) gives the exact audit scope. Publication priority is unverified.
