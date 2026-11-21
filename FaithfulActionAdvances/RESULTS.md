# Four advances on minimum faithful permutation actions

1. [Minimum faithful transitive degree at orbit cap \(p^2\)](transitive-degree.md). The transitive threshold problem is NP-complete with a supplied minimum-degree faithful action whose orbits all have size \(p^2\). The numerical approximation gap is exponential in the supplied degree. At cap \(p\) the problem is polynomial.
2. [Minimum actions with a small noncyclic commutator part](commutator-parameter.md). For class-two permutation groups, the parameter is the size of the complement of the largest cyclic factor in each Sylow derived subgroup. In particular cyclic derived subgroup gives a polynomial-time algorithm on succinct permutation input with unrestricted center.
3. [Optimal actions for scalar-center coprime extensions](coprime-actions.md). A genuinely nonnilpotent Cayley-table class has a deterministic polynomial-time algorithm. It includes class-two exponent-\(p\) normal Sylow subgroups with scalar center action and arbitrary cyclic complements, as well as the stated unbounded-rank split abelian complements.
4. [Exact actions for thin central quotients](thin-central-quotients.md). Central quotient minimization for extraspecial products is fixed-parameter tractable in the dimension of the central kernel, the prime being fixed. The algorithm handles arbitrary factor ranks and binary signs.

The four main statements have written proofs. [Lean](FaithfulActionAdvances.lean) and [verification](Verification.json) give the independently checked supporting identities. Publication priority is unverified.
