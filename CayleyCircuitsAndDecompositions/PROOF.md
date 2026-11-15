# Cayley-table lower bounds, quasigroup decomposition, and characteristic-two symmetrization

These informal proofs extend the earlier work on Cayley-table lower bounds, group decomposition and algebraic isomorphism. Random relabelling makes clause falsification rare. Operator-group decompositions let a quasigroup factorization retain its point stabilizer. The adjoint-algebra argument finds symmetric multipliers using at most three directions in a rank-improvement search.

| Proof | Result |
| --- | --- |
| [Stretched-exponential CNF lower bound](GroupIsomorphismCNF.md) | Grochow–Kardeş–Levet Question 7.1. For infinitely many orders $n=3^r$, both CNFs and DNFs deciding isomorphism from binary-encoded Cayley tables have size at least $2^{\Omega(\sqrt n)}$, even on valid Abelian inputs of exponent at most nine. An exponent-four version gives $2^{\Omega(n^{1/3})}$. |
| [Quasigroup direct product decomposition](QuasigroupDecomposition.md) | Johnson–Levet–Vojtěchovský–Widholm Question 7.4. A deterministic polynomial-time algorithm outputs fully refined factor tables and a product isomorphism for every quasigroup. |
| [Characteristic-two symmetrization](CharacteristicTwoSymmetrization.md) | Ivanyos–Qiao's characteristic-two symmetrization question. Over every characteristic-two field, a deterministic polynomial arithmetic algorithm finds invertible left and right changes making a tuple symmetric, or determines that none exist. The algorithm also handles alternating matrices, and has polynomial bit time over explicitly represented finite fields. |
| [Loewy lengths and modular group algebra factors](GroupAlgebraFactorization.md) | Refutes Osterlund's conjecture for diagonal tensor products yielding the regular module, including counterexamples for directly indecomposable groups at every prime. Resolves the Frattini-class-two case over arbitrary characteristic-$p$ fields of the Carlson–Kovács algebra-factorization question. |

The individual files cite the source questions and the results used in their proofs.
