# Exact generation, principal minors, and algebraic equivalence

Five informal proofs. The magma, transformation-semigroup, and principal-minor results answer the cited questions as stated. The characteristic-two result covers the symmetrization task of a question that also asks about tuple isometry. The code-equivalence reduction is bit-polynomial in the alphabet size, improving on the alphabet-dependent complexity of the earlier repository proof for extension fields.

| Proof | Result |
| --- | --- |
| [Exact generation of finite magmas](ExactMagmaGeneration.md) | The exact minimum generating-set problem is $\mathsf{DP}$-complete, even for commutative magmas with an absorbing zero and zero squares. Answers Collins–Grochow–Levet–Weiß, §7.3. |
| [Rank of regular transformation semigroups](RegularTransformationSemigroups.md) | The Stirling-number bound holds for any regular transformation semigroup generated in one rank. Answers Gray's Open Problem 2. |
| [Characteristic-two tuple symmetrization](CharacteristicTwoSymmetrization.md) | Constructive deterministic polynomial-time symmetrization in the field-arithmetic model. The algorithm also handles alternating tuples. Answers the symmetrization task of Ivanyos–Qiao's first open problem. |
| [Code equivalence and lattice isomorphism](CodeEquivalenceToLattice.md) | Uniform bit-polynomial reductions from permutation and signed-permutation code equivalence over every finite field. Answers the field-extension question of Cheraghchi–Shagrithaya–Veliche in this complexity regime. |
| [Principal-minor oracle lower bound](PrincipalMinorOracle.md) | Exact reconstruction needs all nonempty principal-minor queries in the worst case. Bounded error still needs exponentially many queries. Answers the individual-minor-oracle question of Aravind et al. |

The proofs include attribution and the exact input and complexity models. Publication priority is unestablished.
