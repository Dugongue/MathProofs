# Four results on code and group isomorphism

These are AI-assisted informal proofs. They address three published coding questions and two conjectures concerning one group family. Publication priority for the new arguments has yet to be established.

| Question | Answer |
| --- | --- |
| [Nonprime-field code equivalence to lattice isomorphism](CodeEquivalenceToLattices.md) | Yes for every fixed finite field. The deterministic reduction has time polynomial in the block length and field order, with lattice rank $O(nq)$ over a nonprime field. A separate part gives prime-field descent of permutation equivalence in time polynomial in the block length and the bit length of the field. [Horlemann–Mazumder–Schaller–Weger, §6](https://arxiv.org/html/2607.12870v2#S6) |
| [A monomial-covariant companion code with nonsingular pairing](MonomialCompanion.md) | A universal assignment is impossible over every finite field, even for codes with distinct projective columns. This is equivalent orbitwise to a module-splitting condition. Equivariant lists can require exponentially many companions. [Horlemann–Mazumder–Schaller–Weger, §6](https://arxiv.org/html/2607.12870v2#S6.SS2) |
| [The transition for random-code rigidity](CodeRigidity.md) | For fixed $q$, the probability of scalar-only automorphisms is $e^{-\binom n2/|\mathrm{PG}(m-1,q)|}+o(1)$ uniformly in the dimension, with $m=\min(k,n-k)$. The same law holds under semilinear monomial equivalence, and swaps of equal projective columns describe the quotient in the critical window. [Li–Wang–Zhou, §V](https://arxiv.org/pdf/2607.23936#page=29) |
| [Pseudo-isometries and central quotients of the smallest flat genus-two block](FlatGenusTwoPseudoisometries.md) | The exact pseudo-isometry group refutes Schrock's Conjecture 4.4.4.3. Any isomorphic central quotients have kernels in the same orbit of an automorphism of the original group, proving Conjecture 4.4.4.1 on its full stated domain. The lifting result and the polynomial-time test from raw Cayley tables extend to every size of a single flat block. [Schrock, §4.4.4](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf#page=118) |

The separate field-bit-length question for arbitrary monomial scaling is outside the first bound. The random-code proof credits the existing high-dimension rigidity theorem and resolves the transition range identified in its conclusion.
