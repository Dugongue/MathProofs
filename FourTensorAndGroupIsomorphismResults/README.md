# Four tensor and group isomorphism results

These informal proofs were developed for MathProofs with AI assistance. They reuse the project's fixed-ring algorithm, augmentation encoding, and balanced tensor constructions. Publication priority remains unestablished. The runtime claims invoke published or publicly posted terminal algorithms and have received internal mathematical review.

| Proof | Result |
|---|---|
| [Determinant-resolved tensor isomorphism](sl.md) | For every fixed finite commutative ring, finds witnesses and counts all transporters by determinant triple in $2^{O_R(n^{7/4}\log(n+2))}$ time. This decides the determinant-one case and outputs generators of the ordinary stabilizer. |
| [Class-two groups with bounded derived exponent](group.md) | Gives isomorphism time $N^{\widetilde O(\sqrt{\log_p N})}$ for odd $p$ and fixed derived exponent bound, and for $2$-groups with elementary abelian derived subgroup. The exponent of the group itself may grow. For every fixed $p$ and derived exponent bound, the stated succinct problem is prime-field TI-complete. |
| [Balanced order reduction over commutative rings](order.md) | Uniform objectwise reduction of order-$d$ free tensor isomorphism to ordinary three-tensor isomorphism over the same commutative ring, with maximum side $O(d^6n^{\lceil d/3\rceil})$. The constructor uses only reindexing and zero and one, including over a supplied composite integer modulus. |
| [Tensor isomorphism in nonfree modules](torsion.md) | For any fixed finite commutative principal ideal ring, gives the $7/4$ exponent bound on the original generator counts for arbitrary presented modules, and the $3/2$ exponent up to logarithms in odd characteristic. The tensor is an element of a genuine tensor product. |

The [short-probe algorithm](ALGORITHM.md) and [augmentation-quotient compiler](JETS.md) are included as supporting proofs. The existence of a polynomial-time reduction from unrestricted determinant-one TI to ordinary TI remains open here. The balanced result reaches the counting exponent when three divides $d$. Its result for other orders is the ceiling exponent. [Open questions and prior field reductions](https://arxiv.org/html/1907.00309#S10.SS2)
