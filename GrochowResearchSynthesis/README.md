# Group isomorphism, closed tensor orbits, and field descent

## Group isomorphism

- [All finite class-two groups](CLASS-TWO-BLACK-BOX.md). A class-two decision oracle suffices for deterministic polynomial-time isomorphism search, exact counting, and automorphism generation on Cayley tables. The construction handles mixed cyclic orders and includes 2-groups.
- [Arbitrary exponents in the Lazard range](LAZARD-CLASS-REDUCTION.md). For \(p\)-groups of class \(c<p\), ordinary class-two decision suffices for decision, search, counting, and automorphism generation. The marked reduction recovers finite associative ring data from the adjoint ring of a commutator. Every query has order polynomial in the source order.

Together these give the four reductions for finite nilpotent groups whose Sylow \(p\)-subgroups have class at most two or class less than \(p\). The odd-order decision bound of Grochow–Qiao–Stange–Sun gives the corresponding \(N^{O((\log N)^{8/9})}\) algorithms on the odd-order family. [Part IV](https://arxiv.org/abs/2306.16317) · [Part V](https://arxiv.org/abs/2611.00735)

## Tensor orbit closure and restriction

- [Exact separating degrees](EXACT-GL-SEPARATOR-DEGREES.md). For explicit disjoint closed general-linear orbits the least degree is \(2(2^m-1)\) for two symmetric mixed cubic records in dimension \(m\). For one symmetric balanced order-\(2r\) tensor in dimension \(m+1\) it is \((2r-1)(r^m-1)/(r-1)\). Both examples work over any algebraically closed field. The cubic separator has a polynomial-size arithmetic circuit. [Lysikov–Walter](https://arxiv.org/abs/2411.04639)
- [Field descent and tied asymptotic restriction](ASYMPTOTIC-TENSOR-DESCENT.md). A multiplication tensor transports restriction witnesses over extensions. The note characterizes when diagonal assistance yields an extension-invariant preorder and proves a zero, one, or greater-than-one criterion for symmetric subrank over the algebraic closure in every prime-power order.
- [All tensor homomorphisms](ALL-TENSOR-HOMOMORPHISMS.md). The balanced encoding preserves singular and rectangular maps in mixed trilinear records of side length at most \(n^{\lceil d/3ceil}\). A second encoding preserves all maps in marked associative path algebras. The last two notes address the functoriality and asymptotic spectrum directions of Question 7.5. [Grochow–Qiao, Part I](https://doi.org/10.1137/21M1441110)

The linked manuscripts are written proofs. Eleven supporting Lean declarations passed the axiom audit. The Python scripts run finite controls. Publication priority for the new claims remains unverified.
