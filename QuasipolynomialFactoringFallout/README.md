# Consequences of deterministic quasipolynomial finite-field factoring

Assume complete univariate factorization over every explicitly represented finite field \(\mathbb F_q\) is deterministic in \(d^{O(\log(d+1))}(\log q)^{O(1)}\) bit time for degree \(d\). This is the computational input. Where a result uses only linear algebra or a classical reduction, its unconditional scope is stated separately.

| Result | Scope | Proof |
| --- | --- | --- |
| Deterministic transporter search from bounded-dimensional projected stabilizers | Projective quivers with polylogarithmic cycle rank, and unrestricted ordinary TI on the stated small-mode diagonal connected-stabilizer locus. The algorithm outputs actual mode maps. | [Transporters](Transporters.md) |
| Prescribed-determinant search and exact counting at square-zero radical | Recognizable ordinary associative multiplication isotopes, arbitrary finite base field and arbitrary matrix factors in the semisimple quotient. Also gives a Frobenius-power extension test and an exact factoring equivalence for restricted étale witness search. | [Square-zero algebras](SquareZero.md) |
| Efficient extension testing and hard least-degree optimization | For finite étale multiplication tensors, membership is polynomial-time, while the binary minimum-degree threshold is NP-complete over \(\mathbb F_2\). A compact power-equation family gives a multiplicative-order equivalence and output-sensitive witness construction. | [Extension profiles](Profiles.md) |
| Short PC and IPS certificates in explicit finite quotients | An input border basis of maximum monomial degree \(\rho\) gives deterministic PC refutations of degree at most \(\rho+2\) in the gate encoding, and short Hilbert-like IPS certificates for the original equations. Factoring supplies the affirmative closed-point witnesses. | [Certificate construction](Certificates.md) |

The projective-quiver theorem develops deterministic monomial cuts that preserve rational points. The square-zero section identifies exactly which parts extend the earlier graph and determinant work. The lower bound for the least extension degree and the finite-quotient negative certificates hold independently of the factoring input. None of the theorems resolves unrestricted tensor isomorphism or the unrestricted polynomial-in-rank PC degree question.

The results are written proofs. [Isotopy.lean](Isotopy.lean) contains a supporting multiplicativity identity checked with Lean and audited for axioms. The complexity bounds and classification theorems are established in the written arguments.
