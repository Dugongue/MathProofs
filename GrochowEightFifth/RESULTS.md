# Ten answers to open questions

The proofs are written in prose. [Lean verification](Verification.json) covers two algebraic identities that support the eigenvalue proofs.

| Question | Answer |
| --- | --- |
| Blum-Smith et al., Question 5.10 | In characteristic two, explicit representations have separating degree exactly four and invariant-field generation degree exactly r+1 in dimension 4r+1. [Proof](invariants-q510.md) |
| Blum-Smith et al., Question 5.8 | Faithful absolutely irreducible representations of nonabelian affine groups have field-generation degree at most nine and separating degree at least the underlying prime. [Proof](invariants.md) |
| Modular extension of Blum-Smith–Derksen Theorem 1.1 | The bound β_field ≤ 2D_span+1 holds in all characteristics. It is sharp in each odd modular characteristic. [Proof](invariants.md) |
| Dawar–Wilsenach, determinant in odd characteristic | Independent even row and column symmetry forces exponential orbit size for determinant circuits in every odd characteristic, on an unbounded sequence of dimensions. [Proof](alternating-determinant.md) |
| Dawar–Dwivedi–Pago–Seppelt, depth-three question | A matrix-symmetric circuit of support k and output degree d reduces in characteristic zero to depth three with orbit size n^O(√(kd)). [Proof](complexity.md) |
| Dawar–Wilsenach, squared matching counts | Squared matching counts modulo any fixed odd prime have linear counting width on simple bipartite graphs. This gives the square-symmetric circuit lower bound even on symmetric zero-one inputs. [Proof](complexity.md) |
| Simons Workshop Problem 3.9 | Randomized exact matrix-vector queries approximate a near-maximum-modulus eigenvalue in O(ε⁻² log(nK/δ)) products for a supplied eigenbasis condition bound K. [Proof](extremal-eigenvalues.md) |
| Simons Workshop Problem 3.9 rightmost variant | Randomized exact matrix-vector queries approximate a nearly rightmost eigenvalue in O(ε⁻⁴ log(nK/δ)) products. [Proof](extremal-eigenvalues.md) |
| Simons Workshop Problem 3.4 | Ritz values preserve target multiplicities with sharp angle exponents 2/(r+1) for reducing subspaces and 1/(r+1) in the general invariant case with diagonalizable target restriction. The buffer of dimension r is arbitrary. [Proof](buffered-ritz.md) |
| Simons Workshop Problem 4.4 | Isotropic subgaussian kernel features of dimension O(k) give a uniform constant-factor transfer from O(k) sampled rows. An explicit selector attains the guarantee for orthogonal feature clusters. [Proof](kernel-row-sketch.md) |

## Further results

- [Finite-group epimorphism counts and WL Version I](groups.md) gives a same-prime, single-query class-two reduction for counting epimorphisms between exponent-p groups of class at most p, for odd p. It also gives count-free Version I identification for the specified direct products with short power expressions.
- [The determinant symmetry boundary](complexity.md) classifies all ten determinant-preserving overgroups of simultaneous alternating permutations, distinguishing the polynomial and exponential ranges.
- [Orbit evaluation and cyclic degree bounds](invariants.md) gives a randomized polynomial-time computation of the spanning degree for explicitly listed group actions and a sharp composite-order two-weight bound.
