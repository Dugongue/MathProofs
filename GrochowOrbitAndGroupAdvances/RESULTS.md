# Orbit recovery, graph multiplicities, and tensor and group algorithms

## Answers to questions in papers

1. **A generic real orbit need not determine the abstract group.** Two nonisomorphic groups of order \(3\cdot 2^{34}\) acting faithfully on \(\mathbb R^{72}\) have isomorphic orbit Gram graphs at every common seed. This refutes Mixon–Vose Conjecture 2.7. Together with their two-orbit theorem it gives the exact worst-case abstract recovery count when cross-orbit inner products are available. [Proof](invariants.md) · [Source question](https://arxiv.org/html/2411.17434#S2)
2. **Sharp concrete orbit count.** In real or complex dimension \(d\), the exact worst-case count is \(\lceil d/2\rceil\) for Borel recovery from ambient-coordinate observations with jointly generic competitors. With arbitrary competitors realizing the observed point sets, the sharp count is \(d\). This answers the minimum-orbit question in Mixon–Vose §4 for both observation models. [Proof](concrete.md) · [Source question](https://arxiv.org/html/2411.17434#S4)
3. **Square-root degree separation for Grochow–Urisman’s multiplicities.** Two explicit symmetry-characterized cluster graphs first differ in their filtered multiplicity profiles at degree \(\Theta(\sqrt n)\). In the full orbit modules the first differing Specht label has exact weight \(m+1\) at \(n=6m^2\). The logarithm of the number of possible filtered profiles through degree \(d\) is at most \(\exp(O(\sqrt d))\), uniformly in graph order. [Proof](graph-multiplicities.md) · [Source question](https://arxiv.org/html/2606.26244v2#S6.SS4)

## Classical tensor-isomorphism catalogue

Five project catalogue targets have proofs, with the exact field and input conventions in the [theorems](determinants.md).

| Target | Result |
| --- | --- |
| 25 | Orthogonal similitude TI with independent unknown multipliers is ordinary-TI complete uniformly over finite fields, including characteristic two. |
| 26 | Symplectic similitude TI reduces to symplectic TI at linear side length with transporter lifting and recovery. |
| 27 | Finite-field semilinear classical TI has a uniform base-field ordinary-TI compilation. Shared twists act on extension-balanced tensors. Independent twists act on tensors over the common base. |
| 30 | Compact quaternionic-unitary TI in the complex coordinate model is equivalent to complex unitary TI. The real quaternionic-linear model reduces to real orthogonal TI. |
| 39 | The five symplectic actions on three-way arrays are equivalent with linear side growth over every field. |

## Further theorems

- In dimension \(d\) there can be \(2^{\Omega(d)}\) pairwise nonisomorphic finite groups with identical within-orbit Gram data at every common seed. The proof identifies their isomorphism classes as orbits of sets of oriented linear forms over \(\mathbb F_3\). [Proof](ambiguity.md)
- A single numerical Gram graph recovers the regular permutation action if the true representation has no four-dimensional quaternionic constituent. Competitors may have such constituents. [Proof](recovery.md)
- The Easdown–Praeger minimum faithful degree inequality holds for every abelian quotient of every finite nilpotency-class-two group, including \(2\)-groups of arbitrary exponent and center rank. The general conjecture concerns all finite groups. [Proof](groups.md#1-the-easdownpraeger-inequality-for-all-finite-groups-of-class-at-most-two)
- Compact representations of quotients of field Heisenberg groups admit polynomial-time epimorphism decision, search, and exact counting in every characteristic. [Proof](groups.md#3-compact-exact-epimorphism-counting-for-quotients-of-field-heisenberg-groups)
- Bounded-width factor-center arrangements admit exact Cayley-table epimorphism counts and uniform sampling in the scope stated in the proof. [Proof](groups.md#4-exact-epimorphism-counts-for-bounded-width-factor-center-arrangements)
- Minimum faithful **transitive** degree and an optimal stabilizer are computable in polynomial time for compact class-two \(p\)-groups with elementary abelian central quotient and cyclic derived group. [Proof](groups.md#5-minimum-faithful-transitive-degree-when-the-central-quotient-is-elementary-abelian-and-the-derived-group-is-cyclic)
- A separate bounded-factor solvable-radical construction is included for its independent method. The project already reports a stronger bound. [Proof](groups.md#2-parallel-computation-of-the-solvable-radical-with-bounded-simple-factors)

## Verification

The main theorems have written proofs. Three finite supporting declarations passed Lean kernel checking and an independent transitive axiom audit. These cover the displayed nine-point Hermitian span, its rich projective lines, and its coordinate-permutation check with Frobenius. An independent computation checked all 85 points of \(\mathbb P^3(\mathbb F_4)\), the 512 span elements, and all 3,000 admissible projective frame images into the nine-point set. [Lean certificate](OrbitGramCertificate.lean) · [Axiom record](Verification.json) · [Independent finite check](check_nine_points.py)
