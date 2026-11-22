# Sharp dimensions for tests of tensor and matrix isomorphism

## Main results

1. **When do field extensions conceal a tensor orbit?** Over every finite field, take multiplication tensors of finite étale algebras with three independent changes of basis. For any nonempty list of extension degrees greater than 1, the first dimension where all tests can miss an inequivalence is half the least product of $2p$ over a set of primes meeting every degree. The first unordered pair of tensor orbits is unique. The same threshold describes cancellation after tensoring finite étale trace tensors with a fixed trace tensor whose field factors have those degrees. One degree-one test guarantees recovery in all dimensions. [Rigidity and descent](Degree.md) · [Cancellation and polynomial operations](Counting.md)
2. **How hard is it to detect the first failure?** Existence of a collision up to a binary dimension bound is NP-complete even for semiprime extension degrees over a fixed finite field. Writing the bound in unary gives a polynomial-time algorithm. The instance specifies a suite of tests. Direct tensor isomorphism takes two individual tensors as input. [Reduction and algorithm](Degree.md)
3. **What does a modular characteristic polynomial add?** For the permutation of geometric points, also supply its characteristic polynomial modulo $m$. The joint threshold has the same prime-set formula with all primes of $m$ mandatory and an extra factor $m/\operatorname{rad}(m)$. The first pair remains unique. With the modular observation alone, the answer is exactly $2^{\omega(m)-1}m$ for $m>1$. Two proofs using prime coordinates connect the result to tensor cancellation. [Prime powers, mixed tests and extremizers](Modular.md)
4. **How soon can an identity distinguish locally conjugate tuples?** For each prime $p$ and $r\ge2$, explicit commuting permutation matrices agree up to simultaneous permutation conjugacy on every proper subgroup of $(C_p)^r$. Over characteristic $p$, their first separating scalar polynomial identity in the generators has degree $(r-1)(p-1)+1$. A Polynomial Calculus refutation of the simultaneous-conjugacy equations in the unknown change of basis has degree exactly 2. The two degrees measure different variables. [Construction, exact degrees and earlier work](Orbit.md)

Quadratic and cubic extensions give a concrete instance of the first theorem. In every dimension below 12 the two tests jointly recover the original tensor orbit in this family. In dimension 12, the first pair consists of six copies of the base field and its degree-six extension on one side, and three quadratic plus two cubic factors on the other. It also collides under the permutation characteristic polynomial modulo 6. At dimension 12 each test regime has just this pair, up to interchange and isomorphism.

## Prior work and scope

The alternating construction and qualitative cancellation criteria have precedents for finite dynamical systems. Earlier work also exhibits loss of information in the characteristic polynomial of a permutation matrix in positive characteristic. The proposed contributions are the sharp dimension, rigidity for arbitrary combined observations, and the complexity of the first-collision decision problem. Bibliographic priority remains open. [Ploščica and Zelina](https://ploscica.science.upjs.sk/clanky/p14.pdf) · [Porreca and Rolland, §3.3](https://arxiv.org/html/2604.04065v1) · [Cherniavsky and Sklarz](https://arxiv.org/abs/math/0411554)

The matrix-tuple example relates to the Polynomial Calculus equations in Galesi, Grochow, Pitassi and She. Their Question 7.3 concerns ordinary matrix conjugacy and congruence. Here the separating identity and refutation are computed for an explicit family of simultaneous-conjugacy instances. The extremal side of the underlying group-action construction already appeared in the project's Galois-marks work. [Open Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

## What was checked

All four entries have mathematical proofs in the linked notes. Independent Lean 4.33 kernel checks and transitive axiom audits passed for eight component statements. The complete extremal, complexity and degree theorems are written proofs. The formal statements cover multidimensional mass doubling, transport of cycle weights, a local lower bound, recovery of a unital commutative algebra isomorphism from an isotopy, and the two orientations of the norm obstruction for matrix conjugacy. [Formal audit scope](Audit.json)

The Python controls have separate entry points. Run each with Python 3 from this directory. `profiles.py` compares direct characteristic coefficients and cycle powers across 17 test panels and 124,729 partition observations through dimension 24. `CountingCheck.py` tests actual cycle products for 179 marker profiles through dimension 16. `DegreeCheck.py` checks 4,136 partition–schedule inputs and the extension spectrum of a dimension-120 pair. `OrbitCheck.py` performs modular elimination for seven tuples and reproduces the supplied small-case results. [Orbit controls](OrbitControls.json)

## Anonymous search provenance

Four seeded runs used the same v6 packed bank with 590,787 declaration records. Producers and consumers were joined by numeric output and explicit input expression IDs across different opaque module IDs. Names and descriptions were unavailable to the selection function. Of 823 qualifying multi-input joins, the four frozen lists retained 180, 160, 125 and 128, with 351 distinct consumers in their union. The full registered source catalog was available for follow-up. These numbers describe this packed-bank scan alone. Some joins match common hypotheses without encoding a substantial theorem application.

In the first list, positions 12, 26, 52, 79 and 92 contained squarefree factorization, coprime divisibility and primitive roots, a cycle-type producer, a valuation lemma, and cyclotomic expansion. Choosing to connect them to modular Frobenius profiles came after the reveal. The individual records and seeds are retained below. The mathematical deductions and proofs followed the reveal and were checked separately.

| Selection | Seed | Limit | Frozen numeric IDs |
|---|---:|---:|---|
| Modular observations | 842333 | 180 | [List](Frozen.json) |
| Descent and rigidity | 619731 | 160 | [List](DegreeFrozen.json) |
| Cancellation | 37847531 | 125 | [List](CountingFrozen.json) |
| Simultaneous conjugacy | 912783 | 128 | [List](OrbitFrozen.json) |

To replay, supply the v6 bank to [the structural selector](fanin.py) and the listed seed and limit. The SHA-256 digests of the declaration and binder arrays are respectively `c513f93e7071d3969d64b1eb19855fbd2a4f6ed6375b24f6769d477c20a504f1` and `02e86aca916469fd85cf11e727de4825e96cfaaf155f03f69735fff77ca88286`.

~~~text
python fanin.py BANK --seed 842333 --keep 180 > candidates.json
python fanin.py BANK --reveal candidates.json
~~~
