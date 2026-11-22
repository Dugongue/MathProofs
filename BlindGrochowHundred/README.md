# One hundred Lean theorems from structural search

Four workers each received 180 distinct structural matches from a shared Lean term bank. The selector matched numeric output and input IDs before reading declaration names. The workers interpreted their matches after the reveal, using them to find and develop the following families.

| Worker | Theorems | Scope |
|---|---:|---|
| A | 25 | Paired Frobenius tests, period arithmetic, weighted marginals and exact rectangle collisions |
| B | 25 | Character-constrained matrix transports, graph gauges, certificates and reachable linear realizations |
| C | 25 | Multiplication transports, Frobenius tensors, centroids and associative reconstruction |
| D | 25 | Linear observation orbits, rank increments and optimal finite compression |

## Results to read first

- **Paired field-extension tests.** If powered periods from two extensions are recorded as pairs, taking their least common multiple recovers the period at the gcd of the exponents. Coprime exponents therefore recover all original weights. Separate extension decks record only marginals, whose weighted rectangle ambiguity is quantified. [Proofs and scope](A.md)
- **Character-constrained transport.** An invertible anchor translates left-right transport to simultaneous conjugacy plus a character condition. A root gauge for a directed graph extends uniquely exactly when it transports every based edge label. These are exact criteria for the stated presentations. [Proofs and precedent](B.md)
- **Multiplication from trilinear data.** A separating reference pairing and a symmetric tensor let normalized contractions recover a product. Commutation of those contractions suffices for associativity, including in characteristics 2 and 3. Nondegenerate weighted forms also recover orthogonal algebra splittings. [Proofs and precedent](C.md)
- **Optimal compression of scalar tests.** An arbitrarily large scalar-valued linear panel on a finite-dimensional space has a subpanel with the same kernel of size exactly its joint rank. Every finite scalar subpanel with the same kernel has at least that size. Vector-valued probes satisfy a corresponding dimension-decrease bound on any specified subspace. [Proofs](D.md)

## Verification and reuse

The four Lean sources contain the exact statements. Their 100 selected conclusions passed independent Lean kernel and transitive axiom audits on the published source bytes. The mathematical notes explain applications of the formal statements and their relationship to prior work. This is a collection of exact conclusions with different scopes and levels of novelty. [Full theorem index](Theorems.md) · [Audit](Audit.json)

The packed bank contained 590,787 declaration records and 823 eligible multi-input matches. This pass froze 720 of those matches, partitioned into four disjoint queues. These counts apply to the packed snapshot used for structural selection. To regenerate the public queues, supply the same packed bank. To check a pass, supply a compatible Lean installation and the independent checker.

~~~text
python proof_pass.py plan BANK queues-copy --seed 9814551 --keep 180 --quotas 25 25 25 25
python fanin.py BANK --reveal queues-copy/worker-1.json
python proof_pass.py audit Pass.json CHECKER receipts --target 100
~~~

[Frozen queue A](queues/worker-1.json) · [Frozen queue B](queues/worker-2.json) · [Frozen queue C](queues/worker-3.json) · [Frozen queue D](queues/worker-4.json) · [Audit manifest](Pass.json)

The target applications are structured cases of the matrix, tensor and algebra equivalence problems studied in the tensor-isomorphism literature. The matrix certificate conclusions spell out algebraic identities. Degree bounds and interpretations in a Polynomial Calculus presentation are explained in the accompanying notes. [Grochow and Qiao on TI-completeness](https://arxiv.org/abs/1907.00309) · [Tensor isomorphism over rings](https://arxiv.org/abs/2611.00735) · [Polynomial Calculus and matrix conjugacy](https://arxiv.org/html/2305.19320#S7.SS3)
