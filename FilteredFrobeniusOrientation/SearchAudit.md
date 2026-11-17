# Search and scope audit for the determinant TI chain

**Outcome:** no new equivalence between previously unmerged unrestricted catalogue degrees was established. The positive result retained from this run is [determinant cancellation for filtered Frobenius algebras](FrobeniusOrientation.md), an informal sufficient reduction for explicitly recognized families. It is not presented as closing the published TI versus SL-TI question.

## The unchanged target

Over F₃, let O be ordinary three-tensor isomorphism, A first-mode determinant-one isomorphism, B determinant-one isomorphism in two modes on the same transporter, and S special-linear tensor isomorphism. The existing research chain remains

    O ≤ₘᵖ A ≤ₘᵖ A∧A ≤ₘᵖ B ≤ₘᵖ S.

The problem in this run was to prove a new reverse deterministic polynomial-time many-one reduction. Existing constant-query reductions already identify A, B and S under polynomial-time Turing reductions. That older fact is not a new many-one collapse.

A universal binary pack A∧A ≤ₘᵖ A would suffice to merge all signed tiers, using the existing seven exact character tests for S. This construction was not obtained. Nor was a new merge of the remaining Frobenius, shared-reference, odd-stabilizer, quadratic-extension or plane-balance degrees obtained.

## Search coverage

Work was performed by one researcher without delegated agents. The saved private search ledger contains:

- Seventeen federated query runs across all 103 registered source catalogues, the existing checked-declaration index and the notes index. The returned source lists contained 730 records, including repeated snapshots and unrelated names.
- A no-limit notes-index conjunction query with 179 matching documents, followed by focused source and hypothesis inspection.
- Topic scans of active research, the canonical project, relocated notes, historical scratch work and backup locations across four storage volumes. The combined manifests contain 16,525 distinct path strings; 2,801 also match the narrower topic-name filter. These are path counts, not counts of different proofs or files read in full.
- Focused canonical-project scanning found 646 matching source files. Research-directory scans found 1,643 and 3,861 matching files in the two principal research collections, plus 175 in the relocated collection.
- Primary-source searches of arXiv, author publication pages, conference proceedings and the relevant algebra literature, together with GitHub and Hexagon searches.

**This was a broad multi-layer search, not an exhaustive semantic review of every file or theorem.** Federated query result caps were 45 or 100. Seventeen per-query error entries were recorded, mostly time-budget interruptions on large historical catalogues. Five broad storage-root scans timed out; narrower scans subsequently covered the principal research and relocated directories. Some temporary dependency/test directories were inaccessible, and one reserved-name test fixture could not be read. Backup, cache and source-snapshot duplicates were not treated as independent evidence. No absence-of-proof conclusion is inferred from search limits.

## The closest reuse candidates and their exact scope

| Candidate | What the inspected material actually supplies | Consequence for the target |
| --- | --- | --- |
| `target_of_conjunctive` | Composition in an abstract reduction system, given both a conjunction compiler and the reduction into it | It does not construct either missing signed query. |
| `searchToDecision_of_canonicalLabelling` | Search assuming an appropriate canonical labelling | It is not an unrestricted ordinary-TI search algorithm. |
| Matrix-tuple canonical forms | Two moving modes, with tuple labels fixed | Allowing arbitrary changes of the third mode remains additional work. |
| Exterior determinant identities | Exact action on the top exterior power | They do not provide a polynomial-size low-order tensor realization of all intermediate exterior data. |
| Ordinary neutral conjunction | An ordinary comparison can be attached without altering the live signed comparison | Two independent signed comparisons are not covered. |
| Span-parity compiler | Linear feasibility with columns enabled by ordinary TI comparisons | Replacing an ordinary enabling predicate by a signed predicate is not justified. |
| Signed tensor-system compiler | A system can be compiled while retaining one specified determinant character | It retains one constraint; it does not turn two independent constraints into one. |
| Existing Frobenius connected sums | Preserve a live sign while absorbing ordinary conditions | They do not turn arbitrary local algebras into Frobenius algebras with the same sign. |
| Compressed-algebra structure | Perfect pairings and symmetric-power grade actions | These yield the positive result in the companion proof, with the precise parity conditions stated there. |

The actual Lean statements and surrounding assumptions were inspected for the selected reuse candidates. Discovery records and historical verification labels were kept separate from current kernel checking. No new Lean compilation or axiom audit was performed in this informal run.

## Literature assessment

[Chen, Grochow, Qiao, Tang and Zhang](https://arxiv.org/html/2306.03135v2) give the ordinary tensor-system compiler used in the companion reduction and state the motivating special-linear containment question. A determinant constraint cannot simply be appended as an arbitrary polynomial equation and declared to be an ordinary tensor system.

[Grochow and Qiao's linear-length reductions](https://arxiv.org/abs/2306.16317) include search/counting-to-decision consequences in the Cayley-table group model. The representation size and reduction type must be preserved when transferring those statements; a polynomial bound in group order is not a polynomial bound in a short tensor description.

[Bläser, Dutta and Okyay](https://arxiv.org/abs/2606.16744) distinguish invertible-matrix equations from a generalized special-linear existential theory. The latter permits extra linear constraints and has a real-field hardness result. Neither that theorem nor the former algorithm supplies the missing finite-field tensor reduction.

[Gordeev and Popov](https://annals.math.princeton.edu/2003/158-3/p08) realize algebraic groups as automorphism groups of finite-dimensional algebras under field hypotheses. The existence statement alone gives neither the required polynomial size nor a compatible realization of the original tensor action over F₃.

The useful new synthesis came from standard Frobenius duality and symmetric-power determinant identities. [Jelisiejew](https://arxiv.org/abs/1511.08007) warns through characteristic-three counterexamples that canonical grading cannot be silently assumed. The companion proof avoids that assumption by working on the intrinsic radical filtration. [Hermitian K-theory via oriented Gorenstein algebras](https://hoyois.app.uni-regensburg.de/papers/gorenstein.pdf) includes the standard annihilator/orthogonal-complement identity; its use of “orientation” means a Frobenius functional, not automatically the determinant-one condition studied here.

No retrieved source established the missing universal packing construction. This is a report of what was found, not a claim that such a result is absent from all literature. Novelty of the companion synthesis remains unverified.

## Retained sufficient theorem

The companion proof reduces the first-determinant test to one ordinary TI comparison for scalar-residue commutative Frobenius algebras in each of three cases: odd total dimension; symmetric Hilbert function of odd socle degree; or compressed even socle degree with even specified binomial exponent. It includes raw recognition, independent frame calibration, all unit factors in multiplication isotopies, and the single ordinary-query output.

The finite controls passed 450 determinant cases, ten complete quartic algebra-isomorphism checks and 10,744 basis associativity checks. These controls support the stated formulas but do not replace the written universal proof. The result enlarges a solved subfamily inside the existing Frobenius branch. It does not establish a new unrestricted tier collapse or a published open-problem closure.
