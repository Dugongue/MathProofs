# Precise references and proof dependencies

**PROVED — confidence 0.99; reference record.** The cumulative proof uses the following external results only for the exact statements described below. Every further structural, arithmetic, and geometric claim used here is proved in the included chapters or is explicitly identified as user-stipulated background in the unchanged prior report.

## 1. Finite cyclic terms

**Libor Barto and Marcin Kozik (2012).** *Absorbing Subalgebras, Cyclic Terms, and the Constraint Satisfaction Problem*. Logical Methods in Computer Science **8**(1), article 07. **Theorem 4.1.** A finite idempotent Taylor algebra has a cyclic term of every prime arity greater than its cardinality.

Primary published PDF: <https://lmcs.episciences.org/673/pdf>.
DOI: <https://doi.org/10.2168/LMCS-8(1:7)2012>.

Application: the preceding structural and amplification chapters obtain the common cyclic operations on finite image sorts. The many-sorted product reduction and preservation under terms are proved there. The new witness chapter uses their proved all-prime generic-certificate conclusion and one fixed cyclic certificate; it makes no additional uncited cyclic-arity assertion.

## 2. Polynomial integer normal forms

**Ravindran Kannan and Achim Bachem (1979).** *Polynomial Algorithms for Computing the Smith and Hermite Normal Forms of an Integer Matrix*. SIAM Journal on Computing **8**(4), 499–507. **Theorem 2 and Lemma 3.** Used for polynomial square nonsingular Hermite computation with a polynomial-bit unimodular multiplier.

Publisher/DOI: <https://doi.org/10.1137/0208040>.

The theorem numbering was checked in the original-paper text reproduced at <https://studyres.com/doc/14829602/paper---math-tamu> and <https://studylib.net/doc/7924410/paper>. These are mirrors of the original paper, not additional theorem attributions.

Application: `Witness_bounds.md`, Lemma 9, gives the complete reduction from a rectangular integer system to that square Hermite computation and derives the full integer solution parametrization. The prior arithmetic appendix and general-algorithm chapter give the same reduction and the exact residue-image formula. Rational elimination bit bounds are stated and justified in those proofs. No assertion about general rectangular forms is left to an unspecified reference.

## 3. Fixed finite-domain CSP tractability

**Andrei A. Bulatov (2017).** *A Dichotomy Theorem for Nonuniform CSPs*. Proceedings of the 58th Annual IEEE Symposium on Foundations of Computer Science, 319–330. **Theorem 4, implication (2) to (1).** Used for the polynomial-time tractability of a fixed finite constraint language with a weak near-unanimity polymorphism.

Primary author PDF: <https://www.cs.sfu.ca/~abulatov/papers/focs17.pdf>.
DOI: <https://doi.org/10.1109/FOCS.2017.37>.

Application: `Witness_algorithm.md`, Proposition 5.3, proves that all the varying generic tables have bounded arity, are preserved by one common cyclic idempotent family, and therefore lie in one fixed finite language. It writes out the sorted-to-product reduction, the weak-near-unanimity identities, and the finite singleton-pin search reduction. The earlier general-algorithm chapter proves the corresponding statement for exact residue tables.

## 4. Optional older appendix reference

**Manuel Bodirsky, Barnaby Martin, Marcello Mamino, and Antoine Mottet (2018).** *The Complexity of Disjunctive Linear Diophantine Constraints*. 43rd International Symposium on Mathematical Foundations of Computer Science, LIPIcs **117**, article 33, 33:1–33:16. **Proposition 21** and **Theorem 22** are used in the optional older family chapter and archival audit, respectively for fixed finite Horn-template tractability and the binary-parameter quantifier-free Horn arithmetic algorithm. The new constructive theorem does not use this paper as an additional black box.

Primary published PDF: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.33/LIPIcs.MFCS.2018.33.pdf>.
DOI: <https://doi.org/10.4230/LIPIcs.MFCS.2018.33>.

## 5. Internal prerequisites reproduced in full

The following are internal theorem citations to earlier work in this same cumulative deliverable. They are not invented external publications.

| Needed statement | Complete proof location |
|---|---|
| Q implies block-generic operations | `prerequisites/chapters/N_next_structure.md`, Theorem 1 and Corollary 7.1 |
| Fixed certificate amplifies to all sufficiently large prime arities | `prerequisites/chapters/N_amplification.md`, Theorem II.8 |
| All-modulus sufficiency and finite criterion | That chapter, Theorems II.9–II.12 |
| Product lattice parametrization | `prerequisites/chapters/N_general_algorithm.md`, Lemma 3.2 |
| Exact finite residue relaxation and one fixed solver | That chapter, Lemmas 4.3–4.4 and Proposition 4.5 |
| Supported pp sets and computable hulls | That chapter, Lemmas 5.3–5.4 |
| Original-cell refinement and polynomial persistent data | That chapter, Lemmas 6.1–6.2 and Proposition 6.3 |
| Stable-state generic feasibility | That chapter, Lemmas 7.1–7.2; also reproved in `Witness_algorithm.md`, Theorem 6.2 |
| Prior decision theorem | That chapter, Algorithm 8.1 and Theorem 8.2 |
| Original shared-GC counterexample, including Q for every N | `prerequisites/chapters/N_next_counter.md` |

`N_Complete.md` reproduces the entire prior continuous report as Appendix P, so all these proofs are also available in one reading file.

## 6. No new external geometric theorem

**PROVED — confidence 1.00.** The integer root bound, constructive avoidance, common arithmetic-tail threshold, affine-basis construction, exact rational and real convex decompositions, affine-equality test, and objective trichotomy are proved in the new chapters. No generic appeal to a geometric theorem, compactness theorem, or unnamed “standard argument” is used to justify them. The implementation dependencies GMP and the optional Boost.Multiprecision backend are software choices, not citations offered in place of those proofs.
