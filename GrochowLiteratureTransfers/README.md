# Four algorithmic results for tensor and group isomorphism

These results address scoped parts of questions from Joshua A. Grochow’s collaborations. Each statement is a proved algorithm or exact count under explicit input hypotheses. The question numbers are from the papers.

| Question | Result |
| --- | --- |
| Part III, Open Question 1.9 | [Prescribed determinants over prime-power rings](PrescribedDeterminants.md). Polynomial bit-time decision and exact counting for ordered slices of arbitrary width, with arbitrary compact ring exponent and fixed residue prime. This yields full three-mode determinant-one decision and counting when $\tau r^2=O(\log L)$. |
| Part V, §1.4 | [Dyadic matrix tuple isometry](DyadicTupleIsometry.md). Polynomial bit-time decision, search and counting with an invertible common anchor and a commutative commutant. Covers characteristic-two finite fields and compact $\mathbb Z/2^\tau\mathbb Z$. |
| Part III, Open Question 1.8 | [Compact tensor isomorphism](TwoSimpleSpectra.md). Two simple marginal spectra suffice. One simple marginal also suffices when a family of weighted Gram matrices has scalar commutant. The real rational decision bound is polynomial bit time. The complex bound is in the exact arithmetic model. |
| Group Epimorphism, Open Questions 2 and 3(5) | [Central epimorphism counts](CentralEpimorphisms.md). Polynomial table-time decision, search and exact counting for central radicals and products of nonabelian simple quotient factors when the target radical has bounded generator number, allowing unbounded repeated simple factors. For elementary abelian radicals, bounding either intersection with the derived subgroup also suffices. |

The [literature search](Literature.md) identifies the recent input to each proof and nearby results. The full algorithms are proved in prose. [GrochowIsomorphism20261120.lean](GrochowIsomorphism20261120.lean) checks four lemmas used in the arguments, covering the character coset, the norm equation, equality of Gram linear relations, and uniqueness of the central lift. Lean 4.33.0 with Mathlib at the [recorded commit](Verification.json) verified their kernel terms and transitive axioms. The complete algorithmic bounds and the unrestricted source questions remain outside that formal verification. The [exact controls](check_controls.py) test small instances and can be run with Python 3.10 or newer.

Priority is undetermined. These statements are scoped results on the listed questions. The unrestricted determinant-one reduction, characteristic-two isometry algorithm, compact reduction and epimorphism problems remain open here.
