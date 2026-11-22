# Four proposed fields of mathematics

These proposals specify their objects, what counts as the same object, and which general problems their invariants are meant to answer. Each has a written first theorem with an example that distinguishes its object from its closest established counterpart.

| Proposal | Defining object | First theorem |
| --- | --- | --- |
| [Simultaneous computability](SimultaneousComputability.md) | One shared input and a family of effective witness sets indexed by mathematical environments, with transport maps between them | Every monotone family of computably enumerable languages on a finite poset is realized by integral points of one bounded-format family of smooth hypersurfaces with integral local points everywhere. Finite realizability can fail to extend to all finite field extensions. |
| [Geometry of partially observed laws](PartiallyObservedLaws.md) | The geometric laws shared by every mathematical response consistent with prescribed probes | All $2m$-uniform hypergraphs occur as minimal concavity failures of a phase-moment response even with the lower marginals and moments fixed. |
| [Quantitative witness descent](QuantitativeDescent.md) | The joint budget and error frontier for one witness realizing all observations on a cover | Sparse adjacency eigenvalues give an exact width–error formula for positive semidefinite completions on transitive graphs. Even the unique exact completion and all local observation costs can agree while this frontier changes. |
| [Geometry of proof obstructions](ProofObstructionGeometry.md) | The functor of coefficient obstructions to certifying marked identities at each budget and after each base change | Every finite flag of closed obstruction schemes can occur, including nilpotents, over a constant smooth solution scheme. |

The manuscripts give closest established subjects and initial questions about realization, equivalence and composition. The first theorems are written proofs with provisional publication priority. Lean 4.33.0 separately checked the [coefficient retraction lemma](ObstructionRetraction.lean) for the fourth proof, using only the standard Mathlib axioms.
