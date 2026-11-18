# Functorial tensor reductions and structured group epimorphisms

Status: AI-assisted informal proofs, reviewed by separate workers. No Lean certification and no publication-priority claim. This packet develops four published research targets; it does not claim four complete published open-question closures. Earlier dependencies are included for inspection, with scientific citations preserved.

## What was established

| Published target | Exact result in this packet | Status of the published question |
|---|---|---|
| Grochow–Qiao, Open Question 7.5: functorial reductions and asymptotic spectra | Explicit all-linear-restriction functors from tensors to associative, commutative cube-zero, and class-two Lie algebras; further form and group directions with their stated conventions. Conversely, polynomial-dimension isomorphism-reflecting functors from all graph homomorphisms, or the stated algebra categories, to fixed-order all-covariant tensors are impossible. | Several specified positive and negative directions answered. The omnibus classification is not exhausted. |
| Grochow–Qiao–Stange–Sun, Part V, Section 1.4: characteristic-two Matrix Tuple Isometry | Polynomial symplectic transport with arbitrary isotropic quotient markings and full or partial quadratic data. Mixed natural/line-quotient affine transport for a one-vector stabilizer. Over the binary field, every invariant quotient of its natural isotypic module has a constructively recovered mixed presentation. | Sufficient cases only. The norm-lifting corollary retains a single symplectic residue block of dimension at least 10, at most two active Tate grades, and the specified first point stabilizer. |
| Grochow–Srivastava–Thakkar, Open Question 3(4): Abelian Sylow and tame-tower epimorphisms | Exact polynomial table-time decision, construction and counting for two-prime Abelian Sylow towers with equal-order complements, and more generally matched torsion-image flags or bounded total flag deficit. A separate small-orbit algorithm covers nonsplit extensions with invariant flags. | Full two-prime polynomial time, arbitrary towers and tame towers remain open. |
| Grochow–Srivastava–Thakkar, Open Question 3(3): genus-two epimorphisms | Exact polynomial ring-map counting from Frobenius complete intersections to arbitrary finite local target algebras with the same residue field. Recognition and transfer give polynomial Cayley-table epimorphism decision, construction and counting for the stated flat genus-two group source class. | The full genus-two question remains open. Source Frobenius complete-intersection and flat-bimap hypotheses are essential. |

## Proof files

- [Functorial reductions](Functors.md): object constructions, singular-arrow formulas, isomorphism reflection, field scopes, and the symmetric-cubic spectrum argument. Symmetric and alternating matrix-space morphisms use the explicitly specified shared-factor tensor convention. Conjugacy morphisms use intertwiners. Group outputs use compact matrix generators, not exponentially large Cayley tables.
- [Graph functor boundary](GraphFunctorBoundary.md): positive all-graph-homomorphism reduction into commutative cube-zero algebras and their unitizations, alongside a complete negative result for the ordinary all-covariant fixed-order tensor target.
- [General categorical boundary](CovariantLimits.md): the mutual-restriction support argument and precise spectrum conventions. These statements do not rule out isomorphism-only reductions or mixed-variance categories.
- [Characteristic-two affine isometry](Matrix.md): geometric algorithm, mixed-module transport, binary quotient classification, and exact remaining hypotheses.
- [Tower-group epimorphisms](Groups.md): complement flags, orbit method, bounded-deficit algorithm, and the equal-order-complement corollary.
- [Genus-two Frobenius sources](Genus.md): compact ring algorithm, raw-table recognition, centroid transfer, and exact group count.

## Audit and dependency records

[Genus audit](GenusAudit.md), [categorical audit](AllHomObstructionAudit.md), [graph boundary audit](GraphBoundaryAudit.md), and [tower-group audit](GroupsAudit.md) record separate mathematical reviews. The matrix note includes its independent review record. Reviews are not machine certificates or proof of novelty. The initial genus audit recorded display-format defects; those displays were corrected before staging without changing the mathematical statements.

The inherited [module algorithm](PriorModules.md), [flat genus-two correspondence](PriorGenus.md), [original matrix norm algorithm](OriginalMatrix.md), [marked-stabilizer continuation](Round2Matrix.md), and [point-stabilizer cocycle computation](Round3Matrix.md) supply the preceding proof context. The earlier [matrix audit](OriginalMatrixAudit.md) and [continuation audit](Round2MatrixAudit.md) are included. These are research notes with explicitly stated promises, not established general-purpose black boxes.

[check_genus.py](check_genus.py) compares the ring-count recurrence against direct generated-subalgebra tests on six small characteristic-three cases, totaling 444 image tuples. This finite check supports the implementation of the recurrence; it does not establish the universal theorem or benchmark a complete group solver.

## Primary problem statements and attribution

- [Grochow and Qiao, tensor-isomorphism reductions, Section 2.3 and Question 7.5](https://par.nsf.gov/servlets/purl/10494304).
- [Grochow, Qiao, Stange and Sun, Part V, Section 1.4](https://arxiv.org/html/2611.00735v1).
- [Grochow, Srivastava and Thakkar, Section 7, Open Question 3](https://arxiv.org/html/2609.07429v1#S7).
- [Skresanov, Proposition 3.9 and Proposition 4.2](https://arxiv.org/html/2605.26748v2), [Ciocănea–Teodorescu, finite-ring module algorithms](https://arxiv.org/abs/1512.08365), and [Babai–Qiao, Abelian Sylow tower isomorphism](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.453) supply cited algorithmic ingredients.
- [Brooksbank–Maglione–Wilson, genus-two definition](https://joshmaglione.com/papers/Genus2.pdf), and [Christandl–Fawzi–Ta–Zuiddam, symmetric spectra](https://arxiv.org/pdf/2104.01130) supply the stated frameworks.

All preceding constructions and external theorems remain credited in the proof files. This packet contains informal mathematical exposition and an original finite test script, not copied third-party implementation code. Whether any new assembly is already in the literature requires a separate priority search.
