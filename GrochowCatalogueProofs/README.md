# Proofs for the Grochow research catalogue

Written proofs, reductions, or explicit counterexamples answer **37 catalogue entries**. The proof packets cover 9 tensor and algebra targets, 12 group and code targets, 8 algebraic-complexity targets, and 8 graph and quantum targets.

GP-0349 addresses Elder–Shen–Weiß's open problem on epimorphisms to the dihedral group of order eight. The construction also gives NP-completeness of Angela Wuu's Homomorphism Extension problem at fixed target degree eight. [Dihedral proof](DihedralEpimorphism.md) · [Extension and counting proofs](HomomorphismExtension.md)

The collection includes direct applications of classical algorithms and extensions of proofs already in MathProofs. Related entries can share a construction, as with the dihedral counting results and the quantum graph pair. The index counts catalogue questions, and does not claim priority for each argument.

[DAG connections](DAG-Connections.md) · [Lean and finite verification](Verification.json) · [Machine-readable resolutions](Resolutions.json)

| Catalogue ID | Result at its proved scope |
| --- | --- |
| [GP-0076](SquareZeroAlgebras.md) | Graph-isomorphism equivalence. Deterministic over each fixed finite field and Las Vegas with variable field. |
| [GP-0084](BoundedWidthGradedLie.md) | Grade-preserving isomorphism is FPT in width for a fixed finite field and in width plus field bit length uniformly. |
| [GP-0091](IntegralCancellation.md) | Exact stable cancellation criterion, cancellation at torsion exponents 1, 2, 3, 4, and 6, and failure with 5-torsion. |
| [GP-0108](LocalStabilizers.md) | Generators and reduction kernel in polynomial bit time for the recognized split block-scalar class at fixed prime. |
| [GP-0194](SecantDegreeTest.md) | The universal strict-improvement claim fails already at the rank-one Segre secant. |
| [GP-0241](PfaffianRecovery.md) | Polynomial witness recovery for recognizable split symplectic block spaces with labelled scheme factors. |
| [GP-0247](QuadraticRefinements.md) | TI equivalence in characteristic two with arbitrary output mixing, even with injective polarization. |
| [GP-0277](SchemeReduction.md) | Fixed-order reduction that explicitly preserves stabilizer group schemes up to described factors. |
| [GP-0279](RankControlledReduction.md) | One ordinary 3-TI instance of rank polynomial in the input rank and tensor order, without rank decompositions. |
| [GP-0336](GroupCatalogueClosures.md) | Graph-isomorphism hardness already with zero repeated projective columns. |
| [GP-0349](DihedralEpimorphism.md) | Epimorphism from finite presentations onto D8, and every fixed nonabelian dihedral group, is NP-complete. |
| [GP-0362](GroupCatalogueClosures.md) | Deterministic feasibility and expected-polynomial exact uniform sampling on the prescribed central quotient. |
| [GP-0377](HomomorphismExtension.md) | Counting up to the marked action's centralizer is #P-complete, even with target S8. |
| [GP-0379](HomomorphismExtension.md) | Joint extension is NP-complete for a target of degree eight and one orbit per marked action. |
| [GP-0381](HomomorphismExtension.md) | Counting block-preserving extensions is #P-complete with one fixed eight-point block. |
| [GP-0477](GroupCatalogueClosures.md) | Sparse alternating presentations can force quadratic witness density. |
| [GP-0479](GroupCatalogueClosures.md) | Identical rank-drop schemes over every extension can hide different class-two group types. |
| [GP-0498](GroupCatalogueClosures.md) | Minimum-support threshold is NP-complete for every fixed exponent at least two. |
| [GP-0501](GroupCatalogueClosures.md) | Polynomial-delay enumeration of maximal proper normal subgroups via chief factors. |
| [GP-0503](GroupCatalogueClosures.md) | Uniform NC reachability and pointwise stabilizer computation for a supplied quotient coset. |
| [GP-0535](GroupCatalogueClosures.md) | Uniform AC⁰ recovers every missing entry with one hole per Cayley-table row. |
| [GP-0542](algebraic-algorithms.md) | Generic tangent vectors of layered ABP varieties need at most double width at the same depth. |
| [GP-0549](algebraic-algorithms.md) | Compute intersection bases of circuit-described spaces in bounded-error polynomial arithmetic time without dense expansion. |
| [GP-0605](algebraic-algorithms.md) | Newton faces preserve same-order ROABP width over every field, including with internal cancellations. |
| [GP-0640](algebraic-algorithms.md) | Compute the minimum degree of matrix-entry TPP separators by incrementally building evaluation spaces. |
| [GP-0686](field-and-invariants.md) | A degree-one separator can exist even if no invariant polynomial separates its marked point from the closed set. |
| [GP-0711](field-and-invariants.md) | PIT with circuit-encoded rational-function constants is equivalent to unrestricted-degree PIT over the constant field. |
| [GP-0712](field-and-invariants.md) | Finite-field IPS descent costs quasi-linear size in the certificate gate count times the extension degree. |
| [GP-0743](geometric-ips.md) | Bounded-incidence-treewidth Boolean CSPs have polynomial-size division-free Geometric IPS certificates. |
| [GP-0865](GraphClosures.md) | Quadratic adjacency-access query bound persists even with unlimited preprocessing. |
| [GP-0927](GraphClosures.md) | Polynomial explicit cycle index for diameter at least two. Diameter one can have superpolynomial output. |
| [GP-0950](GraphClosures.md) | Unlabeled affine orbits give no seed bound except in the trivial and two-point cases. |
| [GP-0952](GraphClosures.md) | A quantum fractional automorphism set is polyhedral exactly when it is the classical automorphism convex hull. |
| [GP-0954](GraphClosures.md) | Connected quantum-isomorphic graphs can have quantum fractional automorphism sets with different affine types. |
| [GP-0955](GraphClosures.md) | Quantum graph isomorphism does not preserve polyhedrality. |
| [GP-0956](GraphClosures.md) | The quantum automorphism group of the complete directed hypergraph is the classical symmetric group. |
| [GP-0957](GraphClosures.md) | Every finite directed hypergraph quantum automorphism group has a Banica graph realization. |

GP-0968 is recorded as previously answered by the literature. GP-0335 receives a counterexample to unrestricted lifting from one additive transporter and a promise repair. These are outside the count. [Graph audit](GraphClosures.md) · [Group audit](GroupCatalogueClosures.md)

A further extension covers fixed nonabelian targets with prime-square central index. [Additional epimorphism theorem](PrimeSquareCentralIndex.md)
