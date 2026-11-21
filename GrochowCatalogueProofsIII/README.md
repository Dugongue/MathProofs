# Grochow research catalogue proofs III

This packet gives written arguments for **25 additional catalogue entries**. The 67 entries in the preceding two proof packets are excluded.

The count comprises 13 answers to the stated questions, 8 answers within an explicit model or parameter regime, and 4 exact complexity equivalences. The equivalences characterize the underlying difficulty and leave open the requested polynomial algorithm where the base problem remains open.

The lead result builds polynomial-size hitting sets for bounded Hasse derivative spaces over every fixed finite field. A multiplicative difference equation supplies a rank-dependent series truncation bound. [Proof](HasseDerivativeHitting.md)

[Proof dependencies](DAG-Connections.md) · [Lean verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0146](OrthogonalSeedSampler.md) | Explicit dense polylog-seed sampler with exact orbit dispersion and an all-target orthogonal algorithm over F5. | proved in a stated model |
| [GP-0237](MatrixSpaceClassifications.md) | TI-complete even with matched invertible anchors, so a polynomial algorithm here would give one for ordinary TI. | exact complexity equivalence |
| [GP-0242](MatrixSpaceClassifications.md) | The singular, common-radical-zero promise is polynomially equivalent to unrestricted alternating-space pseudo-isometry. | exact complexity equivalence |
| [GP-0248](MatrixSpaceClassifications.md) | TI-complete even for matrix spaces generating the same full algebra, with either conjugation or left-right equivalence. | exact complexity equivalence |
| [GP-0333](SimultaneousIsoduality.md) | Monomial code-equivalence complete with one target instance, already for three individually isodual codes. | exact complexity equivalence |
| [GP-0338](SelfOrthogonalPuncturing.md) | The binary problem is NP-complete, parameterized equivalent to binary k-VectorSum, and has no PTAS unless P = NP. | proved in a stated model |
| [GP-0358](CentralExtensionLifts.md) | Polynomial-time onto lifting with prescribed quotient action, arbitrary abelian p-power central heights, and explicit compact coordinates. | proved in a stated model |
| [GP-0360](AlternatingEpimorphisms.md) | NP-complete to test surjection onto the fixed Heisenberg group of order p³ for every fixed odd prime p. | proved answer |
| [GP-0361](AlternatingEpimorphisms.md) | Sharp 3/2 approximation for the fixed Heisenberg target. General targets rule out every ratio below 2 and every fixed additive error unless P = NP. | proved in a stated model |
| [GP-0380](CosetHomomorphismExtension.md) | Coset-constrained homomorphism extension is NP-complete at index two with one mark, and polynomial at index one. | proved answer |
| [GP-0471](LazardSubgroupConjugacy.md) | Bit-polynomial subgroup conjugacy for compact class-c p-group presentations with c below p. | proved answer |
| [GP-0473](MinimalCentralAmalgam.md) | Exact minimum ambient-order formula for the prescribed central gluings, with NP-complete compact threshold decision. | proved answer |
| [GP-0611](ROABPSparsityLifting.md) | One explicit substitution forces middle ROABP width exactly equal to input sparsity in every order and over any field. | proved answer |
| [GP-0612](PrimitiveNewtonSummands.md) | Polynomial-time primitive summand search would imply P = NP even for explicit bivariate vertex-monomial circuits with polynomial-size promised output. | proved answer |
| [GP-0677](GeometricEquationHitting.md) | Uniform unsatisfiable 3-CNFs hit all quadratic polynomials in the equation coordinates, with a universal degree-12 obstruction for larger classes. | proved in a stated model |
| [GP-0685](GroupedReadOnceRecovery.md) | Deterministic bit-polynomial black-box reconstruction of a grouped read-once rational formula, allowing singleton output groups. | proved answer |
| [GP-0691](HasseDerivativeHitting.md) | Explicit polynomial-size Hasse derivative hitting sets over every fixed finite field, with a logarithmic-degree evaluation extension. | proved answer |
| [GP-0738](TensorOrbitProofDegree.md) | Ordinary GL orbit closures always meet. In the SL version, concise tensors separate linear from constant PC degree at identical cubic formats. | proved answer |
| [GP-0940](InducedMotifAlgorithms.md) | Exact counts for supplied bounded rank-width with fixed-parameter dependence and almost-linear host dependence. | proved answer |
| [GP-0941](InducedMotifAlgorithms.md) | Tight quadratic-bit one-pass adversarial insertion-only space on fixed triangles, even with zero pendant types. | proved in a stated model |
| [GP-0942](InducedMotifAlgorithms.md) | Exact dynamic motif counting in logarithmic amortized updates for bounded core size and fixed motif. | proved answer |
| [GP-0944](InducedMotifAlgorithms.md) | Canonical reuse of weighted and directed pendant rooted attachments via relative-boundary pattern tables. | proved in a stated model |
| [GP-0995](FlatSurfaceConstraints.md) | Fixed transitive actions have a hard constant-factor gap on flat triangulated surfaces exactly when the alphabet has more than one point. | proved answer |
| [GP-0996](FlatSurfaceConstraints.md) | Exact factor-six optimum transfer into uniformly bounded-degree closed orientable flat triangulations using the original action. | proved answer |
| [GP-1000](IncidenceHomologicalCuts.md) | An exact fixed-parameter algorithm in incidence width at each fixed finite field for persistence-class deletion. | proved in a stated model |

## Credited literature results

- [GP-0112](NovemberLiteratureResolutions.md) · Dicke entropy law, including repeated species. This packet also gives the coefficient-one all-field transfer.
- [GP-0114](NovemberLiteratureResolutions.md) · A four-mode counterexample to irreducibility of all asymptotic-rank sublevels.
- [GP-0197](NovemberLiteratureResolutions.md) · An explicit family of secants of three-factor Segre varieties that fail S2 and Cohen–Macaulayness.
- [GP-0232](MatrixSpaceClassifications.md) · Already classified as TI-complete by Grochow and Qiao. This packet supplies the square-zero reduction used in the new promise results.

## Additional scoped results

- [GP-0818](UnaryCAStructuralCertificates.md) · All-length finite test when the source is a shift followed by a unary map.
- [GP-0998](VariablePrimeHomology.md) · Variable-prime hardness at constant incidence width and fixed-field bounds.
- [GP-0110; GP-0118](GraphCutWeightedEquivalence.md) · Exact equivalence of the two universal MaxCut conjectures.
- [GP-0147](ClassicalTransporterFieldDegree.md) · An exact factorial transporter field degree for an explicit family of rational orthogonal tensors.
- [GP-0170](EquivariantFormRecovery.md) · A scalar obstruction for literal bilinear-form recovery over fields larger than three.
