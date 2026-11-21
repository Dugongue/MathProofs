# Grochow research catalogue proofs IV

This packet gives written arguments for **26 additional catalogue entries**. The 92 entries in the preceding three proof packets are excluded.

The count comprises 15 answers to the stated questions, 8 answers within an explicit model or parameter regime, and 3 exact complexity equivalences. The equivalences characterize the underlying difficulty and leave open the requested polynomial algorithm where the base problem remains open.

The bounded-degree quantum isomorphism reduction works at maximum degree 15 on connected graphs. The set-multilinear identity test saves enough arithmetic work to absorb the conversion from semantic input. [Quantum isomorphism](BoundedDegreeQuantumIso.md) · [Identity testing](SemanticSetMultilinearPIT.md)

[Proof dependencies](DAG-Connections.md) · [Lean verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0205](RealBorderRankMembership.md) | Euclidean real border-rank threshold is in the existential theory of the reals using a one-block algebraic separation bound. | proved result |
| [GP-0221](SegreSecantAlgorithms.md) | Polynomial-time generation of fixed-rank set-theoretic Segre secant equations, with an effective ideal-generation algorithm at fixed order. | proved result |
| [GP-0223](SegreSecantAlgorithms.md) | Compute exact degrees of Segre secants in polynomial bit time for fixed rank and order, including unequal formats. | proved with scope |
| [GP-0276](TensorOrderReductionBounds.md) | Equivariant polynomial order reductions require an output axis of dimension at least n^ceil(d/3). | proved with scope |
| [GP-0278](TensorOrderReductionBounds.md) | Deterministic exact fixed-format order reductions lose exponentially in output support density. | proved with scope |
| [GP-0303](OrbitDistanceHardness.md) | Inverse-polynomial-gap O and U tensor orbit-distance approximation is NP-hard even with simple, separated marginal spectra and connected support. | proved result |
| [GP-0370](PositiveEpimorphismApproximation.md) | For every fixed nonabelian simple target, a constant-factor randomized approximation on positive counts exists exactly if RP = NP. | proved result |
| [GP-0389](FaithfulSupportSetCover.md) | Listed faithful coset types give exact weighted Set Cover on direct powers of a fixed simple group, yielding NP-completeness in compact input. | proved result |
| [GP-0401](FaithfulLinearDimensions.md) | Minimum faithful complex dimension is NP-complete for compact class-two p-groups at each fixed prime, with polynomial-degree permutation generators. | proved result |
| [GP-0402](FaithfulLinearDimensions.md) | Minimum faithful rational dimension is NP-complete for compact permutation p-groups at every fixed prime. Rational versus complex dimension bounds are sharp at every exponent and center rank. | proved result |
| [GP-0417](MixedCohomologyRelatorBounds.md) | An r-relator Sylow presentation bounds H² by rd cyclic factors of explicitly bounded exponent, for arbitrary prescribed mixed-exponent actions. | proved result |
| [GP-0513](PermutationFamilyCanonization.md) | Singly exponential joint canonization of unordered compact permutation-group families via Wiebking's two canonizers. | proved result |
| [GP-0658](LinearDimensionNonassociative.md) | A universal explicit 2d-dimensional algebra over a transcendental evaluation extension detects free degree-d nonassociative polynomials over the base field. | proved with scope |
| [GP-0659](SuppliedAlgebraAndSemanticPIT.md) | Functional identity over a supplied finite algebra is coNP-complete. Formal identity over a supplied algebra is equivalent to commutative PIT. | proved with scope |
| [GP-0679](SemanticSetMultilinearPIT.md) | Deterministic t^(5d/6) times polynomial arithmetic work for semantic set-multilinear integer circuits, and a bit bound with bounded gate heights. | proved result |
| [GP-0682](SuppliedAlgebraAndSemanticPIT.md) | Semantic degree threshold with unbounded intermediate degree is many-one equivalent to PIT in the same promised circuit model. | exact comparison |
| [GP-0692](SuppliedAlgebraAndSemanticPIT.md) | One determinant tests full derivative-space rank. This gives randomized polynomial bit time and a deterministic equivalence to bounded-degree PIT. | proved with scope |
| [GP-0702](FrobeniusSparsePowerRecovery.md) | Inverse Frobenius reduces inseparable power reconstruction to the coprime exponent, with proper polynomial-time recovery for pure characteristic powers. | exact comparison |
| [GP-0742](QuotientTableIPS.md) | A correct one-dimensional quotient table leaves IPS search equivalent to general IPS search. Certified basis products suffice for efficient extraction. | exact comparison |
| [GP-0824](ModularHomomorphismTests.md) | Explicit test counts and maximum graph orders for modular-to-integral homomorphism dependence on bounded targets in the shift-lift families. | proved with scope |
| [GP-0916](CharacteristicUniformPC.md) | One explicit nonisomorphic graph family forces asymptotically sharp PC degree simultaneously in every fixed finite characteristic. | proved result |
| [GP-0921](FractionalTransporterRounding.md) | A fractional graph transporter with an entry strictly above one half in each row rounds to an isomorphism, and the threshold is sharp. | proved result |
| [GP-0923](HomomorphismSeparatorGenus.md) | Minimum separator Euler genus is uncomputable even at bounded degree. It has an O(n log n) upper bound and explicit linear lower bounds. | proved result |
| [GP-0958](BanicaHypergraphAction.md) | A uniform directed-hypergraph quantum group acts on the hypergraph C*-algebra and specializes exactly to Banica graph symmetry. | proved result |
| [GP-0959](HypergraphFreeWreath.md) | A directed hypergraph block substitution has an explicit free wreath product quantum automorphism formula. | proved with scope |
| [GP-0972](BoundedDegreeQuantumIso.md) | Finite-dimensional and commuting quantum graph isomorphism separate on connected graphs of maximum degree 15, where the commuting problem is undecidable. | proved result |
