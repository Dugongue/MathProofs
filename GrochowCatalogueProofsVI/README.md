# Grochow research catalogue proofs VI

This packet gives written arguments for **26 additional catalogue entries**. The 144 entries in the preceding five proof packets are excluded.

The count comprises 8 answers to the stated questions, 17 answers within an explicit model or parameter regime, and 1 exact complexity equivalences. Each proof states its input model and the conclusion it establishes.

The conormal multidegree bound extends to determinant pencils with repeated factors, with the original multiplicity as a weight. A single mixed quartic is complete for tensor orbit-closure intersection. A polynomial-time Cayley-table algorithm handles epimorphisms injective on an arbitrary marked subgroup when the target is a product of nonabelian simple groups and a finite abelian group. A dyadic growth bound on coefficient tests gives the sharp round order for colored cyclic groups in group WL Version I. [Reduced conormal bound](ReducedConormalBound.md) · [Mixed quartics](PureMixedQuarticTOCI.md) · [Marked quotients](MarkedQuotientSeparation.md) · [Colored cyclic groups](CyclicCountingWL.md)

Lean checks the two coset identities behind the update step in GP-0495. The catalogue results have written proofs.

[Proof dependencies](DAG-Connections.md) · [Verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0104](PresentedTensorOrder.md) | Reduce arbitrary-order dense presented tensors over a fixed finite commutative ring to free three-tensors and recover transporters. | proved with scope |
| [GP-0177](HybridOrthogonalTensor.md) | For both rational and real witnesses, sandwich hybrid orthogonal TI between bipartite graph isomorphism and same-field ordinary TI. | proved with scope |
| [GP-0256](PureSignatureDichotomy.md) | Classify fixed pure mixed signatures and tuples of individually balanced signatures for products of general linear groups. | proved with scope |
| [GP-0262](PureMixedQuarticTOCI.md) | Orbit-closure intersection for a single mixed quartic is TOCI-complete by an affine-linear embedding on three copies of the input space. | proved result |
| [GP-0263](SymmetricOrthogonalTOCI.md) | Orbit-closure intersection for one degree-15 symmetric form under the complex orthogonal group is TOCI-complete. | proved result |
| [GP-0274](SpecialUnitarySimpleSpectra.md) | Decide finite-field special-unitary transport and count the determinant orbit splitting when the three Hermitian Gram spectra are split and simple. | proved with scope |
| [GP-0322](MatroidSupportCycles.md) | Count labeled projective representation classes exactly over any finite field when the fundamental support is a cactus. | proved with scope |
| [GP-0323](MatroidSupportCycles.md) | Compare displayed matroids in fixed-parameter time in support cycle rank and test labeled projective rigidity with field size as an additional parameter. | proved with scope |
| [GP-0350](MarkedQuotientSeparation.md) | Construct a Cayley-table epimorphism injective on an arbitrary marked subgroup for targets that are products of nonabelian simple groups and arbitrary finite abelian groups. | proved with scope |
| [GP-0398](CharacterTableFaithfulDegree.md) | Compute the minimum faithful permutation degree of every odd-prime p-group from its ordinary character table with power maps. | proved with scope |
| [GP-0431](CyclicCountingWL.md) | One round of group WL Version II suffices for colored cyclic groups, and at sufficiently large fixed width the worst-case round order in Version I is log log n. | proved result |
| [GP-0495](DynamicCosetIntersection.md) | Return exact feasibility and a witness under online point-image constraints in polynomial update time after quasipolynomial preprocessing. | proved result |
| [GP-0534](LatinDepthTwo.md) | Compute the exact DNF size of Latin-square validity and prove a cubic CNF lower bound under a binary row-permutation promise. | proved with scope |
| [GP-0541](ModularSecantMembership.md) | Test fixed-degree, fixed-rank secant membership for both divided-power Veronese tensors and ordinary powers in positive characteristic. | proved with scope |
| [GP-0587](ReducedConormalBound.md) | Extend the ordinary and symmetric conormal bounds to all reduced components of a non-squarefree determinant pencil, weighted by their original multiplicities. | proved result |
| [GP-0596](SparseRationalInterpolation.md) | Deterministically reconstruct sparse rational functions of fixed individual degree from an exact oracle that reports poles. | proved result |
| [GP-0694](SuccinctLabelMatrixPIT.md) | Run deterministic noncommutative matrix hitting directly on ABPs with product-depth-bounded or log-depth binary DAG labels. | proved with scope |
| [GP-0703](HighPowerRoabpPIT.md) | Give deterministic white-box testing for high powers with variable-width ROABP bases and a polynomial-size hitting set for fixed width in one known order. | proved with scope |
| [GP-0718](AffinePpDegree.md) | Transfer polynomial calculus refutations through affine primitive-positive decoders with degree at most the maximum of the original degree and a fixed local bound. | proved with scope |
| [GP-0772](CoherentExponentiationAndFusions.md) | Determine the full automorphism group when Hamming adjacency is recognized from the fused valencies, with strict enlargement examples. | proved with scope |
| [GP-0773](CoherentExponentiationAndFusions.md) | For each d≥2 construct an algebraically isomorphic scheme with no exponentiation representation using d factors. | proved result |
| [GP-0777](CoherentExponentiationAndFusions.md) | A cut using at most c basis colors certifies that every primitive fusion has rank at most c+1. | proved result |
| [GP-0821](SparseCollisionCanonicalForms.md) | For an explicit two-member relation built from a forward permutation, randomized canonization implies average-case inversion, and efficient worst-case inversion suffices. | proved with scope |
| [GP-0874](WeightedDeckUniqueAnchors.md) | Reconstruct rationally weighted complete graphs at orders 3 and 4, and at every order when the unique-weight edges have minimum degree at least two. | proved with scope |
| [GP-0888](FiniteFieldGraphInvariantEvaluation.md) | Equate polynomial evaluation of polynomial-degree separating invariants over the fixed base field with a polynomial-time Boolean graph complete invariant. | exact comparison |
| [GP-0976](FiniteGroupReferenceProbes.md) | Construct a single polynomial-bit probe that identifies transporters for an explicit finite group action up to the scalar kernel. | proved with scope |

## Two corollaries

These follow directly from GP-0262 and are excluded from the main count.

- [GP-0254](PureMixedQuarticTOCI.md) TOCI-completeness for a mixed quartic plus a matrix.
- [GP-0255](PureMixedQuarticTOCI.md) TOCI-completeness for a single mixed sextic.
