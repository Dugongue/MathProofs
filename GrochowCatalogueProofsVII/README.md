# Grochow research catalogue proofs VII

This packet gives written arguments for **26 additional catalogue entries**. The 170 counted entries in the preceding six proof packets are excluded.

The count comprises 5 answers to the stated questions and 21 answers within an explicit model or parameter regime. Each proof states its input model and the conclusion it establishes.

The regular determinantal complexity of the generic determinant is at least quadratic, giving explicit forms with a quadratic exact-versus-border gap. The code survey's universal equivariant partner fails over every finite field, and an invariant complement characterizes the code orbits admitting one. Minimum common refinement is polynomial-time for two jointly faithful actions and NP-complete for three. The dyadic lifting algorithm tracks the full stabilizer coset inside a prescribed residue class. [Determinantal gap](DeterminantalJetRankGap.md) · [Code partners](MonomialDualPartner.md) · [Common refinements](CommonPermutationRefinement.md) · [Dyadic lifting](DyadicPrescribedResidueTransport.md)

Lean checks two identities used in the repetition-code obstruction in GP-0313. The catalogue results have written proofs.

[Proof dependencies](DAG-Connections.md) · [Verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0102](DyadicPrescribedResidueTransport.md) | Lift a prescribed mod-2 tensor and isometry transporter residue, retaining a compact description of the full compatible coset. | proved with scope |
| [GP-0166](CharacteristicTwoGramSpectrum.md) | Give exact squarefree-spectrum probabilities for the standard characteristic-two dot-product Gram at every rectangular width. | proved with scope |
| [GP-0168](RandomAnchorRankThreshold.md) | Find the low-rank anchor threshold with joint spectral projectors and exact rank-one laws for squarefree spectra. | proved with scope |
| [GP-0267](RectangularWidthTwoOCI.md) | Classify rectangular two-slice product-SL orbit closures by one determinant or a trivial invariant ring. | proved with scope |
| [GP-0281](ExactGramRenyiLaws.md) | Compute exact densities and all Rényi divergences of alternating and Hermitian Gram laws for individual uniform tensor flattenings. | proved result |
| [GP-0285](SquareZeroRadicalOrbits.md) | Lift supplied classical top transporters through square-zero commutant radicals in all characteristics. | proved with scope |
| [GP-0302](RankOneSpectralBlockTransport.md) | Give polynomial orthogonal and unitary transport with rational spectra and growing rank-one spectral blocks. | proved with scope |
| [GP-0313](MonomialDualPartner.md) | Rule out a universal monomial-equivariant dual partner over every finite field and characterize the code orbits admitting one. | proved result |
| [GP-0335](PrimeFieldBlockTransport.md) | Recover semilinear transport from additive block witnesses using chord subfields and compatible Frobenius exponents. | proved with scope |
| [GP-0339](ChainRingDiagonalTransport.md) | Find all diagonal lifts of a prescribed permutation over a chain ring with unrestricted Smith types. | proved with scope |
| [GP-0355](UniformQuotientKernels.md) | Sample exact uniform quotient kernels for targets that are products of nonabelian simple groups and arbitrary finite abelian groups. | proved with scope |
| [GP-0357](CommonGenusOneQuotients.md) | Find a largest common odd-exponent-p quotient with commutator dimension at most one and output both quotient maps. | proved with scope |
| [GP-0412](LocalCocycleCompletion.md) | Extend exact local cocycles to a compact evaluator on an elementary abelian quotient with arbitrary same-characteristic action. | proved with scope |
| [GP-0497](CommonPermutationRefinement.md) | Optimize common refinements of two jointly faithful actions in polynomial time and prove NP-completeness for three. | proved with scope |
| [GP-0579](DeterminantalJetRankGap.md) | Prove that every affine representation of the generic s-by-s determinant that has corank one at zero has size at least 1+ceil(s²/2). | proved result |
| [GP-0580](DeterminantalJetRankGap.md) | Determine the quadratic asymptotic size needed to match all second-order Koszul coefficient data under regularity. | proved with scope |
| [GP-0600](QuantitativeCoprimeFactorLifting.md) | Bound numerator and denominator parameter degrees in coprime factor lifting with circuit size independent of input parameter degree. | proved with scope |
| [GP-0670](CanonicalCommutativeSemisimplification.md) | Construct a canonical closed rational representative of matrix tuples with commutative semisimplification. | proved with scope |
| [GP-0746](ReadAbpTreewidthPIT.md) | Decide exact white-box PIT for read-k oblivious ABPs in polynomial time at fixed adjacency treewidth. | proved with scope |
| [GP-0760](SuccinctDimensionTesting.md) | Reduce dimension testing for unrestricted division-free circuits to explicit quadratic systems with a fixed counting-hierarchy bound. | proved result |
| [GP-0770](IntrinsicCoherentExponentiation.md) | Show that group exponentiation does not descend to orbital configurations and characterize sufficient orbit data. | proved result |
| [GP-0771](HammingFusionRankSearch.md) | Enumerate Hamming fusions with product coordinates in fixed-parameter time in the configuration rank. | proved with scope |
| [GP-0823](SmallMinorHomIndependence.md) | Show that every connected forbidden minor on at most four vertices has an independent homomorphism count, giving a minimum order lower bound of five. | proved with scope |
| [GP-0875](FPTDeckRecognition.md) | Recognize vertex decks and list all preimages in fixed-parameter time in the smallest twin-class count of any card. | proved with scope |
| [GP-0883](ReturnWalkCanonization.md) | Canonize graphs when diagonal spectral projectors distinguish twin classes, even with repeated eigenvalues and unbounded quotient size. | proved with scope |
| [GP-0998](HomologyWidthBinaryPrime.md) | Give an exact width algorithm and prove binary-prime NP-hardness at constant width under Las Vegas reductions. | proved with scope |

## Additional proofs

The application and the refinement below are outside the main count.

- [GP-0577](DeterminantalJetRankGap.md) The regular lower bound and the published restriction give degree-n forms with border size n and exact size at least 1+ceil((n−6)²/2).
- [GP-0886](DegreeTwoOrbitSeparation.md) For n≥6 the separation degree on maximum-degree-two graphs is exactly ceil(n/2).
