# Grochow research catalogue proofs V

This packet gives written arguments for **26 additional catalogue entries**. The 118 entries in the preceding four proof packets are excluded.

The count comprises 9 answers to the stated questions, 13 answers within an explicit model or parameter regime, and 4 exact complexity equivalences. Each proof states its input model and the conclusion it establishes.

Three-tensor isomorphism for modules given by presentations reduces to one free-tensor instance over any fixed finite commutative ring. The tensor-train theorem gives a smoothness test covering simultaneous rank drops. The random-graph theorem gives the sharp polynomial-time reconstruction threshold for deck corruption. The squarefree fixed-algebra proof gives length 43 at the first nonsmoothable member of its family. [Presented modules](PresentedModuleTensorReduction.md) · [Tensor trains](LayeredABPTangents.md) · [Random decks](RobustRandomVertexDeck.md) · [Fixed algebras](VeroneseFixedAlgebra.md)

Lean checks two first-jet identities used in the branching-program proof. The fixed-algebra proof has four exact rank computations with a replayable checker. All catalogue results below have written proofs.

[Proof dependencies](DAG-Connections.md) · [Verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0092](CayleyTensorEncoding.md) | A linear-log-order class-two Cayley encoding over every fixed finite field, optimal for balanced objectwise encodings. | proved with scope |
| [GP-0095](PresentedModuleTensorReduction.md) | Presented-module and free three-tensor isomorphism are polynomial-time many-one equivalent over every fixed finite commutative ring. | proved result |
| [GP-0176](RationalPurificationTI.md) | Gaussian-rational mixed-state local unitary equivalence and three-factor unitary tensor isomorphism reduce to each other in polynomial bit time. | exact comparison |
| [GP-0184](VeroneseFixedAlgebra.md) | The complex squarefree third Veronese family first becomes nonsmoothable with seven variables, at length 43. | proved with scope |
| [GP-0253](DeterminantRankSeparations.md) | An explicit rank-one form gives exponential partition-to-raw-analytic rank separation, and the determinant has an exact fixed-field analytic rank formula. | proved result |
| [GP-0314](LcdNormalizationAndCanonization.md) | Over fields of size greater than three, reversibly normalize to an LCD code and recover ordinary monomial canonization from an LCD canonizer. | exact comparison |
| [GP-0332](MixedMetricCodeEquivalence.md) | Mixed Hamming and matrix-rank code equivalence with a compatible shared action is polynomial-time equivalent to tensor isomorphism. | exact comparison |
| [GP-0353](SemisimpleMarkedQuotients.md) | Count distinct marked quotient kernels in polynomial time for nonabelian semisimple Cayley-table targets. | proved with scope |
| [GP-0356](SemisimpleMarkedQuotients.md) | Find a maximum simultaneous image in polynomial time for nonabelian semisimple targets with optional square-free-exponent abelian direct factors. | proved with scope |
| [GP-0393](OptimalCoreFreeStabilizerCounting.md) | Counting optimal stabilizer conjugacy classes is #P-hard at every fixed odd prime even with an explicit optimum and a maximizing stabilizer. | proved result |
| [GP-0527](ReadOnceQuasigroupReachability.md) | Read-once parenthesized product reachability is NP-complete even for explicitly tabulated commutative quasigroups. | proved result |
| [GP-0529](ParallelQuasigroupWitnesses.md) | Uniform NC³ constructs polynomial-size straight-line membership witnesses in explicitly tabulated quasigroups. | proved result |
| [GP-0543](LayeredABPTangents.md) | An explicit cut-capacity test characterizes smoothness for fixed-order tensor-train varieties, including redundant caps and simultaneous rank drops. | proved with scope |
| [GP-0559](FiniteFieldProductRecovery.md) | Single products admit randomized polynomial reconstruction with extension-field queries, and distinct formal products can have identical base-field evaluations. | proved with scope |
| [GP-0561](StableThreeBlockReconstruction.md) | Reconstruct real three-block depth-three circuits from bounded coefficient noise under explicit separation and conditioning assumptions. | proved with scope |
| [GP-0563](BorderDepthFourChunking.md) | Give growing-bottom-degree bounds for the elementary symmetric polynomial and match them in the chunk-aligned border model. | proved with scope |
| [GP-0567](BinaryWaringMultiplicities.md) | Compute representation multiplicities of binary Waring secants in time polynomial in the numerical degrees and secant rank. | proved with scope |
| [GP-0598](LacunaryFactorRecovery.md) | Recover the bounded-individual-degree rational factor set with high probability, with expected output-sensitive time for sparse expansion. | proved with scope |
| [GP-0782](CoherentBaseAndFiberLifting.md) | Give an intersection-number certificate that the fibers of a coherent configuration determine all pair colors. | proved result |
| [GP-0812](CoherentBaseAndFiberLifting.md) | Lift prescribed color isomorphisms in polynomial time on coherent configurations of bounded fiber size, including nonseparable homogeneous examples. | proved result |
| [GP-0877](RobustRandomVertexDeck.md) | With high probability a dense random graph has sharp polynomial-time vertex-deck recovery threshold 2e+f≤n−3 for e replacements and f erasures. | proved result |
| [GP-0973](GraphStatePermutationHardness.md) | Permutation-allowed graph-state local-unitary equivalence is GI-hard and is GI-equivalent on the recognizable two-private-leaves family. | proved with scope |
| [GP-0974](GraphStateMonomialTransport.md) | Compute compact local and permutation-allowed graph-state stabilizers when two-body marginals isolate local Pauli axes. | proved with scope |
| [GP-0975](GraphStateMonomialTransport.md) | Decide simultaneous graph-state transport when a qualifying anchor forces monomial local unitaries. | proved with scope |
| [GP-0994](FixedFieldSurfaceThreshold.md) | Rational-weight orientable surface localization and fixed-prime weighted difference constraints have the same approximation threshold. | exact comparison |
| [GP-0999](RelativeHomologyFPTAS.md) | A deterministic FPTAS minimizes binary relative homology support on fixed-genus orientable surfaces with arbitrarily many boundary components. | proved result |

## Lean supplement

[GP-0542](LayeredABPTangents.md) receives two Lean-checked supporting identities. The previously answered entry is excluded from the count.

## Literature updates

These results are credited to the cited authors and excluded from the proof count.

- [GP-0251](DeterminantRankSeparations.md) Chen and Zhao prove that the determinant has partition rank d-o(d), uniformly over fields.
- [GP-0252](DeterminantRankSeparations.md) Chen and Zhao obtain a linear-order partition-to-geometric rank separation.
