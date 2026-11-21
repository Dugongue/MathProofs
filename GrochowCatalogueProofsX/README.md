# Grochow research catalogue proofs X

This packet gives written arguments for **24 additional catalogue entries**. The 239 counted entries in the preceding nine proof packets are excluded.

Each proof specifies the model or parameter regime in which its conclusion holds.

Special-linear tensor isomorphism is decidable in polynomial bit time when one slice space has maximum rank two. Exact formulas count complements for extraspecial kernels in class-two groups. In the same compact group model, alternating-form ranks determine the smallest faithful degree with normal point stabilizers. A dimension-preserving reduction gives no computable finite witness bound for graph quantum isomorphism at coherent multiplicity four. It preserves the witness dimension exactly. [Upper-rank-two SL-TI](UpperRankTwoSpecialLinear.md) · [Complement counts](ExtraspecialComplementCounts.md) · [Normal faithful degree](NormalFaithfulDegreeClassTwo.md) · [Quantum witness dimensions](CoherentMultiplicityFourWitnesses.md) · [Squarefree cubic decompositions](SquarefreeCubicDecompositions.md)

Lean independently checks two coset-representative identities used in the parallel Schreier transversal proof. The catalogue results have written proofs.

[Proof dependencies](DAG-Connections.md) · [Verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0216](SquarefreeCubicDecompositions.md) | Classifies all shortest ordinary decompositions of the squarefree cubic tensor by projective sign choices. | degree three and characteristic other than two |
| [GP-0229](PencilStabilizerOrders.md) | Exact left-right stabilizer order by endomorphism-ring units and projective support symmetries. | arbitrary finite-field matrix pencils, deterministic bit time |
| [GP-0234](RankTwoMatrixSpaceEquivalence.md) | Deterministic bit-polynomial recognition and left-right equivalence of matrix spaces of maximum rank at most two. | all explicitly presented finite fields and arbitrary dimensions |
| [GP-0269](UpperRankTwoSpecialLinear.md) | Special-linear TI reduces to ordinary TI in deterministic polynomial time whenever one slice space has maximum rank at most two. | certified slice upper rank two over explicit finite fields |
| [GP-0275](PrimeExtensionTensorComparison.md) | Exact reductions between ordinary tensor isomorphism over a prime field and its finite extensions. | extension-to-prime uniform in field size, reverse at fixed characteristic |
| [GP-0321](MatroidComponentLiftGroups.md) | Computes the image, lifts and order of the monomial automorphism group. | supplied abstract matroid automorphisms, parameterized by field size and maximum component cycle rank |
| [GP-0364](CompactSimpleCentralEpimorphisms.md) | Decides and counts central epimorphisms over all automorphisms of a nonabelian simple quotient. | compact perfect extensions over a displayed quotient table |
| [GP-0375](CyclicDerivedIntegralEpimorphisms.md) | Integral alternating invariant factors and torsion divisibilities decide epimorphism onto a cyclic-derived torsion-free target. | source class-two quotient with derived rank at most one |
| [GP-0407](NormalFaithfulDegreeClassTwo.md) | Alternating-form ranks give the optimal faithful degree with normal point stabilizers, with parallel evaluation under a small derived subgroup promise. | class two and odd prime exponent |
| [GP-0427](ExtraspecialComplementCounts.md) | Exact formulas count complements and their conjugacy classes and construct a complement. | extraspecial normal kernel in a class-two odd prime exponent group |
| [GP-0487](PrimeOrbitConjugatorCounts.md) | Counts simultaneous conjugators of compact group lists across partially matched prime regular orbits. | collective cyclic regular prime orbit actions |
| [GP-0491](CanonicalAbelianSchreierTransversals.md) | Logspace-uniform NC constructs a generator-independent ordered Schreier transversal. | elementary abelian ambient permutation action and unary index |
| [GP-0523](SimultaneousAffineLatinIsomorphisms.md) | Joint isomorphism of any number of Latin operations is decidable in polynomial time with hidden common coordinates. | common elementary abelian affine structure on each domain |
| [GP-0606](QuadraticIndividualDegreeSparseFactors.md) | Bounds factor sparsity by the input sparsity times a product controlled by higher-degree shared variables. | arbitrary fields, polynomial bound at fixed degree and logarithmically many higher-degree shared variables |
| [GP-0697](CompressedLaurentDepthThreeLimits.md) | Extracts exact limit circuits for depth-three inputs with exponentially large binary pole orders. | bounded number of common Laurent exponent generators |
| [GP-0713](ConstantWidthXORPlaceholderIPS.md) | Constructs constant-width ordinary and geometric placeholder IPS for inconsistent XOR constraints. | bounded-arity XOR CNFs |
| [GP-0715](PathwidthPolynomialCalculusROABP.md) | Constructs same-order linear ROABP-IPS from DAG-like Polynomial Calculus. | bounded pathwidth of labeled incidence graph |
| [GP-0756](CountGeometricBinomialZeros.md) | Classifies distinct geometric zero counting and gives short infinity certificates. | overdetermined sparse binomial systems over rationals and finite fields |
| [GP-0758](AdditiveFrobeniusFeasibility.md) | Decides feasibility and counts geometric solutions for compressed additive Frobenius systems. | additive equations and binary Frobenius indices |
| [GP-0800](IntersectionTableCertificates.md) | Reconstructs the intersection table from selected positive entries on a supplied generating set of basis relations. | named generators and labeled fibers |
| [GP-0935](CycleIndexTranspositionClasses.md) | Classifies the transposition case of symmetry-characterized graphs and separates full cycle indices up to complementation. | restricted automorphism family |
| [GP-0961](PointedMatroidGames.md) | Pointed independent-set quantum isomorphism equals ordinary matroid isomorphism. | loopless matroids, also pointed bases through rank three |
| [GP-0965](CoherentMultiplicityFourWitnesses.md) | Dimension-preserving reduction to ordinary uncolored graph quantum isomorphism, yielding no computable finite witness cap. | coherent multiplicity at most four |
| [GP-0993](IncidenceBlockCanonization.md) | Near-linear canonical labeling by compressing degree-two paths inside incidence blocks. | parameter is the maximum cyclomatic number of an incidence block |
