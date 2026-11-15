Lean proofs obtained and formalized with use of AI models, namely some combination of Claude Opus 5/5.5, Claude Fable 5/5.1, GPT-5.6 Sol and GPT-6 Astra.
I've tried to assert the novelty of these proofs: all are pending comprehensive human validation and formal writeups.
Each Lean file imports only Mathlib.

----------------------------------
INFORMAL PROOFS (not formalized yet)

<!-- audited-informal-open-problems:start -->
[AmannNilpotentRigidity/Proof.md](AmannNilpotentRigidity/Proof.md) — Amann, Theorem 2.2 conjecture. A uniform cohomology-ring obstruction gives quasi-isometric rigidity for the stated family for every k ≥ 2. Informal proof. [Original paper](https://arxiv.org/abs/1710.04542)

[NormalizedQuarticTensorCones/ExactMembership.md](NormalizedQuarticTensorCones/ExactMembership.md) — Ke–Honorio cone-membership question. Exact membership in the paired-entry normalized Carathéodory symmetric tensor cone is NP-complete at order four, even with balance. Informal proof. [Original paper](https://jmlr.org/papers/volume23/22-0232/22-0232.pdf)

[NormalizedQuarticTensorCones/Positivity.md](NormalizedQuarticTensorCones/Positivity.md) — Ke–Honorio, Appendix C. Positive semidefiniteness testing is coNP-hard for quartic tensors with the prescribed paired-index entries fixed to one. Informal proof. [Original paper](https://jmlr.org/papers/volume23/22-0232/22-0232.pdf)

[ExceptionalCopositivePlus/Proof.md](ExceptionalCopositivePlus/Proof.md) — Bomze–Dür exceptional copositive-plus question. Gives an exceptional boundary example and a separate 3 × 3 counterexample to Theorem 4.8 and Corollary 4.14 as printed. Informal proof. [Original paper](https://doi.org/10.1007/s10013-024-00722-x)

[PositivePolynomialBorderRank/Proof.md](PositivePolynomialBorderRank/Proof.md) — Klingler–Netzer–De las Cuevas, Outlook question. Positive polynomial decompositions can have an unbounded gap between SOS rank and border SOS rank. Informal proof. [Original paper](https://doi.org/10.22331/q-2025-02-26-1649)

[ReflectionPositivityCoarseGraining/Proof.md](ReflectionPositivityCoarseGraining/Proof.md) — A two-spin counterexample to the reflection-positivity implication posed in MathOverflow 503899 under its stated channel hypotheses. Informal proof. [Original question](https://mathoverflow.net/questions/503899)

[SymplecticSpectrumPreservers/Proof.md](SymplecticSpectrumPreservers/Proof.md) — Dinov, Problem 4.8. A linear map preserving all covariance symplectic spectra is symplectic or antisymplectic. Finite probes suffice. Informal proof. [Original preprint](https://arxiv.org/html/2607.07851v1)

[SymmetricSubgraphCircuits/Proof.md](SymmetricSubgraphCircuits/Proof.md) — Grochow–Jacob, Open Question 1.11, symmetric-circuit version. Paths rule out an exponent bounded by a constant times pattern treewidth. Informal proof. [Original question](https://arxiv.org/html/2606.26244v2)
<!-- audited-informal-open-problems:end -->

<!-- tensor-and-algebra-open-questions:start -->
[TensorAndAlgebraOpenQuestions/Smoothed-Exact-TI.md](TensorAndAlgebraOpenQuestions/Smoothed-Exact-TI.md) — **Exact smoothed orthogonal and unitary tensor isomorphism (Open Problem 2, Chizewer–Everett–Mithal–Qiao).** Informal proof of polynomial-bit exact decision after arbitrarily small independent rational-grid perturbations.

[TensorAndAlgebraOpenQuestions/Finite-Field-Orthogonal-TI.md](TensorAndAlgebraOpenQuestions/Finite-Field-Orthogonal-TI.md) — **Finite-field orthogonal tensor isomorphism with nonsplit spectra (orthogonal part of Open Problem 4).** Informal algorithm for squarefree marginal spectra and a positive limiting success fraction over each fixed finite field.

[TensorAndAlgebraOpenQuestions/Positive-Characteristic-PC.md](TensorAndAlgebraOpenQuestions/Positive-Characteristic-PC.md) — **Positive-characteristic Polynomial Calculus for matrix isomorphism (partial progress on CCC 2023 Open Question 7.3).** Informal degree bound from indecomposable multiplicities and polynomial expanded size when the relevant base-p digit position is bounded over a fixed field.

[TensorAndAlgebraOpenQuestions/Nonassociative-Test-Algebras.md](TensorAndAlgebraOpenQuestions/Nonassociative-Test-Algebras.md) — **Quadratic-dimensional nonassociative test algebras (partial progress on Mukhopadhyay–Ramya–Shastri, Section 5, Question 2).** Informal proofs of improved upper bounds and a characteristic-two obstruction to the published commutative construction.
<!-- tensor-and-algebra-open-questions:end -->

<!-- manin-bilinear-lean-reduction:start -->
[ManinBilinearReduction/ManinSingleFile.lean](ManinBilinearReduction/ManinSingleFile.lean) — **Manin’s bilinear undecidability conjecture (Conjecture 7.2), provisional Lean formalization.** The single file uses only Mathlib imports. The reduction from number-ring undecidability is Lean-verified, and the provisional endpoint has one explicit placeholder for that arithmetic theorem.
<!-- manin-bilinear-lean-reduction:end -->

<!-- general-position-polynomial-bounds:start -->
[GeneralPositionPolynomialBounds/PROOF.md](GeneralPositionPolynomialBounds/PROOF.md) — **General-position polynomial classifications and root bounds.** Informal proofs answering both balanced complete multipartite classification questions in Rather, arXiv:2603.06930v3, §4. Also proves the sharp minimum root modulus over connected graphs of each order, attained exactly by paths and the four-cycle, and exponential growth of the maximum root modulus.
<!-- general-position-polynomial-bounds:end -->

<!-- mathproofs-crossovers:start -->
[MathProofsCrossovers/PROOF.md](MathProofsCrossovers/PROOF.md) — **Crossovers in tensor isomorphism and binary designs.** Informal proofs of finite-field unitary TI equivalence with ordinary TI (Chen et al., Open Question 1.10), small-Gaussian-noise smoothed orthogonal and unitary TI (Chizewer et al., Open Problem 2), and a classification of minimum-rank bent translation designs (Hyun et al., Open Problem 3). Rules out the direct affine-block extension of Hyun et al. Theorem 6 to all plateaued functions, even with arbitrary block selection and repetitions. Credits the prior complex unitary reduction to Lysikov and Walter. Publication priority remains provisional.
<!-- mathproofs-crossovers:end -->

<!-- sparse-graph-distance-number:start -->
[SparseGraphDistanceNumber/PROOF.md](SparseGraphDistanceNumber/PROOF.md) — **Two bounds for the distance-number of sparse graphs.** An informal proof of Bakhajian and Feldheim's Conjecture 1 gives a uniform bound for fixed treewidth and maximum degree. A separate grid construction answers the bounded-degree question of Carmi, Dujmović, Morin and Wood, giving O(n/√log n) lengths for every fixed degeneracy bound.
<!-- sparse-graph-distance-number:end -->

<!-- rational-unit-distance:start -->
[RationalUnitDistance/PROOF.md](RationalUnitDistance/PROOF.md) — **Unit-distance realizability over the reals and rationals (CG64–CG65).** Resolves both open questions in Schaefer, Cardinal and Miltzow's compendium by proving existential-real completeness in every fixed dimension d ≥ 2 for ordinary and induced unit-distance recognition and for unit linkages. Also proves polynomial-time equivalence between rational polynomial solvability and injective unit-edge realization in ℚ²⁴, even for graphs that realize over ℝ and every ℚₚ. Assuming Glazer's claimed integer definition, rational realization is halting-complete even on a family of bounded pathwidth.
<!-- rational-unit-distance:end -->

<!-- rational-subrings-and-mazur:start -->
[RationalSubringsAndMazur/PROOF.md](RationalSubringsAndMazur/PROOF.md) — **Hilbert's tenth problem on rational subrings and a Cantor-set strengthening of Mazur's conjecture.** Assuming Glazer's claimed definition of ℤ in ℚ, identifies the many-one degrees of solvability over all subrings of ℚ with enumeration degrees of their inverted prime sets, using one fixed smooth degree-eight family. Also strengthens the known refutation of Mazur's 1992 conjecture to continuum many components inside a single real component of a smooth projective variety, with synchronized Cantor limit sets at all completions.
<!-- rational-subrings-and-mazur:end -->

<!-- rational-point-decision:start -->
[RationalPointDecision/PROOF.md](RationalPointDecision/PROOF.md) — **Rational-point decision on smooth hypersurfaces and marked projective varieties (Poonen).** Gives an unconditional equivalence between Hilbert's tenth problem and point existence on smooth affine hypersurfaces over every fixed number field. Over ℚ it also gives an unconditional equivalence with distinguishing exactly one rational point from infinitely many on smooth projective varieties with a supplied point. Assuming Glazer's claimed integer definition, the latter problem is halting-complete in one fixed smooth projective family.
<!-- rational-point-decision:end -->

<!-- diophantine-constant-fields:start -->
[DiophantineConstantFields/PROOF.md](DiophantineConstantFields/PROOF.md) — **Diophantine definitions of constants by rational specialization (Pheidas, AIM Question 4).** Assuming Glazer's claimed definition of ℤ in ℚ, gives one parameter-free definition of the constant field ℚ in every purely transcendental extension of ℚ, and defines the constants in the function field of every ℚ-variety with Zariski-dense rational points. Also records the resulting refutations of Pasten's Conjectures 5.13, 5.14, 5.16, and 5.20 and answers Pheidas's denominator-support question over ℚ.
<!-- diophantine-constant-fields:end -->

<!-- bilinear-diophantine-undecidability:start -->
[BilinearDiophantineUndecidability/PROOF.md](BilinearDiophantineUndecidability/PROOF.md) — **Bilinear Diophantine undecidability (Manin, Conjecture 7.2).** Proves undecidability for integer systems built from any fixed nonzero bilinear map, using Koymans–Pagano's theorem, and completes Manin's classification of extension decidability for simply connected finite targets. Also gives a single smooth projective counterexample to Pasten's Diophantine approximation conjecture over ℚ at every completion, conditional on Glazer's claimed Diophantine definition of ℤ in ℚ.
<!-- bilinear-diophantine-undecidability:end -->

<!-- local-global-r-equivalence:start -->
[LocalGlobalREquivalence/PROOF.md](LocalGlobalREquivalence/PROOF.md) — **Undecidable Local–Global R-Equivalence on One Smooth Projective Variety.** Assuming the integers are Diophantine in the rationals, proves that deciding R-equivalence of two given rational points is halting-complete on a single fixed smooth projective variety. The input pairs lie on rational curves together over every completion. The construction uses a fixed smooth projective family with spherical real fibers whose rational point sets have either exactly two points or infinitely many. AI-assisted informal proof.
<!-- local-global-r-equivalence:end -->

<!-- ternary-rational-nash:start -->
[TernaryRationalNash/PROOF.md](TernaryRationalNash/PROOF.md) — **Rational Nash Equilibria at the Pairwise–Ternary Boundary.** Proves unconditional $\exists\mathbb Q$-completeness for rational equilibrium existence with two actions per player, bounded interaction degree, and a fixed finite alphabet of pointwise zero-sum local payoff tables of arity at most three. Exact Nash equilibrium search is FIXP-complete under the same restrictions. Pairwise games always have a rational equilibrium. Assuming the integers are Diophantine in the rationals, also proves halting-completeness on a fixed-core family of bounded pathwidth and a fixed-graph family with one varying payoff vector. AI-assisted informal proof.
<!-- ternary-rational-nash:end -->

<!-- rational-nash-equilibrium:start -->
[RationalNashEquilibrium/PROOF.md](RationalNashEquilibrium/PROOF.md) — **Rational Nash Equilibrium in Three-Player Zero-Sum Games.** Gives an explicit polynomial-time compactification removing the bounded-witness promise in Berthelsen–Hansen’s reduction, yielding an unconditional $\exists\mathbb Q$-completeness proof. Also gives a conditional halting-completeness result with fixed action sets and two varying pure payoff vectors, assuming Glazer’s Diophantine definition of the integers in the rationals. The hardness classification already appears in the 2024 compendium. AI-assisted informal proof.
<!-- rational-nash-equilibrium:end -->

<!-- ti-sl-midpoint-algorithms:start -->
[SLMidpointAlgorithms/PROOF.md](SLMidpointAlgorithms/PROOF.md) — **Exact midpoint and determinant-coset algorithms for tensor isomorphism.** Gives shared triangular factor elimination, exact unitriangular orbit and midpoint algorithms under explicit hypotheses, and a deterministic ordinary-TI oracle reduction for SL-TI when just one mode has a narrow intrinsic flag. Includes scalar-adjoint primitive families with all modes growing and an oracle-free algorithm for block flag groups with small diagonal images. The unrestricted four-layer midpoint problem remains open. AI-assisted informal proofs with exact finite checks.
<!-- ti-sl-midpoint-algorithms:end -->

<!-- ti-sl-adjoint-multiplicities:start -->
[SLAdjointMultiplicities/PROOF.md](SLAdjointMultiplicities/PROOF.md) — **Determinants on adjoint multiplicity spaces.** A deterministic same-field ordinary tensor isomorphism oracle algorithm computes the transporter determinant coset in time polynomial in L + 2^w over each fixed finite field. Here w is the largest multiplicity whose determinant contribution survives the pair-adjoint corrections. The result handles radicals, nonsplit factors and center-label permutations, and combines with block assembly when the primitive blocks have logarithmic w. Unrestricted primitive SL-TI remains open. AI-assisted informal proof with exact finite checks.
<!-- ti-sl-adjoint-multiplicities:end -->

<!-- ti-sl-four-fronts:start -->
[BalancedQuarticOCI/PROOF.md](BalancedQuarticOCI/PROOF.md) — **TOCI-completeness of a single balanced quartic.** Answers all three explicit completeness cases of Lysikov–Walter Question I.12 (arXiv:2411.04639v2). Two partial traces recover a closed matrix-tag orbit, giving exact reflection of degenerations with dimension doubling. The [product-group extension](BalancedQuarticOCI/PRODUCT-GROUP.md) proves completeness for one bipartite operator and classifies every fixed individually balanced tensor tuple under products of GL groups. The general unbalanced dichotomy remains open.

[SymmetricQuarticOCI/PROOF.md](SymmetricQuarticOCI/PROOF.md) — **TOCI-completeness of one symmetric mixed quartic.** An affirmative answer to Lysikov–Walter Question I.14, with a single tensor in Sym²(W) ⊗ Sym²(W*) and no separate marks. Trace-cancelling internal markers recover the necessary color transfers and lift every contraction invariant. Its implications for I.12 overlap the preceding entry.

[LinearStructureUniversality/PROOF.md](LinearStructureUniversality/PROOF.md) — **Basis-explicit linear-structure universality.** Answers Grochow–Qiao Open Question 7.4 affirmatively for all fixed arities and signatures, over the same field. Makes explicit the application of our prior mixed-system packing and the published FGS compiler to relations, functions, and repeated primal/dual actions. Includes the uniform dense-input extension and the credited prior packing proof. No succinct determinant encoding is claimed.

[SLDeterminantAssembly/PROOF.md](SLDeterminantAssembly/PROOF.md) — **Determinant coset assembly for tensor direct sums.** At every fixed finite field, a deterministic polynomial-time truth-table reduction takes arbitrary SL-TI to SL-TI on concise tensors with local centroid. The exact determinant formula handles matching signs, coordinate changes and deficient modes without a transporter oracle. This closes the block assembly step for the Turing comparison; the primitive reduction to ordinary TI and unrestricted many-one containment remain open.

All four entries are AI-assisted informal proofs, with exact controls and internal reviews. No Lean verification, external validation, or publication-priority claim.
<!-- ti-sl-four-fronts:end -->

<!-- four-target-research-results:start -->
[FractionalBicliqueSeparation/PROOF.md](FractionalBicliqueSeparation/PROOF.md) — **Strict asymptotic fractional biclique cover/partition separation.** An informal all-tensor-powers proof that the Domino has fractional cover number 2 but asymptotic fractional partition number at least 1/2 + sqrt(5/2) > 2. Rules out convergence to 2 discussed by Ghosal–Karrenbauer (SEA 2025, Sections 3–4) and supplies the strict separation missing from their comparison chain; the exact asymptotic value remains open. Includes a complete strictness classification when fractional cover number equals 2, exact controls and internal audits. The integral binary-rank counterexample documented alongside it is Shitov’s prior result, not our discovery.

[MatrixIsomorphismPC/PROOF.md](MatrixIsomorphismPC/PROOF.md) — **Sharp degree-three certificates for matrix conjugacy and congruence.** Informal universal polynomial-size, degree 3 ordinary Polynomial Calculus refutations for nonisomorphic explicit quiver representations and noncongruent labelled matrix tuples in characteristic zero, with stated large-characteristic extensions. Addresses CCC 2023 Open Question 7.3: exact worst-case degree 3 for congruence in every dimension and conjugacy from dimension 4. Includes singular and nonsymmetric matrices; uses endomorphism-algebra block traces and actual degree-3 intertwiner derivations. Congruence unsatisfiability is over the algebraic closure. Unrestricted small characteristic and optimal proof-size complexity remain open.

[QuiverSemistabilityCompression/PROOF.md](QuiverSemistabilityCompression/PROOF.md) — **Reciprocal primitive-core compression.** An exact generic-semistability algorithm and a self-contained classical rank-two branch. The unrestricted binary-dimension question from ICALP 2025 remains open; the numeric core parameter is not silently counted as logarithmic input size.

[SkewTableauxLogspace/PROOF.md](SkewTableauxLogspace/PROOF.md) — **Low-Durfee-rank skew-tableau counting.** An informal positive small-space subtheorem with exact controls. Unrestricted unary skew-SYT Question 5.15 remains open; the proof gives the precise parameter bound.

[CountingLogspacePriorAudit/PROOF.md](CountingLogspacePriorAudit/PROOF.md) — **Credited audit of already-public logspace counting results.** The unary Hermite, principal-Schur and GL2-plethysm FL proof was already posted by fengqiaoqu on 22 October 2026 in [schur-principal-logspace](https://github.com/fengqiaoqu/schur-principal-logspace). Our independent audit found no gap and supplies separate exact diagnostics; explicitly not our discovery. No prior repository code is bundled.

All entries are AI-assisted informal mathematics, not Lean-verified. External human validation and publication priority remain unestablished for the candidate additions.
<!-- four-target-research-results:end -->

<!-- two-complete-results:start -->
[StabilizerCodeLU/PROOF.md](StabilizerCodeLU/PROOF.md) — An informal polynomial-time solution of physical local-unitary equivalence for arbitrary qubit stabilizer codes on the same labelled physical qubits, extending the arbitrary-logical-rank case left outside Zhang’s (2026) graph-state and one-logical-qubit algorithm (arXiv:2610.00527v2, Sections 4.3 and 6). Covers every logical dimension k and constructs exact symbolic local-unitary witnesses, with no supplied axes or CSS promise. Combines minimal-support axis extraction, exact diagonal-orbit compression and paired adjugate flag equations that eliminate the remaining Clifford search. Includes the full proof, attribution, separate AI-worker audits and reproducible exact controls. Physical-qubit permutation search is outside the polynomial-time claim. AI-assisted informal proof; independent human validation, publication priority and Lean formalization remain pending.

[CentralKroneckerAsymptotics/PROOF.md](CentralKroneckerAsymptotics/PROOF.md) — An informal answer to Greta Panova’s Open Problem 6.13 in *Complexity and asymptotics of structure constants* (arXiv:2305.02553): tight asymptotics for the central square-rectangle Kronecker coefficients g((m^m),(m^m),(ceil(m²/2),floor(m²/2))). Proves the leading term (3√3/π)(1 + 1_{m odd})4^m/m^5, with relative correction 1 − 2/m + O(m⁻²), covering both parities, and a near-central window extension. Uses an exact adjacent-difference Fourier integral with global tail bounds; credits the classical Pak–Panova identity and related Melczer–Panova–Pemantle asymptotics. Includes the full proof, internal reviews and portable exact diagnostics. AI-assisted informal proof; independent human validation, publication priority and Lean formalization remain pending.
<!-- two-complete-results:end -->

<!-- matrix-code-conjugacy:start -->
[MatrixCodeConjugacy/PROOF.md](MatrixCodeConjugacy/PROOF.md) — An informal affirmative answer to Problem 1.6 of Li, Li, Qiao, Tao and Wang, *On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields* (arXiv:2604.00591v2): average-case polynomial-time matrix-code conjugacy for arbitrary slice dimension. For every fixed finite field F_q and sufficiently large n, the algorithm succeeds on an Ω(1/q) fraction of uniformly random first n × n × m tensors against every second tensor, including dependent slices; every nonfailure answer is correct and a positive answer includes a conjugator. Combines credited trace-hull and spectral machinery with dimension duality, bounded pair enumeration and a dimension-uniform counting argument. Includes the full proof, explicit binary-runtime analysis and portable exact finite controls. AI-assisted informal proof, internally reviewed; independent human validation, publication priority and Lean formalization remain pending.
<!-- matrix-code-conjugacy:end -->

WhiteBoxPITToFactorization.md — A proposed affirmative answer to the first open question in §7 of Bhattacharjee et al.’s (2025) Closure under factorization from a result of Furstenberg: does efficient white-box polynomial identity testing imply efficient deterministic factorization within restricted algebraic models? Gives a constructive reduction for effectively robust classes, including arithmetic formulas, ordinary commutative branching programs, and constant-depth circuits, over characteristic-zero and sufficiently-large-characteristic fields, retaining the paper’s deterministic univariate-factorization assumption. Computes complete irreducible factorizations with multiplicities and scalar unit; for depth-\(\Delta\) circuits, PIT and output depth are bounded by \(\Delta+c\), with \(c\) absolute. Includes the explicit cluster decoder, adaptive partition algorithm, termination and runtime proofs, and polynomial binary-time consequences over ℚ and fixed number fields; the branching-program implication is credited to Sinhababu–Thierauf (2021). Informal and internally audited, pending independent human validation and full Lean formalization of the extensions.

FourOutcomeTripleCompatibility/FourOutcomeTriple_UniversalSOSCertificate.json — An exact computer-assisted proof of the \((k,n)=(3,4)\) case of Conjecture 10 in Designolle–Farkas, k-fold unbiased measurements and maximal incompatibility (2026). Every triple of four-outcome POVMs in any finite complex dimension has generalized compatibility visibility at least \((1+\cos(\pi/9))/3\), attained by the previously known rank-two triple in dimension eight. Establishes exact attainment at SOS hierarchy level 3 and equality at every higher level, without unbiasedness or rank restrictions. Includes the explicit certificate, proof, and reproducible verifiers checking exact algebraic identities and rigorous Gram-matrix positivity. Computer-assisted informal proof; not yet Lean-formalized.

[ROABPHighPowerRoots/PROOF.md](ROABPHighPowerRoots/PROOF.md) — An informal sufficient result addressing the root question in Section 6 of Andrews et al., *On Closure Properties of Read-Once Oblivious Algebraic Branching Programs* (ITCS 2026): can a power have a small ROABP while its root is hard? Over every characteristic-zero field, if g^d has width w with d ≥ w in a given variable order, then g has width one in that same order and is a scalar times a product of univariate polynomials. Includes a mixed-factor multiplicity versus separation-rank lemma and its Wronskian proof, plus 300 exact rational finite checks. The regime d < w remains open; novelty is unestablished. AI-assisted informal proof, internally reviewed, pending independent human review and Lean formalization.

[BinomialProductDegree/PROOF.md](BinomialProductDegree/PROOF.md) — An informal affirmative answer to the explicit-rational version of Guillaume Lagarde's binomial-product degree question: compute the degree, or detect zero, of a product of rational binomials minus one monomial in deterministic polynomial bit time, with all exponents given in binary. Covers arbitrary signs, zero factors, repeated exponents and exact leading cancellation, using a polynomial-size logarithmic-derivative coefficient bank. Includes the full proof, reference algorithm and 3,000 exact comparison cases plus huge-exponent controls. AI-assisted MathProof work; independent human review, novelty assessment and Lean formalization remain pending.

[HomogeneousCubicVectorialBent/PROOF.md](HomogeneousCubicVectorialBent/PROOF.md) — An informal affirmative answer to Alexandr Polujan's (2021) Open Problem 4.31: do nonquadratic homogeneous vectorial bent functions exist? Gives an explicit homogeneous cubic map from F_2^10 to F_2^2, with all three nonzero components bent, and an infinite direct-sum family in dimensions 10r. Includes the full proof, explicit monomials and two portable exact verifiers checking every truth value, ANF coefficient and Walsh coefficient. AI-assisted MathProof work with separate AI-worker audits; independent human review, novelty assessment and Lean formalization remain pending.

[LinearToSemilinearCodeEquivalence/PROOF.md](LinearToSemilinearCodeEquivalence/PROOF.md) — An informal resolution of the reverse-reduction gap stated in Section VI of Mazumder's (2026) Search-to-Decision Reductions for the Linear and General Code Equivalence Problems. Gives a same-field linear-to-semilinear code-equivalence wrapper of length 5n+10 and dimension k+2, forcing every wrapped witness to have trivial Frobenius. Provides search LCE to decision GCE via the credited existing LCE self-reduction, in polynomial time in n, k and log q. Includes full proofs, AI-worker audits and exact checks; publication priority, human review and Lean formalization remain pending.

[NonprimeCodeToLattice/PROOF.md](NonprimeCodeToLattice/PROOF.md) — An informal answer, at alphabet-polynomial cost, to the nonprime-field LEP-to-lattice-isomorphism question stated by Cheraghchi-Shagrithaya-Veliche (2025) and Horlemann-Mazumder-Schaller-Weger (2026). For every presented finite field F_q, constructs a lattice instance and recovers monomial code witnesses in poly(n,k,q) time, with no original-code distance, hull or genericity promise. Uses an explicit field-descent frame and the credited classical Construction A shortest-vector argument. The stronger uniform poly(n,k,log q) question remains open. Includes full proofs, separate AI-worker audits and portable finite checks; novelty, independent human review and Lean formalization remain pending.

[AffineTensorIsomorphism/PROOF.md](AffineTensorIsomorphism/PROOF.md) — An informal TI-completeness theorem for the standard homogeneous affine groups [[A,b],[0,1]] over every field, addressing the affine-family research direction explicitly proposed in Section 1.5 of Chen-Grochow-Qiao-Tang-Zhang; this is not a numbered-conjecture closure. Proves TI_Aff = TI on arbitrary tensors and extends to growing pointwise-fixed quotient blocks. Reuses and credits the Futorny-Grochow-Sergeichuk / CGQTZ tensor-system compiler. Includes the full proof, separate AI-worker audit and exact stabilizer checks; novelty, human review and Lean formalization remain pending.

[FixedCharacteristicTensorIsomorphism/Proof.md](FixedCharacteristicTensorIsomorphism/Proof.md) — An informal proof of the same-characteristic finite-field clause of Grochow and Qiao's Open Question 7.6: for every fixed prime p, ordinary tensor isomorphism over any two finite fields of characteristic p is equivalent under deterministic polynomial-time many-one reductions, on all inputs. The construction is uniform in the supplied extension degrees and uses classical Frobenius representations with published Futorny–Grochow–Sergeichuk compilation. The other field comparisons and a uniform polynomial bound in log p are not claimed. Includes the full proof, attribution, fresh internal audits and bounded novelty review; publication priority, independent human review and Lean formalization remain pending.

-------------------------------------------
RESOLUTIONS VIA PRIOR WORK (not claimed as our discoveries)

[ClassicalSubdesignFreeDesign16/PROOF.md](ClassicalSubdesignFreeDesign16/PROOF.md) — Records an affirmative answer via classical constructions to the general-design existence clause of Meidl–Polujan–Pott's (2023) concluding Problem 4 / the first part of Polujan's Open Problem 3.69: a simple 2-(16,4,3) design exists without a 2-(16,4,1) subdesign. Construction credit belongs to Martin Glen Oxenham's 1991 finite-geometric cover work; this is NOT claimed as our own discovery or first recognition. We supply the explicit 60-block witness, a three-case hand proof, portable checks and the connection to the later question. The separate vanishing-flat-restricted and realizability questions are not resolved by this example.

-------------------------------------------
MISC PROOFS (RESULTS THAT SEEM SIGNIFICANT BUT DO NOT CLOSE AN EXPLICIT OPEN PROBLEM/CONJECTURE)

<!-- fixed-field-ordinary-four-ti:start -->
- **Ordinary Four-Tensor Isomorphism at Fixed Field Size** ([informal proof](FixedFieldOrdinaryFourTI/PROOF.md), [exact checks](FixedFieldOrdinaryFourTI/check_examples.py)). Answers LLQTW arXiv v2 Problem 1.7 affirmatively. Deterministic polynomial-time recognition over each fixed finite field covers a fraction tending to $1-c(q)^3$ of uniform first inputs, with exact decisions against every second tensor. Handles singular kernel forms and repeated spectra, and gives an $O(n^{4/3})$-dimension objectwise ordinary 3TI reduction on recognized inputs. The all-invertible sector remains open.
<!-- fixed-field-ordinary-four-ti:end -->

<!-- problem18-four-levers:start -->
- **Four Directions from Problem 1.8** ([informal proofs](Problem18FourLevers/PROOFS.md), [Lean block assembly](Problem18FourLevers/BlockOracle.lean), [exact finite checks](Problem18FourLevers/check_examples.py)). Gives a graph encoding with controlled Gram collisions, a positive-density orthogonal search theorem for alternating forms, and a linear-side reduction from ordinary TI to tensors with fixed invertible Grams. The alternating-form result concerns orthogonal masks and does not break ALTEQ. Lean checks the zero-error matching interface for composing partial block decisions.
<!-- problem18-four-levers:end -->

<!-- generic-ordinary-four-ti:start -->
- **High-Coverage Ordinary Four-Tensor Isomorphism** ([informal proof](GenericOrdinaryFourTI/PROOF.md), [exact switch checks](GenericOrdinaryFourTI/check_switches.py)). Transfers the spectral approach of Problem 1.8 to the ordinary general-linear action. For $n\geq37$, a zero-error algorithm decides on at least a $1-16n^4/q$ fraction of uniform first inputs in expected polynomial bit time, with a deterministic algorithm in fixed characteristic. The construction extends to every even tensor order in polynomial dense-input time. The coverage guarantee is for growing fields and leaves the fixed-field LLQTW v2 Problem 1.7 open.
<!-- generic-ordinary-four-ti:end -->

<!-- full-cut-tensor-isomorphism:start -->
- **Full-Cut-Rank Tensor Isomorphism** ([informal proof](FullCutTensorIsomorphism/PROOF.md), [exact marker certificate](FullCutTensorIsomorphism/verify_marker.py)). A linear-side affine reduction embeds unrestricted four-tensor isomorphism in tensors with all pair flattenings invertible and scalar centroid, over characteristic 5 and characteristic zero. The outputs also rule out cyclic covariants and, over fixed finite fields, polynomial-size intrinsic frame lists. This transfers the order-four case of Grochow–Qiao Question 7.8 to a sharply restricted promise.
<!-- full-cut-tensor-isomorphism:end -->

<!-- tensor-frame-recovery:start -->
- **Tensor Frame Recovery and Cyclic Quotients** ([weighted four-tensors](TensorFrameRecovery/PROOFS.md), [cyclic quotient proof](TensorFrameRecovery/CYCLIC-QUOTIENT.md)). Partial progress on Grochow–Qiao Question 7.8. Raw frame recovery compresses the weighted cyclic support to dimension $O(n^{2/3})$ and gives linear dimension for group-table supports under a principal-block criterion. A separate compact quotient method reaches the ambient counting exponent for cyclic covariants with arbitrary payloads, including repeated roots and zero components. Informal proofs.
<!-- tensor-frame-recovery:end -->

<!-- fractional-tensor-order:start -->
- **Fractional-Exponent Tensor Order Reduction** ([informal proofs](FractionalTensorOrder/PROOFS.md), [exact examples](FractionalTensorOrder/check_examples.py)). Progress on Grochow–Qiao Question 7.8. Intrinsic cut supports and centroid blocks improve the balanced reduction on structural promises. Spectral canonization reaches the counting exponent on a checkable class over fixed finite fields, and a finite-point lower bound proves that a single group lift with orbitwise injectivity forces the rounded exponent. The all-input polynomial-time question remains open.
<!-- fractional-tensor-order:end -->

<!-- exact-tree-network-descent:start -->
- **Exact Tree Network Descent** ([overview](ExactTreeNetworkDescent/README.md), [ten informal proofs](ExactTreeNetworkDescent/PROOFS.md)). Exact polynomial-core realization at every minimum edge width over a two-parameter polynomial ring, with a compressed polynomial-time algorithm in the homogeneous case. Dedekind-domain results give a sharp extra-state allowance and ideal-class cancellation. The note credits the classical matrix threshold and distinguishes it from the tree and algorithmic extensions.
<!-- exact-tree-network-descent:end -->

<!-- design-boolean-tool:start -->
**Design Boolean: constructive recognition and reconstruction tool.** [Software, examples and usage](DesignBooleanTool/README.md) implementing our bordered-rank characterization for Open Problem 4 on plateaued-function addition designs. Version 0.2 adds optional native C++ execution and an independently reviewed certificate-first validation argument. On the measured 1024 × 1024 case, full in-memory reconstruction and checking took 11.3 ms versus 366 ms for the SageMath 9.3 adapter; fresh CLI wall time improved from 500 ms to 195 ms. Actual M4RI and GAP DESIGN comparisons, raw samples and limitations are in the [benchmark report](DesignBooleanTool/benchmarks/README.md). These are version-specific adapter measurements, not a current-Sage or state-of-the-art claim. The software passes 34 tests and a 65,536-case structured exhaustive check; the executable and new validation argument are not Lean-verified. Apache-2.0; published examples and mathematical sources are credited in the package.
<!-- design-boolean-tool:end -->

<!-- cross-branch-resolutions:start -->
- **The Missing Complex Hanner Inequality** ([informal proof](CrossBranchResolutions/HANNER.md)) proves the reverse Steinhaus inequality for every finite family of complex Lp functions and 1 ≤ p ≤ 2, resolving the missing range stated by Jenkins–Tkocz. The proof uses an explicit positive-semidefinite regularized Hessian. Independently audited informally; not Lean verified, and publication priority is unconfirmed.
- **A Counterexample to J-Preorder Loewy Monotonicity** ([informal proof](CrossBranchResolutions/LOEWY.md), [exact computational supplement](CrossBranchResolutions/LOEWY-EQUIVALENCE-SUPPLEMENT.md)) refutes Jonsson's Conjecture 43 using connected characteristic-2 algebras with Loewy lengths 5 and 3; tensor powers give arbitrarily large additive violations. The block-theoretic ingredients are established results, not our discoveries. Independently audited informally; not Lean verified, and priority for recognizing the contradiction is unconfirmed.
<!-- cross-branch-resolutions:end -->

<!-- rank-two-geometric-universality:start -->
- **Arithmetic and geometric universality at rank two** ([informal proof](RankTwoGeometricUniversality/PROOF.md)) encodes every affine scheme over Q as a smooth surjective binary rank-two matrix-completion construction, preserving singularities up to smooth variables. Combines local witnesses and smoothing to retain H10(Q)-equivalence even for smooth geometrically integral completion spaces solvable over every completion of Q. Undecidability is conditional; the new strengthening has author audit only, with no Lean certification or established priority.
<!-- rank-two-geometric-universality:end -->

<!-- rank-two-ring-universality:start -->
- **Rank-two matrix completion and tensor universality over rings** ([proofs and scope](RankTwoAndRingUniversality/README.md)) proves binary-entry rank-two completion existentially complete, gives a binary rank-two PSD completion corollary and a fixed-finite-field NP-completeness threshold, extends the finite-free tensor equivalences to arbitrary commutative rings, and gives smaller form-to-tensor reductions in small characteristic. Informal proofs with finite gadget checks; prior rank-three completeness is credited, and novelty qualifications are explicit.
<!-- rank-two-ring-universality:end -->

<!-- tensor-form-questions:start -->
- **Tensor and cubic-form isomorphism questions** ([proofs and scope](TensorFormQuestions/README.md)) gives an arbitrary-base-ring reduction in the finite-free basis model, an explicit six-variable local-to-global counterexample, and an optimal exponent for algebraically equivariant arity reduction. Also explains rational decidability as a credited classical consequence. Informal proofs, with remaining scope and priority qualifications stated.
<!-- tensor-form-questions:end -->

<!-- lean-library-crossovers:start -->
- **Four crossovers from the Lean library and MathProofs** ([informal proofs](LeanLibraryCrossovers/PROOF.md)) refutes Lovett–Zhang Conjecture 37, answers the block-graph general d-position question, resolves Agrawal–Saxena's all-field cubic-form reduction question, and proves Cody–Moore Conjecture 7.6. The note also treats degree padding and smooth quartic point counts.
<!-- lean-library-crossovers:end -->

-------------------------------------------
PROOFS THAT CLOSE AN EXISTING OPEN PROBLEM/CONJECTURE OR IMPROVE A BEST PUBLISHED BOUND:

Problem 18 - First machine-checked solution of LLQTW Problem 1.8: a zero-error average-case polynomial-time algorithm for orthogonal and unitary 3-tensor isomorphism over all finite fields, fully formalized and kernel-verified in Lean 4.

FormulaFactorization.lean - An affirmative answer to the rational arithmetic-formula case of the first open question in §7 of Bhattacharjee, Kumar, Rai, Ramanathan, Saptharishi, and Saraf’s (2025) Closure under factorization from a result of Furstenberg: does efficient deterministic white-box polynomial identity testing imply efficient deterministic factorization within the same algebraic model? Here deterministic polynomial-time PIT for division-free arithmetic formulas over ℚ is formally proved sufficient to compute complete irreducible factorizations as formulas, including multiplicities and the scalar unit. The formalization verifies algorithm execution, exact output encoding, and polynomial runtime in the original binary input size, including coefficient and variable-name bits. Fully Lean-verified in one file importing only Mathlib, with only standard axioms; resolves the rational-formula case, while the branching-program, constant-depth, and other-field variants are outside its scope.

BalancedOrdinaryReduction.lean - Addresses Grochow and Qiao’s Open Question 10.8 on near-optimal reduction from d-tensor isomorphism to three-tensor isomorphism. Over every field, exact isomorphism equivalence and total output dimension O(n^⌈d/3⌉) are formally verified for arbitrary ordered shapes with d ≥ 3 and factor dimensions bounded by n ≥ 2, with an absolute implied constant. This achieves the requested exponent asymptotically as d grows and the counting-bound exponent when 3 divides d; the polynomial-time construction remains a written argument rather than a formally verified running-time theorem. Improves the published dimension exponent from \(\lfloor d/2\rfloor\) to \(\lceil d/3\rceil\), a strict improvement for six factors and every order at least eight: six-way tensors require output dimensions \(O(n^2)\) instead of \(O(n^3)\), and twelve-way tensors require \(O(n^4)\) instead of \(O(n^6)\). Published baseline: https://opus.lib.uts.edu.au/bitstream/10453/189643/2/3717823.3718282.pdf

When three divides \(d\), the reduction attains the finite-field counting lower-bound exponent: uniformly sized inputs can be encoded as ordinary three-tensors with only \(O(n^d)\) output coordinates—linear in the input’s coordinate count—while preserving and reflecting isomorphism exactly. This provides an optimal exponent for infinitely many orders and approaches the optimal exponent as \(d\) grows, addressing Grochow–Qiao’s quantitative order-reduction question.

Lean verifies correctness and the absolute-constant dimension bound over every field, for arbitrary ordered shapes with \(d\ge3\) and factor dimensions bounded by \(n\ge2\); polynomial running time remains a written argument.

PlateauedAdditionDesigns_BorderedRankCharacterization.lean — A self-contained, Mathlib-only answer to Open Problem 4 of Hyun–Kwon–Wang–Wu, Designs, linear codes, plateaued functions, and their interconnections (2026). For every \(r\ge1\) in the nondegenerate parameter range, replaces Theorem 3(iii)’s rank-plus-Reed–Muller embedding condition with the single criterion \(\operatorname{rank}_2\!\begin{pmatrix}M&\mathbf1\\\mathbf1^T&0\end{pmatrix}=m+2\). Proves equivalence with an \(r\)-plateaued addition-design realization having no nonzero linear structures, including the full reconstruction. Also constructs a simple \(2\text{-}(64,28,24)\) design of incidence rank \(9\) showing that the original, unbordered rank condition alone is insufficient already for \(r=1\).

CubicBentSupportCodeDesignAutomorphismGroups.lean — A Mathlib-only formalization answering Open Problem 6 of Hyun–Kwon–Wang–Wu, Designs, linear codes, plateaued functions, and their interconnections (2026) for an infinite family of cubic bent functions with arbitrary quadratic stabilization. The problem asks for simpler, explicit automorphism groups for special bent functions. This proof determines both the full support-code and support-design automorphism groups, replacing Theorem 8’s abstract stabilizer description with an explicit semidirect-product structure, multiplication laws, and exact group orders. It resolves the requested determination for this family—not a classification of all bent functions.

TwoAnchorWalshMUBClassificationAndExtensions.lean - A Mathlib-only proof incorporating the resolution of Open Problem 3.65 in Polujan’s Boolean and Vectorial Functions (2021) and extending it to real Walsh MUB configurations. For vectorial bent maps in the admissible Nyberg range, vanishing-flat design isomorphism, extended-affine equivalence, and arbitrary complex unitary equivalence preserving the computational and Walsh bases individually are equivalent. Constructs the normalized family of \(2^m+1\) real MUBs in dimension \(2^N\), and proves that an additional Walsh-phase basis is unbiased to the family exactly when adjoining its Boolean phase preserves vectorial bentness; the resulting enlarged family explicitly contains the original bases. Subsumes the earlier vanishing-flat classification and Walsh-phase extension proofs. The two-anchor restriction is essential: no unanchored classification or restriction on arbitrary additional complex bases is claimed.

CompleteSevenMUBDegreeFiveParent.lean - A Mathlib-only proof extending the polynomial-parent approach in Designolle’s Most incompatible measurements and sum-of-squares optimisation (2026). Every hypothetical family of seven MUBs in complex dimension six admits an explicit degree-five parent POVM with depolarizing visibility \(56137/184289\) and generalized visibility \(232487/552867\), strictly improving the retained \(4415/14497\) construction. Also proves the exact attained optimum within the common-quadratic odd-sum-of-squares parent class, including finite sums: the largest real root of \(42875\eta^3-12495\eta^2-609\eta+133=0\). The proof establishes the required conditional moments, positivity, normalization, and every marginal from the actual MUB hypotheses. This is a restricted-class optimum—not the optimum over all joint measurements—and does not establish that seven MUBs exist.

FourProjectiveMeasurements_ArbitraryRank_LowerBoundAndRigidity.lean - A proof of the arbitrary-rank four-measurement selected-sum bound, resolving the four-measurement case left open after Theorem 9 of Designolle–Farkas, k-fold unbiased measurements and maximal incompatibility (2026). Covers every outcome count \(n\ge2\) in every positive finite dimension, allowing unequal and zero outcome ranks without assuming unbiasedness. Also proves equality rigidity: attaining the bound forces every subtriple to be algebraically three-fold unbiased.

PairwiseUnbiasedPVMTripleCompatibility.lean — A Mathlib-only proof extending Designolle–Farkas, k-fold unbiased measurements and maximal incompatibility (2026). Every arbitrary-rank triple of pairwise mutually unbiased projective measurements with \(n>0\) outcomes admits an explicit positive normalized parent at generalized visibility \((1+x_n)/3\), where \(x_n\) is the unique positive root of \(n^2x^3-3nx-2=0\). This resolves the pairwise-unbiased special case of Conjecture 10(3,4). For every rank-one MUB triple in dimension \(n\ge3\), the same parent achieves a strictly larger visibility with an explicit, dimension-dependent positive increment, replacing the earlier compactness-only existence result. The proof includes a quantitative flat-unitary inequality and exact sum-of-squares control of all marginal cross terms. All earlier results, including \(x_4=\cos(\pi/9)\), are retained. The unrestricted arbitrary-PVM conjecture and dimension-six MUB existence problem remain open.

PolujanPottV1.lean - An affirmative answer to Polujan-Pott (2021) Open Problem V.1 / Polujan's (2021) Open Problem 3.64: "Can two vectorial bent functions have isomorphic graph translation designs without being EA-equivalent?"

Polujan365.lean - An affirmative answer to Polujan’s (2021) Open Problem 3.65: “For every even \(n\), are two vectorial bent functions EA-equivalent exactly when their vanishing-flat designs are isomorphic?” Here it is proved that vanishing-flat design isomorphism is equivalent to EA-equivalence for all vectorial bent functions in the admissible Nyberg range.

Polujan369.lean - A negative answer to the realizability question in Polujan’s (2021) Open Problem 3.69: “Must a subdesign of a vectorial bent function’s vanishing-flat design, with the parameters expected of an extension, itself arise from such an extension?” Here a six-variable vectorial bent function F: F₂⁶ → F₂² and a 2-(64,4,3) subdesign of VF(F) are formally verified in Lean, together with the impossibility of realizing that subdesign as VF((F,g)) for any Boolean coordinate g. This resolves the realizability question within the admissible Nyberg range; the separate subdesign-existence question is not addressed.

BentAffineOrbit.lean - An affirmative answer to Kudin, Pasalic, Polujan, and Zhang’s (2025) Open Problem 2: “Can one construct EA-inequivalent bent concatenations outside the completed Maiorana–McFarland class using affine rearrangements of one fixed seed?”; here an explicit pair is formally verified in every even dimension N ≥ 8, with distinct linearity indices N/2 − 2 and N/2 − 1, together with an exact rank formula for concatenations from rigid seeds.

PermanentDeterminantalLowerBound_CharZero_AllSizes.lean — A Mathlib-only proof that every size-\(m\) affine determinantal representation of the \(n\times n\) permanent over any characteristic-zero field satisfies \(n^2\le 2m\), strengthened to \(n^2+2\le 2m\) whenever \(n\ge3\). Equivalently, \(\operatorname{dc}(\mathrm{perm}_n)\ge\lceil n^2/2\rceil+1\) for every \(n\ge3\), improving the rounded Mignon–Ressayre (2004) bound by one for both even and odd sizes. Recovers their original theorem as an explicit corollary. This is an additive improvement, not an asymptotic improvement or a separation of VP from VNP; priority relative to subsequent literature remains unverified.

BentDesignRank.lean - A refutation of Hyun, Kwon, Wang, and Wu’s (2026) Open Problem 7: “Do the designs D_{g,h} and TD_h in Theorem 10 always have equal binary ranks?”; here an explicit eight-variable counterexample is formally verified in Lean, satisfying every bent-function and duality hypothesis, with binary ranks 29 and 30 respectively.

MetricRegularBent.lean - An affirmative answer to Meidl, Polujan, and Pott’s (2023) Question 5.16: “Can the set C_F for some (n,m)-bent function F be metrically regular?” Here the code C_q = RM(4,1) + ⟨q⟩ for q = x₁x₂ + x₃x₄ is formally proved equal to its double metric complement. The formalization also verifies that q is extendable by exhibiting g such that q, g, and q + g are all bent. This establishes the requested existence for an extendable (4,1)-bent function; literature priority remains unverified.

DMT17.lean - An affirmative answer to Ding, Munemasa, and Tonchev’s (2019) Conjecture 17: “For each fixed admissible output dimension, does the number of inequivalent codes obtained from vectorial bent functions grow exponentially, with the proportion admitting a two-transitive automorphism group tending to zero?” Here both assertions are formally proved, with the stronger conclusion that even the proportion admitting a transitive automorphism group tends to zero, and quantitative bounds uniform across all admissible output dimensions.

ProductBasisErrorOptimumAndFourMeasurementSpectralBounds.lean — A Mathlib-only proof that four orthonormal product bases in \(\mathbb C^2\otimes\mathbb C^3\), including indirect bases, have minimum total squared unbiasedness error exactly \(2/3\), with explicit attainment and complete classification of all minimizers. Resolves a special case of the arbitrary-rank spectral-bound extension explicitly left open after Designolle–Farkas’s Theorem 9: four projective measurements containing a pairwise mutually unbiased triple, with any fourth PVM. Also proves sharp product-basis minimax corollaries and a strict dimension-six spectral improvement of \(1/583200\). The unrestricted conjecture remains open. Fully Lean-verified using only Mathlib, without placeholders or custom axioms.

FiveIsoentangledETF.lean — A proof that every two-qubit entanglement spectrum admits a five-state equiangular tight frame. Gives an explicit construction spanning product to maximally entangled states, with squared pairwise overlap 1/16 and frame operator (5/4)I. Provides a uniform analytic solution to the existence question explored numerically in Section IV of Wei–Cobucci–Tavakoli, Nonprojective Bell-state measurements (2024).

ETFAllDimensionsAllPurities.lean — A proof that every integer d ≥ 2 admits an equiangular tight frame of d² + 1 normalized bipartite states with any prescribed common reduced purity p ∈ [1/d, 1]. Includes the maximally entangled endpoint, answering the higher-dimensional existence question in Section IX of Wei–Cobucci–Tavakoli’s Nonprojective Bell-state measurements (2024), and extends Section IV’s entanglement-tuning observations to all dimensions at the level of purity.

MaximallyEntangledTightFrame_ExactOneWayPPTOptimum.lean - Proves that every maximally entangled tight frame of \(N\) states in \(\mathbb C^d\otimes\mathbb C^d\), for \(d\ge2\), has exact uniform-prior, single-copy discrimination optimum \(d/N\): an explicit one-way protocol achieves it, and no PPT measurement can exceed it. Includes the exact five-state qubit value \(2/5\), resolving the numerical one-way shortfall reported by Wei–Cobucci–Tavakoli (2024), Section VII.

FiveStateRegularSimplex_TwoCopyGlobalOptimum.lean - Proves that two identical copies of any five-state regular simplex, sampled uniformly, have exact global discrimination optimum \((13+4\sqrt3)/20 \approx 0.9964101615\). Constructs an attaining POVM and proves a matching universal upper bound, giving an exact regular-simplex formulation of the numerical result reported by Wei–Cobucci–Tavakoli (2024), Section VII.

JouxNarayanan54.lean - An affirmative answer to Joux–Narayanan’s Question 5.4: “Does ordinary tensor isomorphism reduce to tensor isomorphism under special-linear transformations?” Here zero-padding each mode from dimension n to 2n is formally proved to preserve and reflect equivalence over every field, for arbitrary input tensors. The proof certifies an explicit coordinate projection with exactly eight times as many output entries, establishing TI ≤ TI_SL.

TIEqTISp.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)'s Open Question 8: "Which, if any, of TI_O, TI_U, TI_Sp are equal to TI?"; here it is proved that TI = TI_Sp.

TIParStandalone.lean - Resolves the maximal-parabolic case of Chen, Grochow, Qiao, Tang, and Zhang’s (2024) research direction in §1.5: “What are the tensor-isomorphism complexity classes associated with other matrix groups, including parabolic subgroups?”; here TI = TI_Par is proved for the maximal parabolic family P_(n,n) over every field, under coordinate-projection reductions with polynomial output-size bounds. This addresses an explicitly proposed research direction, rather than a numbered open question.

FormTI.lean - A partial answer to Chen, Grochow, Qiao, Tang, and Zhang (2024)’s Open Question 1.11: “What is the complexity of tensor isomorphism restricted to other form-preserving groups, including mixed orthogonal groups and groups preserving forms that are neither symmetric nor skew-symmetric?”; here TI-completeness is proved for seven form-isometry families, including O(n,n), O(3n,n), and families preserving nonsymmetric or degenerate bilinear forms, under coordinate-projection reductions with polynomial output-size bounds.

TStarUnimodality.lean - A complete answer to Iršič, Klavžar, Rus, and Tuite’s (2024) Problem 5.2: “Which thick grids have unimodal general-position polynomials?” For m = min(r,a) and n = max(r,a), non-unimodality holds exactly when m = 2 and n = 8; m = 3 and 11 ≤ n ≤ 17; or m ≥ 4 and 2m + 4 ≤ n ≤ m + (m + 1)(1 + (m − 1)!). The classification is formally verified in Lean for all positive parameters, including the graph-counting formula and every exceptional case; literature priority remains unverified.

FangCounterexample.lean - A refutation of Fang’s (2017) Conjecture 2.9: “Does identical collapse tomography at every vertex imply that a graph is vertex-transitive?”; here a ten-vertex counterexample is formally verified in Lean. The classical Tutte 12-cage also refutes the conjecture, as noted in the file; priority for the explicit refutation remains unverified.

CFR525.lean - An affirmative answer to the CFR(5,25) open instance listed by Rosin’s CPro1 (2025), originating from the Handbook of Combinatorial Designs, §VI.62: “Does a 5 × 25 circular Florentine rectangle exist?” Here an explicit witness is formally verified in Lean, proving F_c(25) ≥ 5. This resolves the existence instance, not the exact value of F_c(25).

-------------------------------------------

Pending formalizations:
* Chizewer, Everett, Mithal, and Qiao (2026) [https://arxiv.org/html/2603.27128v1] — Open Problem 4: “Can average-case polynomial-time algorithms be devised for tensor orthogonal and unitary isomorphism over finite fields?”; also Li, Li, Qiao, Tao, and Wang (2026) [https://arxiv.org/html/2604.00591v1] — Problem 1.8: “Can average-case polynomial-time algorithms be devised for 3-tensor isomorphism over finite fields under orthogonal and unitary group actions?” — Here answered affirmatively for cubical tensors under the standard matrix-isometry actions.


<!-- bivariate-polynomial-rank-separations:start -->
### Bivariate Polynomial Rank Separations via Squared Interpolation (informal)

[Proof](BivariatePolynomialRankSeparations/Proof.md). Proves all three clauses of [De las Cuevas–Klingler–Netzer, Conjecture 46](https://arxiv.org/abs/2109.06680). Squared Lagrange interpolation transfers known matrix rank separations to bivariate real polynomials and preserves ordinary, separable, and SOS-purification ranks exactly.

### Classical-group tensor isomorphism (Lean)

[OrthogonalTIStandalone.lean](OrthogonalTIStandalone.lean) — Orthogonal tensor isomorphism reductions under the stated split-form hypotheses and in characteristic two, with an affine reduction obstruction over ordered fields. Partial progress on Chen–Grochow–Qiao–Tang–Zhang, Open Question 7.1.

[LeviHardnessStandalone.lean](LeviHardnessStandalone.lean) — Tensor isomorphism hardness for five group actions under the file's GL Levi-section hypotheses, with a special-linear instance.

[UnitaryTransporterFibersStandalone.lean](UnitaryTransporterFibersStandalone.lean) — A transporter-fibre equivalence and matching cardinalities for hyperbolic unitary padding, with an isomorphism decision equivalence under the stated Hermitian-form hypotheses.
<!-- bivariate-polynomial-rank-separations:end -->


<!-- concise-tensor-degeneration-depth:start -->
### Quadratic Degeneration Depth on the Concise Tensor Locus (informal)

[Proof](ConciseTensorDegenerationDepth/Proof.md). Constructs quadratic-length strict degeneration chains for ordinary and special-linear tensor isomorphism even when all three flattenings have full rank, an identity slice is fixed, and the entire slice determinant polynomial is constant across the chain. Also constructs actions with closed individual orbits and arbitrarily high difference rank of the orbit relation. The first result strengthens the pencil-chain construction to the concise fixed-determinant setting. Publication priority remains unverified.
<!-- concise-tensor-degeneration-depth:end -->


<!-- kronecker-degeneration-depth:start -->
### Exact Degeneration Depth of Matrix Pencils (informal)

[Proof](KroneckerDegenerationDepth/Proof.md). Computes the longest strict-equivalence degeneration chain for complex square pencils, with exactly n(n+1)/2 steps, and for n × (n+1) pencils, with n(n+1)/2+n steps. A potential on Kronecker data handles all eigenvalues. Also gives the exact special-linear square height and the difference level on fixed finite spectral support. This answers the exact-height question raised in the Depth Hierarchy work. Publication priority remains unverified.
<!-- kronecker-degeneration-depth:end -->


<!-- linear-length-classical-tensor-actions:start -->
### Linear-Length Reductions Between the Five Classical Tensor Actions (informal)

[Proof](LinearLengthClassicalTensorActions/Proof.md). Answers the linear-length question in Chen–Grochow–Qiao–Tang–Zhang, Section 1.5, for standard complex and finite-field unitary groups and standard orthogonal groups. Two rank-marked slices recover each coordinate block by intersection. All five actions are pairwise equivalent via constant-free kernel p-projections with linear side-length blow-up, uniformly over the field. [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)
<!-- linear-length-classical-tensor-actions:end -->


<!-- arbitrary-tensor-matrix-space-projections:start -->
### Projection Reductions from Arbitrary Tensors to Matrix Spaces (informal)

[Proof](ArbitraryTensorMatrixSpaceProjections/Proof.md). Answers Grochow and Qiao's question in Remark 2.5 of *Tensor Isomorphism-Completeness* for both alternating matrix-space isometry and matrix-space conjugacy. The reductions satisfy all five requested properties on arbitrary 3-tensors over any field, including degenerate tensors, with linear output side lengths. The alternating projection is in the independent alternating coordinates. [Original question](https://doi.org/10.1137/21M1441110)
<!-- arbitrary-tensor-matrix-space-projections:end -->


<!-- determinant-cosets-by-castling:start -->
### Determinant Cosets from Castling and Normalized Matrix Pencils (informal)

[Proof](DeterminantCosetsByCastling/PROOF.md). Computes the joint transporter determinant coset over F3 with ordinary TI decision in time exponential only in the smaller flattening rank or image codimension, and polynomial in the written input size. Includes rank-deficient flattenings and arbitrary stabilizers, with a separate polynomial test for anchored pencils with a squarefree trace operator. Partial progress on Chen–Grochow–Qiao–Tang–Zhang Open Question 1.9. [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)
<!-- determinant-cosets-by-castling:end -->


<!-- november-14-tensor-results:start -->
### Degree Raising for Form Equivalence (informal)

[Proof](FormDegreeRaising/Proof.md). Resolves the fixed-degree reduction proposed in Appendix A of Grochow and Qiao's *Tensor Isomorphism-Completeness*. The proposed monomial padding works exactly when every nonzero (d-m)-th power is an m-th power. A replacement kernel reduction works over every field for each fixed m < d. [Original question](https://doi.org/10.1137/21M1441110)

### Linear-Length Reductions Between Classical Tensor Actions (informal)

[Proof](FiniteUnitaryLinearLength/Proof.md). Answers the linear-length question in Chen, Grochow, Qiao, Tang and Zhang's Section 1.5 for standard unitary actions over finite fields and over the complex numbers, and standard orthogonal actions over the reals. Fixed couplings and rank markers give reductions in all directions with linear output side lengths. [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)

### A Single Fully Symmetric Cubic Is TOCI-Complete (informal)

[Proof](SymmetricCubicOCI/Proof.md). Strengthens our earlier answer to Lysikov and Walter's Question I.14. Orbit closure intersection for one fully symmetric tensor under the complex orthogonal group is TOCI-complete in each fixed degree at least three. The reduction packs two unrestricted cubics into a single symmetric cubic using closed marker orbits and the Laplacian splitting. [Original question](https://arxiv.org/html/2411.04639v2#S1.SS4)

### Exact Tensor Isomorphism with Arbitrarily Small Discrete Noise (informal)

[Proof](SmoothedOrthogonalUnitaryTI/Proof.md). Gives a bounded rational-grid version of the exact smoothed decision problem in Chizewer, Everett, Mithal and Qiao's Open Problem 2. The algorithm is deterministic and polynomial in the input bits. With high probability over arbitrarily small noise added to the first tensor, it decides orthogonal or unitary isomorphism for every second tensor. This complements the Gaussian result in [MathProofs Crossovers](MathProofsCrossovers/PROOF.md). [Original question](https://arxiv.org/html/2603.27128v1#S1.SS5)

### Pure-Power Tensor Orbit-Closure Dichotomy (informal)

[Proof](PureTensorOCIDichotomy/Proof.md). Classifies the pure-power single-group part of Lysikov and Walter's Question I.12. For fixed primal and dual maximum orders, orbit closure intersection is TOCI-complete if both orders are at least two and one is at least three. The remaining pure-power cases are in polynomial time over rational or fixed number field coefficients. [Original question](https://arxiv.org/html/2411.04639v2#S1.SS4)

### Classification of Tensor Orbit Closures for One General Linear Group (informal)

[Proof](SingleGroupOCIClassification/Proof.md). Classifies every fixed single-group tensor tuple signature with rational input coordinates into deterministic polynomial-time, EqSLP-complete, or TOCI-complete cases. EqSLP is the zero test for integer straight-line programs and belongs to coRP. This extends the pure-power result to mixed slots and gives the one-group part of Lysikov and Walter's Question I.12 with a separate bit-complexity classification. [Original question](https://arxiv.org/html/2411.04639v2#S1.SS4)
<!-- november-14-tensor-results:end -->


<!-- november-14-frontier-round-two:start -->
### Subcubic Homomorphisms Distinguish Graphs of Adjacency Nullity Two (informal)

[Proof](SubcubicNullityTwo/Proof.md) and [exhaustive C++ verifier](SubcubicNullityTwo/CheckSmallSubcubic.cpp). Answers Maehara's Problem 2 affirmatively. Equal subcubic homomorphism counts imply isomorphism when the adjacency matrix has nullity at most two. The proof uses a tensor splitting theorem to reduce every possible exception to an exact calculation on at most eight vertices. Maehara's nullity-three examples show the bound is sharp. [Original question](https://arxiv.org/html/2610.09042v2#S5)

### Quantum Nonvanishing and Logarithmic Degree for Graph Homomorphisms (informal)

[Proof](BoundedDegreeHomomorphismNonvanishing/Proof.md). Answers Cai and Young's question following Corollary 6.2. For every degree bound of at least two, the equality and adjacency signature family is quantum-nonvanishing exactly when the adjacency matrix is nonsingular. The proof also determines the least adjacency nullity at which degree-$d$ probes can fail to distinguish nonisomorphic graphs for every $d\ge4$. The threshold is $2^d-d-2$. [Original question](https://arxiv.org/html/2509.10991v1#S6.SS1)

### Classification of Tensor Orbit Closures for Products of General Linear Groups (informal)

[Proof](ProductGroupOCIClassification/Proof.md). Answers the three concrete completeness questions in Lysikov and Walter's Question I.12. Every fixed product-group tensor signature on rational inputs gives a problem in P, one equivalent to integer straight-line-program zero testing (EqSLP), or a TOCI-complete problem. This gives a randomized dichotomy and identifies the additional complexity statement required for the deterministic dichotomy. [Original question](https://arxiv.org/html/2411.04639v2#S1.SS4)

### Exponential Sparse Polynomial Calculus Lower Bounds for Tensor Isomorphism (informal)

[Positive characteristic](TensorSparsePCBounds/Proof.md) and [characteristic zero](TensorSparsePCBounds/CharacteristicZero.md). Proves sparse monomial-count lower bounds exponential in the tensor side length for the standard 3-tensor isomorphism equations over every fixed field. The positive-characteristic construction also applies to the standard matrix conjugacy, congruence and equivalence equations. This addresses the lower-bound directions of Galesi, Grochow, Pitassi and She's Open Questions 7.2 and 7.3. [Original questions](https://arxiv.org/html/2305.19320#S7.SS2)

### Orthogonal Tensor Isomorphism with Marginal Multiplicity Two (informal)

[Proof](OrthogonalMultiplicityTwo/Proof.md). Gives a randomized polynomial bit-time algorithm from raw rational tensors of fixed order when every mode Gram eigenspace has dimension at most two, including tensors with arbitrary zeros. This addresses the real orthogonal multiplicity-two case of Chizewer, Everett, Mithal and Qiao's Open Problem 5. [Original question](https://arxiv.org/html/2603.27128v1#S1.SS5)

### Explicit Output Lower Bound for Graph Separating Modules (informal)

[Proof](GrochowUrismanExplicitOutput/Proof.md). Rules out a uniform runtime of $f(d)n^{o(d)}$ for outputting the expanded polynomial lists used in Grochow and Urisman's Theorem 3.1. This answers the sublinear-exponent version of the first part of Open Question 1.10 in that explicit output model. [Original question](https://arxiv.org/html/2606.26244v2)

### Treewidth Alone Cannot Bound Symmetric Subgraph Circuits (informal)

[Proof](GrochowUrismanSymmetricSubgraphCircuits/Proof.md). Answers the symmetric-circuit form of Grochow and Urisman's Open Question 1.11 in the negative. Matchings of treewidth one defeat every size bound of the proposed form, even with an arbitrary pattern-dependent factor. This is a deduction from Dawar, Pago and Seppelt's published classification for sublinear bipartite patterns. [Original question](https://arxiv.org/html/2606.26244v2)
<!-- november-14-frontier-round-two:end -->


<!-- determinant-character-reductions-november-14:start -->
### Every Determinant Character Reduces to Unit-Side SL-TI (informal)

[Proof](SLCharacterNormalization/Proof.md). Gives a deterministic same-field reduction for every prescribed determinant character over each fixed finite field, including when $q-1$ has repeated prime factors. The target is a pair of associative multiplication tensors of equal cubic side length congruent to one modulo $q-1$. The side grows linearly in the sum of the input sides at fixed field size. This restricts the targets needed for the forward direction of Chen, Grochow, Qiao, Tang and Zhang's Open Question 1.9. [Original question](https://arxiv.org/html/2306.03135v2#S1.SS5)

### Determinant Recovery from Paired Bilinear Forms (informal)

[Proof](SLResidualBilinearForms/Proof.md). Gives an exact ordinary-TI construction for anchored branches over each fixed finite field. It reads the determinant on a large residual space through the adjoint algebra of a paired tuple of bilinear forms. The exterior-algebra cost only depends on the dimensions of the simple factors whose determinant contributions survive. Explicit growing families separate this criterion from the earlier successive-radical bound.

### Raw Anchor Recovery from Rank-One Slice Frames (informal)

[Proof](SLRawRankOneAnchors/Proof.md). Gives a deterministic polynomial-time determinant-profile algorithm for a raw pencil class with a large rank-one frame, a bounded-dimensional quotient, and a checkable matrix-generation condition. The proof recovers the frame and generates matched anchors from the original tensors. The class includes growing scalar-adjoint examples up to arbitrary independent basis changes.

### Determinant Characters from Quadratic Pencil Factors (informal)

[Proof](SLQuadraticPencilCharacters/Proof.md). Gives a same-field many-one reduction from SL-TI to ordinary TI over $\mathbb F_3$ on an odd balanced pencil class. The geometric determinant factors have bounded degree and a fixed common field of definition. Two quadratic factors whose matrix ratio has squarefree characteristic polynomial suffice, even with an unbounded number of other factors. The construction recovers the relevant factors and reads the label determinant using the resulting commutative algebra.
<!-- determinant-character-reductions-november-14:end -->


<!-- step-17-determinant-reductions-november-14:start -->
### Determinant Profiles from Bounded-Rank Peirce Frames (informal)

[Proof](SLBoundedRankFrames/Proof.md). Gives a deterministic ordinary-TI Turing reduction for truncated triangular multiplication tensors with a raw bounded-rank slice frame of bounded codimension. The complementary blocks can grow arbitrarily. The algorithm computes the full determinant profile and needs no supplied frames.

### Quadratic Pencil Orientation over Separate Factor Fields (informal)

[Proof](SLSeparateFactorFields/Proof.md). Gives a deterministic same-field many-one reduction for total-determinant-one TI over fixed odd finite fields when the absolute pencil factors have bounded degree and two quadratic factors give a nonsingular denominator and a squarefree ratio. Individual factors may require a common splitting field of superpolynomial degree.

### Determinant Characters from Quadratic Pencils with Repeated Spectrum (informal)

[Proof](SLRepeatedPencilSpectrum/Proof.md). Gives a same-field many-one reduction for a weighted label and matrix determinant character with two quadratic factors. It handles repeated and nilpotent ratios when the contributing primary multiplicity widths are logarithmic and either the factor count is bounded or a one-dimensional residue-field terminal represents the matrix determinant ratio.

### Raw Pfaffian Tests for Tensor Determinant Characters (informal)

[Proof](SLCartanPfaffian/Proof.md). Gives a deterministic same-field many-one reduction for the total determinant under a bounded-degree, bounded-count Pfaffian factor promise. A growing raw family has a polynomial-time filter for all determinant characters, including the weights arising from the triangular multiplication construction.
<!-- step-17-determinant-reductions-november-14:end -->


<!-- tensor-determinant-character-compilers-november-14:start -->
### Determinant Characters from Intrinsic Tensor Summands (informal)

[Proof](SLIntrinsicSummands/Proof.md). Recovers the intrinsic direct summands of a concise tensor and compiles their exact determinant test into one ordinary TI instance when polynomially computed invariant buckets have logarithmic size and the local character tests have many-one reductions. A local-centroid terminal reads the determinant through Jordan-length quotients of an intrinsic principal nilpotent ideal. Omitting optional normalization padding reduces arbitrary tensors to a constant list of concise indecomposable multiplication-tensor character tests.

### Determinant Characters from Singular Anchored Slices (informal)

[Proof](SLSingularAnchorFlags/Proof.md). Gives a single ordinary TI instance for ordered anchored slices when the relevant simple-module widths are logarithmic. It allows singular and rectangular slices and arbitrary finite center degrees. It also recovers the anchor choices from raw inputs in an everywhere-singular family built from left and right Kronecker blocks. High multiplicities of just two such blocks can encode an arbitrary concise prescribed-character instance.

### Raw Tensor Matching from a Tuple of Determinant Factors (informal)

[Proof](SLMatchingDeterminantFactors/Proof.md). Computes the full transporter determinant profile in polynomial time over each fixed odd finite field when the absolute determinant factors have bounded degree and a constant tuple of recovered factors gives a nonsingular rational combination and a logarithmic-dimensional space of relative intertwiners. Additional marks can be defined over separate extension fields. No anchors are supplied. An explicit growing family has scalar stabilizer, no rank-one slice, and only singular quadratic determinant factors.

### Determinant Characters from Radical Symbols of Anchored Pencils (informal)

[Proof](SLRadicalSymbolDeterminants/Proof.md). Builds further module equations from paired anchored slices and a prescribed label quotient map. Extracts the equations through the radical layers and removes unknown scalar shears by a characteristic-power polynomial. A growing example with a nonsemisimple anchor algebra and an unbounded initial active width has new width one.
<!-- tensor-determinant-character-compilers-november-14:end -->


<!-- tensor-scalar-shear-and-singular-reductions-november-14:start -->
### Determinant Cosets from Marked Slice Modules (informal)

[Proof](SLSliceShearCosets/Proof.md). Gives a deterministic polynomial-time algorithm for simultaneous conjugacy of ordered matrix tuples up to independent scalar shifts. It computes all shifts and the exact determinant coset. This closes the marked scalar-shear case for tensor pencils with an invertible anchor and prescribed label quotient. A separate iterative bimodule relaxation gives one ordinary TI instance on broader marked branches under a computable determinant-image or surviving-width condition.

### Exact Determinant Profiles from Singular Quadratic Factors (informal)

[Proof](SLRawSingularFactors/Proof.md). Gives a raw polynomial-time determinant-profile algorithm over each fixed finite field, including even characteristic, under a local determinant-factor and affine-dimension criterion. The pencil may be rectangular or identically singular. Only the indecomposable regular summands supplying the chosen marks need bounded-degree determinant factors.

### Nonadaptive Determinant-Profile Assembly for Intrinsic Tensor Summands (informal)

[Proof](SLParallelSummandAssembly/Proof.md). Assembles the exact determinant profile using O(N) parallel ordinary TI queries for N summands of arbitrary unknown isotypes, given local many-one determinant tests. It also gives a one-instance construction when the number of isotypes or the exact class multiplicities are supplied, and a separate one-instance result when object-wise local tests need only a bounded number of orientation corrections.

### Special-Linear Tensor Isomorphism on Everywhere-Singular Pencils (informal)

[Proof](SLEverywhereSingularPencils/Proof.md). Gives a deterministic same-field many-one equivalence between balanced unit-side multiplication-tensor SL-TI and a raw class of everywhere-singular square pencils. A binary-form marker, ordered Kronecker blocks and determinant-preserving shears implement the reduction in linear mode dimensions at fixed field size. It preserves SL-TI with no supplied anchors.
<!-- tensor-scalar-shear-and-singular-reductions-november-14:end -->


<!-- marked-shears-and-frobenius-determinants-november-14:start -->
### Exact Marked Shears via Quotient Flags and Spectral Shifts (informal)

[Proof](SLMarkedShearAlgorithms/Proof.md). Gives a polynomial-time ordinary-TI Turing reduction for the full determinant profile of any prescribed marked-subspace and label-quotient branch, with arbitrary nonscalar shears. Spectral compression lists at most n feasible scalar shifts on an n-dimensional matrix tuple. It gives oracle-free algorithms for several nonscalar anchor classes.

### Determinant Profiles for Long Nilpotent Anchors (informal)

[Proof](SLLongNilpotentAnchors/Proof.md). Gives an oracle-free polynomial-time determinant-profile algorithm for prescribed branches with a commutative split local anchor algebra, free modules, commuting residual slices, and residual endomorphism quotient a product of base fields. The nilpotence length and radical dimensions are unrestricted.

### Algebra-Isomorphism Determinants from the Frobenius Socle (informal)

[Proof](SLFrobeniusSocle/Proof.md). Uses the right regular module of a Frobenius algebra to read the determinant square from socle norms, with polynomial-time ordinary-TI tests for bounded numbers of simple factors and logarithmic simple matrix sizes. Over any fixed field complementary radical-annihilator filtration cells cancel in pairs, leaving exact determinant tests when the diagonal cells are small or admit the specified alternating forms.

### Determinant-One Isomorphism of Local Frobenius Algebras (informal)

[Proof](SLLocalFrobeniusTwists/Proof.md). Gives a single ordinary TI test for determinant-one isomorphism of every local Frobenius algebra in characteristic two. For odd fields, a square-zero filtration and the residue-field twists of its middle multiplication remove paired determinants, with exact width-free examples over quadratic residue fields.
<!-- marked-shears-and-frobenius-determinants-november-14:end -->
