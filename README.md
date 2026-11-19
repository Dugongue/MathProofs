Lean proofs obtained and formalized with use of AI models, namely some combination of Claude Opus 5/5.5, Claude Fable 5/5.1, GPT-5.6 Sol and GPT-6 Astra.
I've tried to assert the novelty of these proofs: all are pending comprehensive human validation and formal writeups.
Each Lean file imports only Mathlib.

----------------------------------
INFORMAL PROOFS (not formalized yet)

<!-- hypothesis-world-extensions:start -->
- [Modular Hom profiles for graphs and finite-field modules](HypothesisWorldExtensions/Results.md) — Informal proofs and executable hypothesis ledger. Two moduli have identical attainable agreement patterns when the module field is allowed to vary. Three suffice to distinguish graphs from modules, and minimally impossible module patterns occur at every arity from three onward. Includes results on exact oracle extraction, rational projector feasibility and low-bit evaluation for binary codes.
<!-- hypothesis-world-extensions:end -->

<!-- grochow-question-equivalences:start -->
- [Grochow questions on oracle extraction, subgraph circuits and canonization](GrochowQuestionEquivalences/Results.md) — Informal proofs. Linear-degree, absolutely irreducible counterexamples to exact and border determinant and Pfaffian oracle extraction in fixed positive characteristic; an equivalence between ordinary subgraph circuits and VFPT = VW[1], already for paths; two oracle-level canonization equivalences; and complete invariants for binary modular-matrix subgroup equality.
<!-- grochow-question-equivalences:end -->

<!-- four-logspace-results:start -->
- [Four logspace results on groups, signed isomorphism, tensors and grids](FourLogspaceResults/Results.md) — Informal proofs. Includes canonical constructive membership for fixed finitely presented subgroups of residually free groups, the five/six threshold for deciding and counting signed transporters, parity-logspace completeness in supplied rank-one tensor completions over the three-element field, and a treewidth classification for normalizing supplied constraint solutions.
<!-- four-logspace-results:end -->

<!-- word-and-fiber-canonization:start -->
- [Canonical words, perfect matchings and local invariants](WordAndFiberCanonization/Results.md) — Informal proofs. A fixed finitely generated subgroup of SL₄(ℤ) has logspace word normal forms exactly when L = NP, and polynomial-time word normal forms exactly when P = NP. Further results cover intrinsic word-length approximation, rank-one matrices measured one or two entries at a time, bounded-degree three-dimensional matching with a supplied solution, average-case selection from two-element classes, and the Boolean locality threshold.
<!-- word-and-fiber-canonization:end -->

<!-- canonization-consequences:start -->
- [Complete invariants and canonical representatives](CanonizationConsequences/Results.md) — Informal proofs of two Fortnow–Grochow logspace implications, a characterization of Grochow’s thesis Question 3.14, an average-case bounded-depth separation on equal-length pairs, and a circuit equivalence between canonization and preimage search. [Length and ambiguity refinements](CanonizationConsequences/Refinements.md).
<!-- canonization-consequences:end -->

<!-- tensor-stabilizer-descent:start -->
- **[Nonsplit graph tensors and principal determinants over local algebras](TensorStabilizerDescent/Results.md)** — Informal proofs reducing special-linear isomorphism of geometric graph tensors and their arbitrary-order truncated-series deformations to GI, and unrestricted special-linear isomorphism over each fixed commutative binary local algebra with residue field of order two to ordinary binary TI. Includes a priority audit of the integral graph stabilizer theorem.
<!-- tensor-stabilizer-descent:end -->

<!-- exact-tensor-transporters:start -->
- **[Exact transporters for codes, graphs, tensor summands and graphical groups](ExactTensorTransporters/Results.md)** — Informal proofs of witness-preserving special-linear three-tensor encodings for permutation and monomial code equivalence over each fixed finite field and an integral graph encoding realizing every finite group as the full special-linear stabilizer scheme of one concise tensor. Includes prescribed graph parity, prime-power graphical group recognition and counting, and ordinary TI reductions for logarithmic-width tensor summands.
<!-- exact-tensor-transporters:end -->

<!-- graph-tensor-witness-transfer:start -->
[Witnesses, counts and canonical forms between graphs and three-tensors](GraphTensorWitnessTransfer/Results.md) — Informal proofs of an exact binary graph-to-tensor witness correspondence, a hidden-coordinate decoder, graph algorithms for structured tensors, parity tests, and an exponential size lower bound for graphs whose automorphisms surject onto all tensor symmetries. Includes proofs, scope and two finite checks.
<!-- graph-tensor-witness-transfer:end -->

<!-- transportensor-foundations:start -->
[Transportensors, Transportensor Isomorphism and Automorphism](TransportensorFoundations/Transportensors.md) — Formal definitions and informal proofs of TI-completeness over fixed finite fields for an expressive fixed signature, an automorphism exact sequence, and witness-preserving comparisons of classical-group variants. Includes the input model, limits and checked finite examples.
<!-- transportensor-foundations:end -->

<!-- tensor-symmetry-recovery:start -->
[Four results on coordinates and symmetries of tensor networks and graph actions](TensorSymmetryRecovery/Results.md) — Informal GI reductions using unordered vectors and covectors or closed walks, exact counting for residual shear symmetries, and sharp observation arities for reconstructing costed groupoid actions. Includes proofs, input hypotheses and finite checks.
<!-- tensor-symmetry-recovery:end -->

<!-- tensor-transport-recovery:start -->
[Recovering coordinates and counting isomorphisms in tensor networks with transport](TensorTransportRecovery/FourTheorems.md) — Informal proofs of a GI equivalence on a recognizable class, singular cycle and root reconstruction, and exact equivariant isomorphism counts with unknown vertex and group correspondences. Includes explicit hypotheses and finite checks.
<!-- tensor-transport-recovery:end -->

<!-- seven-isomorphism-types:start -->
[Seven object types for tensor, group and graph isomorphism](SevenIsomorphismTypes/SevenTypes.md) — Proposed terminology and informal definitions with fully faithful native embeddings and a root transport theorem for invertible edge maps over a specified combinatorial isomorphism.
<!-- seven-isomorphism-types:end -->

<!-- grochow-functor-lifting:start -->
[Functorial tensor reductions and structured group epimorphisms](GrochowFunctorLifting/Results.md) — AI-assisted informal proofs with separate mathematical audits. Answers specified directions of Grochow–Qiao Open Question 7.5 and proves sufficient polynomial-time cases for characteristic-two Matrix Tuple Isometry and Grochow–Srivastava–Thakkar Questions 3(3)–(4), including equal-order-complement two-prime towers and Frobenius-source genus-two groups. The unrestricted questions remain open; no Lean certification or novelty claim.
<!-- grochow-functor-lifting:end -->

<!-- constrained-epimorphism-campaign:start -->
- [Constrained epimorphisms, characteristic-two lifting, and counting optima](ConstrainedEpimorphismCampaign/Results.md) — Informal proofs of polynomial-time counting for marked ordinary persistence maps versus NP-complete existence on alternating zigzags, compact finite-ring surjection algorithms, broader symplectic norm lifting, and counting classifications for integer homology and geometric lattices. Exact scopes, dependencies, and unresolved published questions are stated.
<!-- constrained-epimorphism-campaign:end -->

<!-- quotient-fiber-counting:start -->
- [Quotient–fiber lifting for surface cycles, posets, Sylow towers, and matrix tuples](QuotientFiberCounting/Results.md) — Informal proofs of hardness for counting additional shortest surface cycles from a supplied optimum, an antichain-counting threshold at order dimension three, and polynomial-time algorithms for specified group and matrix classes. Earlier resolutions of the published surface and poset questions are credited.
<!-- quotient-fiber-counting:end -->

<!-- quotient-fiber-lifting-four:start -->
- [Four applications of quotient–fiber lifting](QuotientFiberLiftingFour/Results.md) — Informal proofs for characteristic-two matrix-tuple isometry, finite-group epimorphisms, central quotients, and cross-length complete invariants. Each addresses a restricted case or a structural consequence of a published question.
<!-- quotient-fiber-lifting-four:end -->

<!-- grochow-questions-after-vertex-cover:start -->
- [Monotone permanent-oracle lower bounds and three isomorphism results](GrochowQuestionsAfterVertexCover/Results.md) — Informal affirmative answer to Grochow’s Open Question 5.6 on formal polynomials, including arbitrary-depth monotone c-reductions. The packet includes two derivations, an application to vertex-cover degree spectra, and scoped results on tensors, groups and graphs.
<!-- grochow-questions-after-vertex-cover:end -->

<!-- vertex-cover-and-extension-spectra:start -->
- **[Vertex Cover and extension-field isomorphism](VertexCoverAndExtensionSpectra/Results.md)** — Informal proofs connecting finite étale tensor extension degrees to covering constraints, signed versus ordinary encoding size, counting, approximation, polynomial families, and reconfiguration. Includes transfers to cubic forms, alternating spaces, two-step Lie algebras, and indexed families of graphs and groups.
<!-- vertex-cover-and-extension-spectra:end -->

<!-- four-transport-programs:start -->
- **[Four directions in tensor isomorphism](FourTransportPrograms/Results.md)** — Informal theorems on selecting the minimum extension degree for tensor isomorphism, random Koszul flattenings for determinant tests, recovery and matching of tensor blocks with a shared core, and measurement masks for monomial tensor alignment. Includes proofs, precise input promises, and conjectures.
<!-- four-transport-programs:end -->

<!-- transporting-structure-proposals:start -->
- **[Twenty research proposals on transporting structure](TransportingStructure/Proposals.md)** — Provisional definitions and informal results on witness-preserving reductions, partially observed tensors, calibration, and the cost of exact isomorphism witnesses. Includes a sharp rank-error decoding threshold for protected tensor copies and a factorial field-degree example for ordinary 3-tensor transporters over the reals.
<!-- transporting-structure-proposals:end -->

<!-- grochow-hypothesis-ledger-expansion:start -->
- **[Grochow Hypoworlds expansion](GrochowHypoworldsExpansion/README.md)** — Expanded implication ledger with exact pair and triple replay, characteristic-two matrix-tuple isometry and involutive-algebra norm equivalences, new finite-alphabet coarse-graining hardness, a colored group pebble-game separation, and rational-oracle and IPS degree results. Informal proofs.
<!-- grochow-hypothesis-ledger-expansion:end -->

<!-- november-isomorphism-and-hitting-sets:start -->
- **[November results on isomorphism and algebraic hitting sets](NovemberIsomorphismAndHittingSets/Research.md)** — Informal proofs on indistinguishable colored groups, symmetry-characterized graphs, simultaneous monomial code equivalence, and a clause-local obstruction to 3CNF hitting sets. Includes the scope and dependence of consequences for published open questions.
<!-- november-isomorphism-and-hitting-sets:end -->

<!-- grochow-82-hypothesis-ledger:start -->
- **[Grochow question hypothesis ledger](GrochowHypoworlds/README.md)** — Replays signed implications and contradictions across the 82-row research catalog. Includes informal all-block-size proofs for Song–Grochow's sixteen-rule census, a unary fixed-block noncompleteness result, and exact high-power oracle obstructions for the constant-depth determinantal-ideal and degree-unrestricted black-box factoring formulations.
<!-- grochow-82-hypothesis-ledger:end -->

<!-- eight-further-structural-theorems:start -->
- **[Associative algebra degenerations in classical matrix conjugacy](ClassicalAlgebraDegenerations/PROOF.md)** — Shows that hyperbolic doubling preserves and reflects orbit-closure inclusion for unital algebra structures, under general linear, symplectic and determinant-one split quadratic conjugacy.
- **[Linearizing operations on presented nonabelian groups](PolynomialGroupStructureCompiler/PROOF.md)** — Combines group-ring augmentation truncation with an ordered finite-difference expansion to encode operations and every compatible group homomorphism over fixed bounded class and exponent.
- **[Exact epimorphism counting along the Fitting derived series](HallFittingEpimorphisms/PROOF.md)** — Counts through intermediate coinduced bounds and a final unrestricted abelian layer. Covers bounded-generator targets with metabelian Hall Fitting subgroup.
- **[Epimorphic lifts with ordered simple heads](GroupTransferII/PROOF.md)** — Counts marked lifts through nested affine rows, including coprime actions and elementary modular components for cyclic quotients.
- **[Border factor recovery at arbitrary multiplicity](BorderFactorRecovery/PROOF.md)** — Uses modified Newton iteration and local jets for nonuniform rational factor approximation with size independent of input degree and factor multiplicity.
- **[Rational specialization preserving two quantifier blocks](TwoBlockRationalSpecialization/PROOF.md)** — Uses effective Nullstellensatz and rank witnesses to deterministically specialize parameters while preserving algebraic-closure truth of one- and two-block formulas.
- **[Exact epimorphisms for square-zero radical algebras](SquareZeroRadicalEpimorphisms/PROOF.md)** — Counts onto maps in polynomial full-table time when the target semisimple factors interact through a radical graph of bounded treewidth.
- **[Exact surjections onto linear inverse monoids](LinearInverseMonoidSurjections/PROOF.md)** — A uniform polynomial-time algorithm for raw explicit tables via a single cyclic scalar corner, with arbitrary dimension and field size.
<!-- eight-further-structural-theorems:end -->

<!-- grochow-eight-orbit-transfer:start -->
- **[A degeneration-preserving compiler for tensors](TensorDegenerationCompiler/PROOF.md)** — Transfers full orbit-closure inclusion for tensors to associative algebra degeneration and split classical conjugacy. For three-tensors the algebra has linear dimension and cube-zero radical.
- **[Exact isotopy transporters and degenerations of unital algebras](AssociativeIsotopyDegeneration/PROOF.md)** — Identifies all three-factor transporters of multiplication tensors and recovers associative-algebra degeneration from tensor degeneration.
- **[Logspace membership in affine quasigroups](GrochowGroupsI/PROOF.md)** — Recognizes group-affine quasigroups from raw tables and decides generated membership with witness streaming. Gives a case of Collins–Grochow–Levet–Weiß Question 8.2.
- **[Exact epimorphism counts by central matching weights](GrochowGroupsII/PROOF.md)** — Counts maps onto perfect central products of simple factors using a weighted permanent and a subgroup generated by matching-cycle weights. Extends cases of Grochow–Srivastava–Thakkar Questions 2 and 3(5).
- **[Projective incidence from classical graphs](GrochowGraphI/PROOF.md)** — Uniform raw recognition and isomorphism search for Grassmann and alternating symplectic point graphs, including complements. Gives cases of Grochow–Urisman Question 1.9.
- **[Raw recognition of bilinear-forms graphs](GrochowGraphII/PROOF.md)** — Recovers projective coordinates and all matrix entries from adjacency using rank-drop probes. Covers a family of affine rank-three graphs in Grochow–Urisman Question 1.9 and computes its exact automorphism cycle index over prime fields, relevant to Question 1.8.
- **[Compact isomorphism for supports with a small relation space](GrochowCircuitsI/PROOF.md)** — Gives an exact orthogonal or unitary reduction for strictly feasible free-block supports under a short-kernel hypothesis, with individually encoded algebraic coordinates. A case of Question 1.8.
- **[Support criteria for tensor null cones and closed orbits](GrochowCircuitsII/PROOF.md)** — Shows that scalar-block scaling attains the full norm infimum in the limit for balanced free blocks. Linear feasibility detects the null cone and strict feasibility detects minimum attainment and complex closed orbits.
<!-- grochow-eight-orbit-transfer:end -->

<!-- eight-algebraic-transfer-theorems:start -->
- **[Exact classical transporters for associative algebras](ExactClassicalTransporters/PROOF.md)** — Determines the full split symplectic and determinant-one split quadratic transporter functor of the hyperbolic matrix encoding over every commutative scalar extension.
- **[Linearizing bounded finite-difference degree](FiniteDifferenceIsomorphism/PROOF.md)** — Encodes bounded-degree nonlinear operations on finite abelian groups of fixed exponent, with full recovery of additive morphisms. Gives a prime-field tensor-isomorphism reduction in prime-power characteristic.
- **[Exact counting of epimorphic lifts through abelian kernels](AbelianHeadLifts/PROOF.md)** — Handles nonsemisimple kernels whose head endomorphisms lift, with prescribed point values and nonsplit extensions.
- **[Epimorphism counting with unbounded Fitting inner action](FittingInnerAction/PROOF.md)** — Gives exact polynomial-time counting for bounded-generator targets under module socle conditions, covering wreath products of unbounded nilpotence class, commutator rank and inner-action rank.
- **[Low-degree factors from bounded-order local data](CircuitTransferI/PROOF.md)** — Recovers small rational factors nonuniformly from Taylor data whose order depends on the factor degree and multiplicity.
- **[Rational matrix realization of nonlinear tests](CircuitTransferII/PROOF.md)** — A deterministic specialization preserves nonlinear tests, adjoints and generic ranks of designated regular-representation matrices over rational function fields.
- **[Exact surjection counting onto full matrix monoids](FiniteAlgebraTransferI/PROOF.md)** — Gives a uniform polynomial-time algorithm for arbitrary matrix dimension and finite field size, and for products of a bounded number of factors.
- **[Counting homomorphisms by affine lifts over a quotient](FiniteAlgebraTransferII/PROOF.md)** — Gives exact affine lift counting and onto search, with two criteria for exact onto counting. Applies to block algebras of bipermutive cellular automata with the stated targets.
<!-- eight-algebraic-transfer-theorems:end -->

<!-- four-algebraic-transfer-theorems:start -->
- **[Hyperbolic matrix conjugacy for associative algebras](HyperbolicAlgebraConjugacy/PROOF.md)** — Encodes every finite free unital algebra over a commutative ring as an adjoint-stable matrix algebra. Ordinary, split symplectic and split determinant-one quadratic conjugacy give the same decision on the constructed pairs, with identical transporters for the two forms. Includes a tensor-isomorphism transfer.
- **[Counting epimorphisms through nonabelian Fitting subgroups](FittingSubgroupEpimorphisms/PROOF.md)** — Gives exact polynomial-time Cayley-table counting and polynomial-delay enumeration for unrestricted sources and bounded-generator targets satisfying explicit Fitting-subgroup conditions, including nonsemisimple families of unbounded commutator rank. Extends cases of Grochow–Srivastava–Thakkar Questions 2 and 3(2).
- **[Descent of arithmetic witnesses and oracle reductions](CircuitWitnessDescent/PROOF.md)** — Preserves the truth and residual supports of systems of rational substitution-linear tests under deterministic coefficient descent. Shows that bounded-degree rational polynomial-oracle reductions descend to the rationals and are closed under bounded-degree rational factors in the nonuniform model.
- **[Counting homomorphisms to inverse semigroup targets](InverseSemigroupCoarseGraining/PROOF.md)** — Counts exact surjective coarse-grainings when the finite target has an inverse semigroup multiplication term. Also proves a general decomposition by unary term values with semilattice or quasigroup laws on its classes.
<!-- four-algebraic-transfer-theorems:end -->

<!-- four-algebraic-algorithms:start -->
- **[Four algebraic algorithms and reductions](FourAlgebraicAlgorithms/PROOF.md)** — Exact Cayley-table epimorphism counting into bounded-generator metabelian groups, tensor-isomorphism hardness for split symplectic and special orthogonal Lie subalgebra conjugacy with fixed Levi factor, deterministic circuit-IPS descent from finitely generated characteristic-zero fields, and exact block coarse-graining for finite targets with a quasigroup term. Informal proofs with their field, representation and input hypotheses.
<!-- four-algebraic-algorithms:end -->

<!-- coarse-graining-function-field-ips:start -->
- **[Complexity of elementary cellular-automaton coarse-graining](ElementaryCoarseGrainingComplexity/PROOF.md)** — Answers Song–Grochow's fixed-block question for elementary rules. The decision and witness algorithm takes deterministic single-exponential time in numeric block size, and a separate decision algorithm uses quadratic space. Includes exact counting, an exhaustive verification harness for small blocks, and attribution to the earlier Boolean-structure CSP theorem that already implies the time-class inclusion.
- **[Ideal Proof Systems and PIT over function fields](FunctionFieldIdealProofSystems/PROOF.md)** — Answers the positive-characteristic function-field case of Grochow's §7.2 question, with a same-field equivalence for Boolean UNSAT. The Variety Emptiness equivalence holds in both characteristics. The characteristic-zero Boolean case reduces to the rational case.
<!-- coarse-graining-function-field-ips:end -->

<!-- genus-two-epimorphisms:start -->
- **[Genus-two group epimorphism and the limits of the genus promise](GenusTwoGroupEpimorphism/PROOF.md)** — Informal results on Grochow–Srivastava–Thakkar Open Question 3(3). There is a deterministic polynomial-time Cayley-table algorithm for bounded coefficient-field genus and arbitrary class-two targets of the same odd prime exponent. Under the literal centroid-module definition, exact genus two is polynomial-time equivalent to unrestricted class-two epimorphism at odd prime exponent. The broader algorithmic question remains open. Companion notes handle field Heisenberg quotients including characteristic two and power-map extensions, and local-ring quotient algorithms for bounded generator and socle ranks.
<!-- genus-two-epimorphisms:end -->

<!-- grochow-easy-four:start -->
- **[Polynomial-time canonization and P versus NP](CanonicalFormsAndPNP/PROOF.md)** — Informal answer to all clauses of Fortnow–Grochow Open Question 5.10. Relative to every oracle, unrestricted polynomial-time complete invariants admit polynomial-time canonical forms exactly when P = NP. The proof encodes NP witnesses and adjustable padding in a single equivalence relation.
- **[Coarse-graining the sixteen unresolved elementary automata](ElementaryAutomataCoarseGraining/PROOF.md)** — Informal resolution of Song–Grochow’s elementary-to-elementary census. None of the sixteen rules admits a nonconstant binary block factor at any block size greater than one. For the four-rule orbit of 154 the proof also excludes every proper nonconstant factor to a larger finite alphabet.
- **[Tensor-isomorphism completeness with a fixed simple Levi factor](FixedSimpleLeviConjugacy/PROOF.md)** — Informal strengthening of Grochow’s Question VII.1, whose literal complexity classification follows from Grochow–Qiao’s abelian case. Ambient conjugacy remains TI-complete for perfect, centerless matrix Lie algebras with a fixed nonzero simple Levi factor, nontrivial action, and nonzero square-zero radical.
- **[Field reconstruction from Paley graphs and their switches](PaleyFieldRecovery/PROOF.md)** — Informal constructive result for the Paley family in Grochow–Urisman Question 1.9 and its recognition follow-up. A polynomial-time algorithm recovers the finite field and labels from raw signed adjacency, even after an unknown Seidel switch. Ponomarenko’s earlier result already implies polynomial-time ordinary Paley recognition.
<!-- grochow-easy-four:end -->

<!-- grochow-fourth-batch:start -->
- **[Same-field polynomial identity testing from Boolean IPS](SameFieldBooleanIPS/PROOF.md)** — Informal affirmative answer to the finite-field part of Grochow’s Open Question 7.4. Over each finite field, polynomial simulation of Boolean IPS by a Cook–Reckhow system is equivalent to formal PIT over the same field being in NP. The proof also compares Boolean IPS over finite-degree extensions in Question 7.5. The rational same-field implication remains open.
- **[Tensor-isomorphism reductions on all homomorphisms](FunctorialTensorReductions/PROOF.md)** — Informal answers to several branches of Grochow–Qiao Open Question 7.5. Gives polynomial-time functorial replacements for fixed-order tensor reduction to associative algebra isomorphism and several three-tensor reductions, including the group target over every odd finite field in generating-matrix representation. The functors act on singular and rectangular maps and reflect isomorphism.
- **[Central-radical group epimorphism via factor-center branchwidth](FactorCenterEpimorphisms/PROOF.md)** — Informal progress on Grochow–Srivastava–Thakkar Open Question 3(5). Gives deterministic polynomial time when either factor-center arrangement has bounded branchwidth and a mildly quasipolynomial bound on the full promised class. A fixed A₅-quotient family is equivalent to binary subcode equivalence.
- **[Two-pebble identification for coprime Abelian extensions](HellaCoprimeExtensions/PROOF.md)** — Informal progress on Grochow–Levet Question 5.3. Gives identification in one round with two pebbles in the marked version of Hella’s second bijective game for split scalar actions and for all elementary Abelian 3-complements, with arbitrary coprime Abelian kernels in the latter case.
<!-- grochow-fourth-batch:end -->

<!-- grochow-new-four:start -->
- **[Sparse determinant equivalence and black-box PIT completeness](SparseDeterminantEquivalence/PROOF.md)** — Informal answer to both clauses of Grochow’s arXiv Open Question 6.3. A sparse input gives a deterministic polynomial-time decision algorithm over ℂ. In the polynomial-degree black-box model, determinant equivalence is PIT-hard and reduces back to PIT without a root-finding oracle. The CCC version also asks about root-finding hardness.
- **[Exponential Laurent degree for stable degenerations of sparse forms](KempfDegenerationDegree/PROOF.md)** — Informal affirmative answer to Grochow–Mulmuley–Qiao Question 4.5 (ICALP Question 19). Every Laurent coordinate path to the closed orbit of the displayed family has exponentially large degree, including the canonical Kempf one-parameter subgroup.
- **[Exact linear-size reduction to surface homology localization](SurfaceHomologyLocalization/PROOF.md)** — Informal exact reduction over every finite abelian coefficient group. A triangulated surface with linearly many simplices has optimum exactly three times the minimum number of violated translation constraints. The hardness questions of Grochow–Tucker-Foltz were already answered by Borradaile, Maxwell, and Nayyeri in 2020.
- **[Canonical forms and complete invariants for length-preserving equivalences](LengthPreservingEquivalenceOracle/PROOF.md)** — Informal progress on Fortnow–Grochow Question 5.11. For length-preserving relations, a single oracle gives CF ⊊ Ker = PEq, with a two-element-class witness that also resists randomized canonization. The unrestricted oracle question remains open.
<!-- grochow-new-four:end -->

<!-- grochow-next-four:start -->
- **[VNP-completeness of canonical Ideal Proof System certificates](CanonicalIPSCertificates/PROOF.md)** — Informal answer to the VNP-completeness clause of Grochow–Pitassi Open Question 7.8. Explicit canonical certificates are VNP-p-complete over fields with more than two elements. Over F₂, canonical certificates cannot be VNP-hard under p-projections. The proof also refutes realization of every p-degree.
- **[Least, minimal and descending circuit degrees of ideals](IdealCircuitDegrees/PROOF.md)** — Informal negative answer to Grochow Open Question 6.4 over ℝ and ℂ. Two-generated prime ideals need not have a least circuit degree. A fixed principal ideal admits an infinite strictly descending chain, answering the corresponding clause of Question 6.6. The note also gives incomparable minimal degrees under the stated p-bounded, eventually nonzero convention.
- **[Boolean monotone projections and perfect matching with repeated labels](BooleanMatchingProjections/PROOF.md)** — Informal progress on Grochow Open Question 5.1. Gives an exponential dimension lower bound when each target perfect matching can be witnessed by a source matching with a bounded number of distinct repeated labels.
- **[Exact group epimorphism counting by central lifts and commutator maps](GroupEpimorphismCounting/PROOF.md)** — Informal progress on Open Question 2 of the group-isomorphism counting paper. Gives deterministic polynomial-time exact counting with a prescribed central quotient map, for a target with bounded central quotient, and for odd prime-exponent class-two targets of bounded derived rank.
<!-- grochow-next-four:end -->

<!-- grochow-followup-four:start -->
- **[Counting Weisfeiler–Leman lower bounds for colored abelian groups](ColoredAbelianWL/PROOF.md)** — Informal negative answer to Grochow–Levet Question 8.3. For two-colored elementary abelian 2-groups, counting WL can require dimension at least log log of the group order minus a constant, even with the full colored generated subgroup as the initial tuple invariant.
- **[Saturated circuit degrees in ideal cosets](IdealCosetSaturation/PROOF.md)** — Informal negative answer to Grochow’s Open Question 6.10 for fixed ambient rings. A proper nonzero principal-ideal coset has no saturated degree, even with arbitrary-degree representatives. The proof also gives an exact width criterion for p-bounded families in the family-oracle model, and a linearly growing counterexample in the single-index convention.
- **[Graph isomorphism for three-orbit symmetry-characterized graphs](ThreeOrbitGraphIsomorphism/PROOF.md)** — Informal progress on Grochow–Urisman Open Question 1.9. Gives polynomial recognition and isomorphism to arbitrary raw adjacency inputs for the three-unordered-pair-orbit branch. Also gives raw-coordinate recovery for affine ovoid graphs and polynomial isomorphism with both inputs promised affine rank-three.
- **[Whole cut-polytope projections and traveling salesman](WholeCutTravelingSalesman/PROOF.md)** — Informal progress on Grochow Open Question 5.4. Gives a general whole-polytope construction, an extension bound for bounded-treewidth quadratic maps, and a linear degree lower bound for polynomial maps fixing all tour incidence vectors. The unrestricted polynomial-size whole-cut question remains open.
<!-- grochow-followup-four:end -->

<!-- boolean-counting-permanent:start -->
- **[Monotone permanent projection lower bounds for Boolean counting](BooleanCountingPermanent/PROOF.md)** — Informal proof answering both clauses of Grochow’s Open Question 5.2. Any monotone affine projection of the permanent agreeing on Boolean inputs with general perfect-matching counts or directed Hamiltonian-cycle counts requires exponential dimension.
- **[Four graph-to-tensor routes in ordinary Polynomial Calculus](FourRoutePolynomialCalculus/FOUR-ROUTES.md)** — Informal results on Galesi–Grochow–Pitassi–She Open Question 7.5. Gives all six pairwise comparisons in characteristic zero for the incidence-code, semisimple Lie, alternating-space, and Grigoriev graph-algebra constructions, including the reverse comparison through the FGS markers.
- **[Epimorphisms of abelian Sylow towers with bounded action ranks](SylowTowerActionRanks/PROOF.md)** — Informal progress on Grochow–Srivastava–Thakkar Open Question 3(4). Gives a polynomial-time algorithm under bounded joint action ranks and relates a two-prime family exactly to binary permutation subcode containment.
- **[Logspace membership through nuclear quotients](NuclearTowerMembership/PROOF.md)** — Informal progress on Collins–Grochow–Levet–Weiß Question 8.2. Gives deterministic logspace membership for a bounded tower of normal nuclear quotients over the covered loop classes and proves a companion finite Lie ring membership theorem.
<!-- boolean-counting-permanent:end -->

<!-- permutation-roots-sparse-graph-probes:start -->
- **Permutation roots, sparse graph probes, and quasigroup algorithms** ([informal proofs](IsomorphismBridgeFrontier/RESULTS.md)). Proves NP-completeness of permutation-group homomorphism extension, answering Kantor–Luks §13 Problem 2 and Wuu Open Problems 1.6 and 1.8, and gives the sharp orbit-size threshold for every fixed root exponent. Proves coRE-completeness for planar bipartite subcubic homomorphism probes of any fixed girth. Gives exact central-quasigroup isomorphism counts in logspace and polynomial-time joint and constrained Latin-operation decompositions.
<!-- permutation-roots-sparse-graph-probes:end -->

<!-- topology-and-invariant-crossovers:start -->
- **Topology, invariant degree, and group-generation crossovers** ([informal proofs](TopologyAndInvariantCrossovers/RESULTS.md)). Proves rational TI-completeness of rational homotopy equivalence from invariant tables even with fixed integral cup products and trivial ordinary Massey products. Gives exact exponential separation degrees for local unitary and orthogonal tensor invariants, linear refutation-degree bounds for spectrally simple real orthogonal tensors, and polynomial-time minimum semigroup generation under additional primitive wreath chief-layer hypotheses.
<!-- topology-and-invariant-crossovers:end -->

<!-- tensor-isomorphism-and-algebraic-crossovers:start -->
- **Four crossovers in tensor isomorphism and algebraic algorithms** ([informal proofs](TensorIsomorphismAndAlgebraicCrossovers/RESULTS.md)). Realizes affine group scheme torsors over every field as ordinary three-tensor transporters up to smooth split factors. Narrows Collins–Grochow–Levet–Weiß Question 8.3 to one-free-element generation and extends the polynomial-time cases. Proves binary tensor-isomorphism completeness of ANF cubic bent equivalence and gives a deterministic width-capped exact-root algorithm for same-order ROABPs.
<!-- tensor-isomorphism-and-algebraic-crossovers:end -->

<!-- further-portfolio-isomorphism-crossovers:start -->
- **Four isomorphism crossovers** ([informal proofs](FurtherPortfolioIsomorphismCrossovers/RESULTS.md)). Deterministic quasipolynomial-time minimum semigroup generation on arbitrary Cayley tables, and polynomial time with bounded nonabelian chief factors in the maximal subgroups (progress on Collins–Grochow–Levet–Weiß Question 8.3). Also proves an exact local-unitary overlap formula and a fidelity-threshold hardness result for repeated code states, arithmetic universality in one rank-two alternating congruence orbit, and exponential sparse Polynomial Calculus lower bounds for four-tensors with every pair flattening invertible.
<!-- further-portfolio-isomorphism-crossovers:end -->

<!-- portfolio-isomorphism-crossovers:start -->
- **[Four theorems on isomorphism, specialization, and proof complexity](PortfolioIsomorphismCrossovers/RESULTS.md)** — Informal proofs of a Hilbert's-tenth equivalence for smooth rational Fano specialization on canonical inputs, a per-instance Polynomial Calculus degree classification for geometric matrix nonisomorphism, sharp-exponent symmetric quartic compression when the input order is divisible by four, and exact polynomial-time epimorphism counting for elementary abelian Sylow towers with a further first-layer extension.
<!-- portfolio-isomorphism-crossovers:end -->

<!-- open-problem-archive-additions:start -->
- **[Proofs recovered from the Open Problem Archive](OpenProblemArchiveAdditions/RESULTS.md)** — Informal solution of TheoremDB P2750 with reproducible full orbit enumeration, symplectic tensor isomorphism for five actions and fixed arity, special-linear isomorphism of fixed-width finite-field pencils in deterministic polynomial time, tensor isomorphism hardness in concise critical formats, and exact classical and entanglement-assisted zero-error capacity for finite-ring rank-threshold channels.
<!-- open-problem-archive-additions:end -->

<!-- recovered-research-proofs:start -->
- **[Recovered proofs from the research archive](RecoveredResearchProofs/RESULTS.md)** — Informal proofs resolving Kaspers–Pott’s design-isomorphism conjecture and refuting four of Fang’s collapse-pattern conjectures. Includes new equal-intersection design examples, the prime-square perfect-sequence classification, an exact six-job scheduling lower bound, and a base-two approximation for Euclidean TSP with unit-ball neighborhoods.
<!-- recovered-research-proofs:end -->

<!-- grochow-group-frontier:start -->
- **[Fitting-free epimorphisms, fixed nilpotent targets, and code-to-lattice equivalence](GrochowGroupFrontier/RESULTS.md)** — Informal proofs answering Grochow–Srivastava–Thakkar Open Question 3(1) for Cayley tables, extending Elder–Shen–Weiß Open Question 4.1 to a dichotomy for all fixed finite nilpotent targets in the finite-presentation and permutation-generator models, and reducing monomial code equivalence over every fixed extension field to lattice isomorphism. Also constructs minimum faithful actions for all class-two Cayley-table groups in polynomial time.
<!-- grochow-group-frontier:end -->

<!-- minimum-degree-crossovers:start -->
- **[Small permutation orbits, faithful degree, and dihedral quotients](MinimumDegreeCrossovers/RESULTS.md)** — Informal proof of NP-completeness for epimorphism from finite presentations onto D₈, answering Elder–Shen–Weiß Open Question 4.1. Companion results give the sharp factor-p approximation threshold at orbit cap p³, exponential inapproximability for central Heisenberg-power quotients, and NP-completeness of minimum faithful degree with just one p³-point orbit.
<!-- minimum-degree-crossovers:end -->

<!-- group-tensor-frontier:start -->
- **[Minimum permutation degree and tensor-isomorphism reductions](GroupTensorFrontier/RESULTS.md)** — Informal proof that Kantor–Luks §13, Problem 1 (Size of Representation Domain) is NP-complete, already for class-two odd-\(p\) groups given by bounded-orbit permutation generators with trivial quotient kernel. The group bridge proves TI-completeness on minimum-degree exponent-prime permutation presentations. Companion results give a linear-side determinant-profile kernel over fixed finite fields, exponential extension degrees for finite-field TI, and a deterministic signed local-algebra algorithm with unbounded residue degree.
<!-- group-tensor-frontier:end -->

<!-- cube-zero-determinant-absorption:start -->
- **[Absorbing odd automorphisms into one-sign tensor isomorphism](CubeZeroDeterminantAbsorption/RESULTS.md)** — Informal polynomial-time many-one reductions over F₃. An unrestricted one-sign comparison with an independent odd-automorphism test reduces to the asymmetric correction comparison. One-sign absorption holds when either conjunct belongs to the stated cube-zero multiplication families. The unrestricted reverse reduction remains open.
<!-- cube-zero-determinant-absorption:end -->

<!-- determinant-reverse-families:start -->
- **Determinant comparisons for orbit, component, and algebra families.** Single-instance reductions remove Cayley-table parity on colors with logarithmically many intrinsic 3-group orbits and graph parity with logarithmic marked classes inside components. Further reductions handle subspace arrangements generated by small intersections and odd automorphisms of square-zero-radical multiplication tensors. Informal proofs. [Results](DeterminantReverseFamilies/RESULTS.md)
<!-- determinant-reverse-families:end -->

<!-- graph-group-determinant-ti:start -->
- **Graph and group counterparts of the determinant TI chain.** Ordinary three-tensor isomorphism over F₃ is many-one equivalent to abstract isomorphism of class-two groups of exponent dividing nine given by permutation generators. The hardness construction uses orbits of size at most 81 and retains all three determinant signs on characteristic group sections. Further reductions compare marked graph, ternary-code, and Cayley-table isomorphism with the chain. Informal proofs. [Results](GraphGroupDeterminantTI/RESULTS.md)
<!-- graph-group-determinant-ti:end -->

<!-- marked-permutation-reverse:start -->
- **Marked permutation isomorphism equivalences.** Over F₃, marked monomial-label tensor isomorphism and marked subspace-arrangement isomorphism have the same many-one degree. Marked graphic-matroid isomorphism is many-one equivalent to marked graph isomorphism, including arbitrary graph 1- and 2-separations. The unsigned corollary answers the many-one question posed by Rao and Sarma. Informal proofs. [Results](MarkedPermutationReductions/RESULTS.md)
<!-- marked-permutation-reverse:end -->

<!-- tensor-determinant-intervals:start -->
- **Intermediate determinant comparisons for tensor isomorphism.** Over F₃, explicit many-one reductions refine the ordinary, one-sign, two-sign and special-linear chain. Includes 44 source-automorphism correction predicates and a seven-node upper chain whose reverse steps fail in the affine compiler model. Informal proofs. [Catalogue and reductions](TensorDeterminantIntervals/RESULTS.md)
<!-- tensor-determinant-intervals:end -->

<!-- tensor-determinant-families:start -->
- **Determinant restrictions for cyclic tensors and matrix multiplication factors.** Over F₃ the three signed problems on cyclically presented three-tensors have exactly the degree of unrestricted one-sign TI. Two even matrix multiplication factors give ordinary TI degree. SL-TI on symmetric or alternating matrix pencils has unrestricted two-sign degree under independent matrix maps. Additional reductions cover two algebraic families. Informal proofs. [Results and proofs](TensorDeterminantFamilies/RESULTS.md)
<!-- tensor-determinant-families:end -->

<!-- four-isomorphism-results:start -->
- **Four results on group, tensor, and matrix isomorphism** — [Informal proofs](FourIsomorphismResults/RESULTS.md). A succinct class-two group and prime-power tensor equivalence, NP-hardness of least extension degree for rational TI, a characteristic-two matrix-tuple isometry algorithm for specified residue factors, and a witness-preserving tensor kernel that removes repeated slice modules.
<!-- four-isomorphism-results:end -->

<!-- filtered-frobenius-orientation:start -->
- **Determinant cancellation in filtered Frobenius algebras** — [Informal proof](FilteredFrobeniusOrientation/FrobeniusOrientation.md). Gives deterministic polynomial-time reductions from first-mode determinant-one multiplication-tensor isomorphism to one ordinary TI instance for odd-dimensional algebras, symmetric Hilbert functions of odd socle degree, and compressed even-socle algebras satisfying an explicit parity condition. Works from raw tensor coordinates without a supplied grading or transporter. Includes exact finite controls and a [search/scope audit](FilteredFrobeniusOrientation/SearchAudit.md). **Does not close unrestricted TI versus SL-TI or claim publication priority; not Lean-formalized.**
<!-- filtered-frobenius-orientation:end -->

<!-- tensor-sign-packing:start -->
- [Packing Independent Determinant Tests in Tensor Isomorphism](TensorSignPacking/RESULTS.md) (informal proofs) — A single ordinary TI instance enforces binary linear equations whose variables are enabled by ordinary TI comparisons. This assembles determinants across arbitrary numbers of centroid blocks with local sign tests and gives one-instance packing of two independent signed comparisons on several identifiable families over $\mathbb F_3$. Unrestricted signed conjunction remains open.
<!-- tensor-sign-packing:end -->

<!-- tensor-determinant-conjunction:start -->
- [Ordinary Conjunctions in Determinant Tensor Isomorphism](TensorDeterminantConjunction/RESULTS.md) (informal proofs) — Over $\mathbb F_3$, all 30 catalogue comparisons retain their polynomial-time many-one degree after adjoining a list of ordinary tensor-isomorphism tests. Also gives a one-instance ordinary TI reduction for complete-intersection Frobenius inputs and a two-test upper bound for the cross-mode sign-correction problem.
<!-- tensor-determinant-conjunction:end -->

<!-- tensor-determinant-interval-collapses:start -->
- [Further Collapses in the Determinant Tensor Isomorphism Intervals](TensorDeterminantIntervalCollapses/RESULTS.md) — Informal many-one equivalences for the commutative multiplication and Frobenius candidates, with additional signed conjunction and upper interval reductions over F3. The unrestricted endpoint collapse remains open.
<!-- tensor-determinant-interval-collapses:end -->

<!-- tensor-determinant-interval-thirty:start -->
- [Thirty Candidate Degrees in the Determinant Tensor Isomorphism Intervals](TensorDeterminantIntervalThirty/RESULTS.md) — Informal deterministic many-one bounds for thirty new definitions over F3, ten in each closed interval. Includes determinant-plane balance and exact affine-probe counts. No strict Karp separation is claimed.
<!-- tensor-determinant-interval-thirty:end -->

<!-- tensor-determinant-lower-bounds:start -->
- [Lower Bounds for Removing Determinant Constraints in Tensor Isomorphism](TensorDeterminantLowerBounds/RESULTS.md) — Informal finite-field lower bounds for fixed tensor markers and low-degree equivariant encoders, plus optimal affine sign-query counts over F3. All three unrestricted many-one separations remain open.
<!-- tensor-determinant-lower-bounds:end -->

<!-- tensor-sign-projections:start -->
- [Determinant Sign Projections and Conjunctions in Tensor Isomorphism](TensorSignProjections/RESULTS.md) — Informal polynomial-time sign projections over F3, a single SL-TI instance for independent two-sign and one-sign comparisons, and three restricted reverse reductions. The unrestricted reverse reductions remain open.
<!-- tensor-sign-projections:end -->

<!-- tensor-sign-reduction-audit:start -->
- **[Two-sign to one-sign reduction audit](TensorSignReductionAudit/RESULTS.md)** — Informal research audit of pair-dependent multiplication networks, determinant representations, and finite orientation constructions over F_3. Documents unsuccessful routes and prior constructions recovered from the DAG; the unrestricted polynomial-time many-one reduction remains open. No new open-problem closure is claimed.
<!-- tensor-sign-reduction-audit:end -->

<!-- tensor-sign-conjunctions:start -->
- [Single-Instance Conjunctions for Determinant Signs](TensorSignConjunctions/RESULTS.md) — Informal one-instance reductions with logarithmic tested dimension or certified sign flexibility, an exact compiler for one signed and arbitrarily many ordinary TI conjuncts, and a common-encoding criterion for collapse to ordinary TI. The unrestricted two-sign to one-sign reduction remains open.
<!-- tensor-sign-conjunctions:end -->

<!-- tensor-isomorphism-collapses:start -->
- [Which TI Interval Problems Collapse?](TensorIsomorphismCollapses/RESULTS.md) — Informal many-one equivalences grouping 21 of the 22 TI interval entries into four ordered groups over F3, with the quadratic norm class between the endpoints. Includes an exact cubic norm transfer and the common Turing closure of twenty entries.
<!-- tensor-isomorphism-collapses:end -->

<!-- tensor-isomorphism-interval:start -->
- [Twenty Candidate Classes Between TI and SL-TI](TensorIsomorphismInterval/RESULTS.md) — Informal deterministic many-one interval proofs over \(\mathbb F_3\) for six determinant-subgroup problems, eight concise structural restrictions and six extension-field norm problems. Includes all sign-subgroup reductions and a three-character route to the endpoint comparison. Strictness is open.
<!-- tensor-isomorphism-interval:end -->

<!-- optimal-max-rank-and-descent:start -->
- [Optimal Max-Rank Hardness and Extension Spectra for Tensor Isomorphism](OptimalMaxRankAndDescent/RESULTS.md) — Informal proofs of TI-completeness for recognizable, balanced, absolutely indecomposable tensors at optimal all-mode maximum matrix rank, and of a complete classification of extension-degree spectra with a nilpotent descent theorem.
<!-- optimal-max-rank-and-descent:end -->

<!-- isomorphism-extension-and-rank:start -->
- [Four Results on Tensor, Graph, and Algebra Isomorphism](IsomorphismExtensionAndRank/RESULTS.md) — Informal proofs of minimum-extension-degree NP-completeness on a raw recognizable tensor family, TI-completeness for low-slice-rank scalar-adjoint tensors, local-generator canonization, and graph reconstruction from absolutely irreducible determinant forms.
<!-- isomorphism-extension-and-rank:end -->

<!-- special-linear-tensor-frontier:start -->
- [Four Further Approaches to Special-Linear Tensor Isomorphism](SpecialLinearTensorFrontier/RESULTS.md) — Informal progress on Chen–Grochow–Qiao–Tang–Zhang Open Question 1.9, covering raw scalar-stabilizer pairs with split determinant pencils, coupled four-layer words in matrix algebras, exact projective products by point counting, and determinant pins on singular Frobenius-form pencils.
<!-- special-linear-tensor-frontier:end -->

<!-- determinant-tensor-routes:start -->
- [Four Routes to Determinant-Constrained Tensor Isomorphism](DeterminantTensorRoutes/RESULTS.md) — Informal progress on Chen–Grochow–Qiao–Tang–Zhang Open Question 1.9, including overlapping contraction flags, full determinant cosets at logarithmic smallest-mode rank, Pfaffian pins in fixed characteristic, and determinant tests for associative action tensors.
<!-- determinant-tensor-routes:end -->

<!-- isomorphism-invariant-zoo:start -->
- [Isomorphism Invariant Zoo](IsomorphismInvariantZoo/RESULTS.md) — Twenty informal constructions for tensor, group, code, gain-graph and cubic-form equivalence, extending the early Rune, Ley, Sigil, Ward and Trellis ideas. Includes exact determinant corrections within congruence classes, canonical tensor flags, a code-to-GI reduction parameterized by the number of bases, and NP-completeness of epimorphism for a compact metabelian permutation-group family.
<!-- isomorphism-invariant-zoo:end -->

<!-- further-invariant-transfers:start -->
- [Four Invariant Transfers in Isomorphism](FurtherInvariantTransfers/RESULTS.md) — Informal proofs giving a negative answer to Agrawal–Saxena’s real-and-congruence cubic equivalence question, uniform NC algorithms for subgroup descent in arbitrary permutation-group quotients, an exact shared-phase switching algorithm for bounded-degree gain graphs, and a determinant-constrained monomial tensor reduction over finite chain rings.
<!-- further-invariant-transfers:end -->

<!-- invariant-transfers-to-isomorphism:start -->
- **[Smooth Cubics, Parallel Group Cores, and Exact Phase Transport](InvariantTransfersToIsomorphism/RESULTS.md)** — Four informal results on GI-hardness of smooth cubic hypersurface isomorphism, deterministic uniform NC for subgroup cores of permutation-group quotients, determinant-one monomial tensor transport over varying finite fields, and exact Butson and cyclic gain equivalence.
<!-- invariant-transfers-to-isomorphism:end -->

<!-- early-invariant-isomorphism:start -->
- **[Exact Isomorphism Reductions from Early Invariants](EarlyInvariantIsomorphism/RESULTS.md)** — Informal proofs of GI-completeness for collinearity isomorphism on a fixed smooth cubic, and a factorization-free reduction from cyclic phase equivalence with binary moduli to graph isomorphism. The phase construction also applies to full-support tensors under monomial actions in every mode.
<!-- early-invariant-isomorphism:end -->

<!-- isomorphism-frontiers:start -->
- [**Parallel Lower Central Series and Average-Case Matrix-Code Conjugacy**](IsomorphismFrontiers/RESULTS.md) — Informal proofs answering Babai–Luks–Seress §10 Problem 3 and Li–Li–Qiao–Tao–Wang Problem 1.6 (version 2). Includes succinct tensor encodings of field-extension power equations and a finite-unitary orbit classification.
<!-- isomorphism-frontiers:end -->

<!-- quotient-groups-and-canonical-tensors:start -->
- **[Quotient Groups, Code Equivalence, and Canonical Tensor Trains](QuotientGroupsAndCanonicalTensors/RESULTS.md)** — Informal proofs answering Levet–Srivastava–Thakkar's normal-centralizer and unrestricted quotient-socle questions, Schrock's sloped genus-two quotient question, and both of Vilmart's canonical LDPU complexity questions. Also gives deterministic hidden extension-linear matrix-code equivalence over finite and number fields and a counterexample and repair for Couvreur–Debris-Alazard–Gaborit Proposition 32. Publication priority remains unverified.
<!-- quotient-groups-and-canonical-tensors:end -->

<!-- parallel-group-algorithms-and-isomorphism:start -->
- **[Parallel Group Algorithms and Isomorphism Proofs](ParallelGroupAlgorithmsAndIsomorphism/RESULTS.md)** — Informal proofs answering Levet–Srivastava–Thakkar Problems 12.1, 12.4 and 12.5 and Levet's Shonan permutation-socle question, together with Schrock's flat-pencil conjectures and Horlemann et al.'s linear monomial-model question. Also records Qiao's fixed-format tensor-isomorphism bound as a consequence of Kayal's theorem, and a sampler for Narayanan's finite-field definition of nondegeneracy. Publication priority remains unverified.
<!-- parallel-group-algorithms-and-isomorphism:end -->

<!-- four-code-and-group-iso-results:start -->
- **[Four Results on Code and Group Isomorphism](FourCodeAndGroupIsoResults/RESULTS.md)** — Informal answers to the nonprime-field code-to-lattice reduction and monomial companion questions in Horlemann et al., the sharp random-code rigidity transition left by Li–Wang–Zhou, and Schrock's flat genus-two conjectures 4.4.4.1 and 4.4.4.3. The lattice reduction is polynomial in block length and field order. Publication priority is pending.
<!-- four-code-and-group-iso-results:end -->

<!-- four-algebraic-isomorphism-transfers:start -->
- **[Four Transfers in Finite-Dimensional Algebra and Isomorphism](FourAlgebraicIsomorphismTransfers/RESULTS.md)** — Informal proofs of polynomial-time characteristic-two tuple isometry with commutative adjoint residue, a group epimorphism and subcode-equivalence bridge with improved Cayley-table bounds for Question 3(5), TI-completeness of a stable-equivalence family, and an exact positive-characteristic closed-orbit encoding of finite-field TI.
<!-- four-algebraic-isomorphism-transfers:end -->

<!-- ternary-determinant-parity:start -->
- **[Determinant-Sign Tests for Ternary Tensor Transporters](TernaryDeterminantParity/RESULTS.md)** — Informal progress on Chen–Grochow–Qiao–Tang–Zhang Open Question 1.9. Gives one ordinary ternary TI instance for specified nonsplit determinant frames and their split local-ring lifts, and one ordinary binary TI instance for ternary tensors with logarithmic-dimensional permutable blocks. The unrestricted same-field question remains open.
<!-- ternary-determinant-parity:end -->

<!-- local-determinant-transfers:start -->
- **[Determinant Constraints in Local-Ring Tensor Isomorphism](LocalDeterminantTransfers/RESULTS.md)** — Gives a polynomial-time reduction from special-linear tensor isomorphism over split binary square-zero algebras and a multigraded binary family to ordinary binary TI. Over other coefficient fields the derivation construction enforces a principal-unit determinant constraint. Also audits the Qiao–Zhang interfaces and gives a direct determinant-constrained local lifting proof with conditional residue-field exponential time. The unrestricted finite-field question remains open. Informal proofs.
<!-- local-determinant-transfers:end -->

<!-- november-group-iso-transfers:start -->
- **[Four Transfers from Polynomial-Time Group Isomorphism](NovemberGroupIsoTransfers/RESULTS.md)** — Uses the Qiao–Zhang manuscript and its finite-rings follow-up to obtain complete three-tensor isomorphism cosets with a residue-field exponential bound independent of nilpotent length, singly exponential sum-rank code equivalence, polynomial table-time nonassociative ring isomorphism, and marked group epimorphism search and counting with bounded-rank radical layers. The epimorphism result addresses parts of Grochow–Srivastava–Thakkar Open Question 3. Informal proofs, with dependencies stated.
<!-- november-group-iso-transfers:end -->

<!-- four-ti-almost-all:start -->
- **[Almost-All Ordinary Four-Tensor Isomorphism](FourTIAlmostAll/RESULTS.md)** — Strengthens Li–Li–Qiao–Tao–Wang Problem 1.7 to $1-o(1)$ coverage over every fixed finite field. A deterministic polynomial-bit-time algorithm recognizes a uniformly random first tensor with high probability, decides against every second tensor, and recovers transporters. The proof uses inverse flattenings, crossed contractions and a fixed-field Fourier estimate. Includes inverse-polynomial failure bounds of any fixed order and lifting to Galois rings. Informal proof.
<!-- four-ti-almost-all:end -->

<!-- effective-local-quiver-comparisons:start -->
- [Four effective local-quiver comparisons](LocalQuiverIsomorphism/RESULTS.md) — Informal proofs of GI-complete raw tensor deformation classes, exact all-orders normalization for fixed-arrow quiver lifts and deterministic transporter counts, linear-size TI equivalence for genuinely obstructed algebra lifts, and polynomial moving-slice transporter search and determinant counts over truncated local rings under a geometric frame promise.
<!-- effective-local-quiver-comparisons:end -->

<!-- intrinsic-isomorphism-crossovers:start -->
- [Intrinsic structures in tensor and algebra isomorphism](IntrinsicIsomorphismCrossovers/RESULTS.md) — Informal proofs of a linear-dimension tensor reduction to global-dimension-two derived equivalence, graph-isomorphism hardness with identical Hochschild cup algebras, deterministic recovery from the Hochschild Lie bracket and a recognizable graph-isomorphism-complete tensor family, linear-length fixed-residue tensor reductions, and degree-preserving proof translations among the five tensor actions.
<!-- intrinsic-isomorphism-crossovers:end -->

<!-- isomorphism-cohomology-crossovers:start -->
- [Tensor, group and algebra isomorphism crossovers](IsomorphismCohomologyCrossovers/RESULTS.md) — Informal proofs of tensor-isomorphism hardness of derived equivalence at global dimension two, linear-length reductions among the five free-module tensor actions over commutative rings, constant-degree comparisons for two graph-to-tensor routes and characteristic-two matrix-congruence degree bounds (Galesi–Grochow–Pitassi–She Open Questions 7.5 and 7.3), and polynomial exact epimorphism counting for homocyclic Sylow complements (restricted Grochow–Srivastava–Thakkar Open Questions 2 and 3(4)).
<!-- isomorphism-cohomology-crossovers:end -->

<!-- group-tensor-crossovers:start -->
[Four crossovers in group and tensor isomorphism](GroupTensorCrossovers/RESULTS.md) — AI-assisted informal proofs of FOLL chief and composition series for arbitrary Cayley-table groups, an NC solution to Levet’s Question 8.2 under the stated index promise, tensor-isomorphism hardness of derived equivalence in global dimension at most three, and Las Vegas polynomial-time characteristic-two matrix tuple isometry for square-zero adjoint radical.
<!-- group-tensor-crossovers:end -->

<!-- logspace-minimum-generation-recurrent-cayley:start -->
[Logspace greedy generator replay on Cayley tables in Lean](LogspaceMinimumGenerationRecurrentCayley/README.md) — Verified components for Collins–Grochow–Levet–Weiß Question 8.1. A finite machine finds the first greedy generator from a raw Cayley table in logarithmic workspace, and a finite replay machine recovers any requested greedy entry from a stored ordinal and initialized workspace. The two use the same native connectivity machine and workspace constant. The unrestricted minimum-generator search theorem remains informal.
<!-- logspace-minimum-generation-recurrent-cayley:end -->

<!-- logspace-minimum-generation-cayley-replay:start -->
[Physical Cayley query and generator replay in Lean](LogspaceMinimumGenerationCayleyReplay/README.md) — Verified components for Collins–Grochow–Levet–Weiß Question 8.1, including physical endpoint decoding, ordinal generator replay, and a silent verdict adapter for nested queries. The complete connectivity and unrestricted search machines remain to be formalized.
<!-- logspace-minimum-generation-cayley-replay:end -->

<!-- logspace-minimum-generation-physical-callbacks:start -->
[Physical Cayley and Berkowitz callbacks in Lean](LogspaceMinimumGenerationPhysicalCallbacks/README.md) — Verified components for Collins–Grochow–Levet–Weiß Question 8.1, including a finite-machine compiler, raw Cayley trial setup, a weighted Gram controller, and streamed arithmetic with exact suspension bounds. The unrestricted search theorem remains informal.
<!-- logspace-minimum-generation-physical-callbacks:end -->

<!-- logspace-minimum-generation-lean-steps-1-to-4:start -->
[Cayley-table input and quotient access in Lean](LogspaceMinimumGenerationLeanSteps1To4/README.md) — Verified components for Question 8.1 covering raw table decoding, connectivity-to-word search, subgroup and chief queries, and the residual replay interface. The unrestricted search theorem remains informal.
<!-- logspace-minimum-generation-lean-steps-1-to-4:end -->

<!-- logspace-minimum-generation-lean:start -->
[Lean components for logspace minimum generation](LogspaceMinimumGenerationLean/README.md) — Verified Cayley-table, Frattini and Gaschütz lifting, quotient replay, and semisimple generation lemmas for Collins–Grochow–Levet–Weiß Question 8.1. The complete search proof is informal. The existence of the unrestricted logspace machine remains to be formalized.
<!-- logspace-minimum-generation-lean:end -->

<!-- logspace-minimum-generation:start -->
[Minimum generating sets in deterministic logspace](LogspaceMinimumGeneration/Proof.md) — Informal proof answering Collins–Grochow–Levet–Weiß Question 8.1. Given the Cayley table of an arbitrary finite group, the algorithm outputs an actual minimum generating set in logarithmic workspace. It queries the alternating solvable-radical and semisimple-socle quotients directly from the input and uses separate lifting algorithms for the two kinds of layers. Includes the [generator-number proof and supporting results](LogspaceMinimumGeneration/README.md). Publication priority is unestablished.
<!-- logspace-minimum-generation:end -->

<!-- generation-and-algebraic-equivalence:start -->
[Exact Generation, Principal Minors, and Algebraic Equivalence](GenerationAndAlgebraicEquivalence/README.md) — Informal proofs.

- [Exact magma generation](GenerationAndAlgebraicEquivalence/ExactMagmaGeneration.md) is DP-complete. Answers Collins–Grochow–Levet–Weiß, §7.3.
- [Regular transformation semigroup rank](GenerationAndAlgebraicEquivalence/RegularTransformationSemigroups.md) satisfies the Stirling-number bound of Gray's Open Problem 2.
- [Characteristic-two symmetrization](GenerationAndAlgebraicEquivalence/CharacteristicTwoSymmetrization.md) has a constructive deterministic polynomial-time algorithm. This covers the symmetrization task of Ivanyos–Qiao's first open problem.
- [Extension-field code equivalence to lattices](GenerationAndAlgebraicEquivalence/CodeEquivalenceToLattice.md) gives bit-polynomial reductions for the permutation and signed-permutation variants.
- [Principal-minor oracle reconstruction](GenerationAndAlgebraicEquivalence/PrincipalMinorOracle.md) requires exponentially many individual-minor queries, answering the oracle question of Aravind et al.
<!-- generation-and-algebraic-equivalence:end -->

<!-- four-tensor-and-group-isomorphism-results:start -->
[Four Tensor and Group Isomorphism Results](FourTensorAndGroupIsomorphismResults/README.md) — Four informal proofs.

- [Class-two groups with bounded derived exponent](FourTensorAndGroupIsomorphismResults/group.md). Gives $N^{\widetilde O(\sqrt{\log_p N})}$ isomorphism time for odd $p$ with bounded commutator exponent and for $2$-groups with elementary abelian derived subgroup. The groups themselves may have unbounded exponent.
- [Determinant-resolved tensor isomorphism](FourTensorAndGroupIsomorphismResults/sl.md). Searches and counts transporters by determinant triple over fixed finite commutative rings with a subquadratic exponent in the side length.
- [Balanced order reduction](FourTensorAndGroupIsomorphismResults/order.md). Changes order-$d$ free tensors to three-tensors with side length $O(d^6 n^{\lceil d/3\rceil})$ over any commutative ring.
- [Nonfree tensor isomorphism](FourTensorAndGroupIsomorphismResults/torsion.md). Gives subquadratic-exponent time for tensors in arbitrary explicitly presented modules over fixed finite principal ideal rings, using the original generator counts.

Internal mathematical audits and attribution included. Publication priority unestablished.
<!-- four-tensor-and-group-isomorphism-results:end -->

<!-- subquadratic-exponent-ring-tensor-isomorphism:start -->
[Subquadratic-Exponent Tensor Isomorphism over Fixed Integer Moduli](SubquadraticExponentRingTensorIsomorphism/PROOF.md) — Gives an exact $2^{O(n^{7/4}\log(n+2))}$-time algorithm for unrestricted free three-tensor isomorphism over every fixed even integer modulus, including $\mathbb Z/4\mathbb Z$, and a $2^{O(n^{3/2}\log^2(n+2))}$ bound for fixed odd moduli. Combines linear-size alternating markers, short probe lists and ordered tuple isometry. Includes a separate [class-2 group encoding](SubquadraticExponentRingTensorIsomorphism/GROUP.md) and exact finite checks for that encoding. Informal proof with independent mathematical audits. Publication priority unestablished.
<!-- subquadratic-exponent-ring-tensor-isomorphism:end -->

<!-- prime-power-tensor-isomorphism:start -->
[Prime-Power Tensor Isomorphism](PrimePowerTensorIsomorphism/PROOF.md) — Reduces unrestricted tensor isomorphism over $\mathbb Z/4\mathbb Z$ to ordinary binary tensor isomorphism by retaining the carry in a quadratic augmentation quotient. Proves deterministic polynomial-time many-one equivalence of the free and arbitrary-module versions over fixed finite commutative rings with the same prime divisors of their characteristics. The [audit](PrimePowerTensorIsomorphism/AUDIT.md) credits the established carry machinery and explains the connection to the same-characteristic finite-field clause of Grochow–Qiao’s Open Question 7.6. Informal proof. Publication priority unestablished.
<!-- prime-power-tensor-isomorphism:end -->

<!-- crossed-flattening-benchmark:start -->
[Crossed-flattening tensor-isomorphism benchmark](CrossedFlatteningBenchmark/BENCHMARK.md) — Benchmark of constructive exact tensor matching on published MatTen, Semeion and orthogonal-array inputs. Reports complete coverage censuses, exact witness checks, cold and resident runtime measurements against CaDiCaL and Z3 adapters, and the effect of fraction-free rational arithmetic.
<!-- crossed-flattening-benchmark:end -->

<!-- tensor-coordinate-recovery:start -->
[Recovering hidden coordinates directly from tensors](TensorCoordinateRecovery/RESULTS.md) — AI-assisted informal proofs. Gives constructive ordinary and determinant-one isomorphism on a generic crossed-flattening class, maximal pairwise repetition extraction and recovery of labeled slice subspaces, stable block recovery in noisy data, and growing-width determinant-labeled pencil algorithms.
<!-- tensor-coordinate-recovery:end -->

<!-- four-isomorphism-research-bets:start -->
[Four algorithmic results on pencils, groups, channels, and designs](FourIsomorphismResearchBets/RESULTS.md) — AI-assisted informal proofs. Constructs rational binary-pencil transporters and isolates the determinant-one norm conditions, recovers rank-metric quotient information with group Weisfeiler–Leman refinement, derives quantitative separation and graph recovery for noisy isospectral Choi matrices, and reconstructs vectorial bent functions from unlabeled vanishing-flat designs.
<!-- four-isomorphism-research-bets:end -->

<!-- tensor-isomorphism-advances:start -->
[Four advances in tensor, group, and geometric isomorphism](TensorIsomorphismAdvances/RESULTS.md) — AI-assisted informal proofs. Gives unrestricted tensor-isomorphism encodings by pure quadratic Hamiltonian shears and smooth rational Fano varieties of Picard rank two, a compact class-two group family with fixed commuting relations, character-degree multiplicities and bounded-generator probe counts, and an exact number-field norm obstruction in regular semisimple determinant-one binary pencils.
<!-- tensor-isomorphism-advances:end -->

<!-- further-isomorphism-transfers:start -->
[Four further isomorphism transfers](FurtherIsomorphismTransfers/RESULTS.md) — AI-assisted informal proofs. Gives an exact reduction of arbitrary ordered 3-tensor isomorphism to polynomial conjugacy of quadratic symplectic maps over any field, a deterministic polynomial-time rational TI and SL-TI algorithm for square three-slice pencils with geometrically irreducible determinant, and graph-isomorphism equivalences for isospectral entanglement-breaking channels and specified persistence local systems.
<!-- further-isomorphism-transfers:end -->

<!-- tensor-isomorphism-structural-combinations:start -->
[Four structural combinations for tensor isomorphism](TensorIsomorphismStructuralCombinations/COMBINATIONS.md) — AI-assisted informal proofs. Reduces arbitrary ordered 3-tensor isomorphism over any field to abstract isomorphism of smooth rational projective varieties with a fixed Tate motive per format. Realizes prescribed Frobenius isomorphism profiles and every finite abelian everywhere-local genus. Gives graph-isomorphism equivalences for recognizable wide Peirce and recoverable rank-one tensor classes, with separate determinant-one results.
<!-- tensor-isomorphism-structural-combinations:end -->

<!-- torsor-proof-circuit-crossovers:start -->
[Torsors, proof complexity, and group circuits](IsomorphismAndProofComplexityCrossovers/AUDIT.md) — AI-assisted informal proofs. Realizes torsors of linear algebraic groups as ordinary three-tensor transporters up to explicit split rational factors. Gives an explicit rational pair of side length 328 with geometrically connected stabilizers that is isomorphic over every completion and inequivalent over the rationals. Proves exact exponential Geometric IPS degree on an explicit Boolean polynomial system despite a linear-size ordinary certificate, a sparse simulation for low-pointwise-rank inversion over finite fields, and a quantitative depth bound for arbitrary Cayley-table subgroup membership. Includes the [supporting inversion proofs](InversionProofComplexity/AUDIT.md).
<!-- torsor-proof-circuit-crossovers:end -->

<!-- inversion-proof-complexity:start -->
[Inversion in algebraic proofs of tensor nonisomorphism](InversionProofComplexity/AUDIT.md) — AI-assisted informal proofs. On explicit concise semisimple multiplication tensors in every fixed positive characteristic, ordinary Polynomial Calculus needs exponential sparse size while fully annotated degree-five PC+INV refutations have polynomial size and use one inversion with variable-or-zero entries. Gives a sharp symbolic-rank and degree bound on eliminating inversion steps, exact proof-degree transfer under regular-sequence pullbacks, and an exponential ordinary-PC versus polynomial annotated PC+INV separation for succinct special-group isomorphism equations. Also gives a polynomial-size Geometric IPS construction from one-linear-form certificates with finite-field axioms. Includes scope, attribution, and exact controls.
<!-- inversion-proof-complexity:end -->

<!-- matrix-code-equivalence-benchmark:start -->
[Matrix-Code Equivalence benchmark](MatrixCodeEquivalenceBenchmark/README.md) — Executable prime-field solver and packed binary backend extending the tensor rank-profile method to left–right equivalence of matrix codes. It decided all 89 independently labelled pairs of published Morrison representatives and recovered a witness for the 4 × 6 Oxford MEDS teaching example. It beat an exact two-row reference on four of six matched Morrison pairs, and on a synthetic rectangular binary cohort the richer rank profiles improved end-to-end time by 18.5× against the same solver with single-word ranks. Includes informal proofs, exact controls, runnable code and raw timings.
<!-- matrix-code-equivalence-benchmark:end -->

<!-- balanced-ti-benchmarks:start -->
[Balanced Tensor Isomorphism benchmark](BalancedTensorBenchmark/README.md) — Executable binary tensor-isomorphism pipeline using the balanced product trees. Includes an implicit encoder, smaller exact rank and spectral tags, exact native backends, and reproducible Traces and CaDiCaL comparisons. The implicit pipeline decided 106 of 106 inputs. With the same grouped-rank backend and a 250 ms native budget, balanced groups completed 105 of 106 and the half split completed 74. With a common fallback, the balanced layout reduced median order-12 runtime from 11.77 ms to 9.61 ms. The executable and smaller tag proofs were reviewed informally, with exact controls. The original reduction has its separate Lean certificate.
<!-- balanced-ti-benchmarks:end -->

<!-- isomorphism-crossovers-round-three:start -->
[Cayley group membership and tensor isomorphism crossovers](IsomorphismCrossoversRoundThree/AUDIT.md) — AI-assisted informal proofs. Gives polynomial-size uniform circuits of depth o(log n) for subgroup membership in arbitrary Cayley tables and depth O(log log n) when the generated subgroup has bounded-rank nonabelian composition factors, addressing part of Stober–Thumm–Weiß Question 39(2). Reduces finite-field tensor isomorphism to literal scalar extensions in the same fixed characteristic at unchanged tensor dimensions. Establishes constant-degree Polynomial Calculus equivalence for graph isomorphism and Grigoriev bare multiplication tensors, a variant of Galesi–Grochow–Pitassi–She Question 7.5. Gives a fixed-signature algebraic reduction for special-linear orbit closure intersection of all matrix pencils, the one-mode-dimension-two case of Lysikov–Walter Question I.13, using Pervouchine’s invariant classification. Publication priority is unestablished.
<!-- isomorphism-crossovers-round-three:end -->

<!-- isomorphism-crossovers-round-two:start -->
[Finite-ring tensor isomorphism, quartic degeneration, and group algorithms](IsomorphismCrossoversRoundTwo/AUDIT.md) — AI-assisted informal proofs. Reduces module and free tensor isomorphism over each fixed finite commutative ring of characteristic p^e to ordinary tensor isomorphism over the prime field, with reverse reductions. Compiles the full degeneration order of an ordinary tensor into one symmetric balanced quartic and proves NP-hardness of directed containment even when all polynomial invariants agree. Gives logspace-uniform FOLL cyclic basis extraction and canonical labeling for abelian Cayley tables and AC⁰ decision at fixed exponent. Gives deterministic logspace and uniform FOLL algorithms outputting minimum generating sets for nilpotent groups, answering Collins–Grochow–Levet–Weiß Remark 7.7. Answers Collins–Levet Question 8.2 by recognizing simplicity in uniform FOLL and computes minimal normal subgroups and nonabelian socle factors in that depth. Extends the central-extension algorithm beyond product quotients under an explicit prime-detection condition, including the coprime case of Grochow–Qiao Open Problem 8.3. Includes supporting proofs and exact finite checks. Publication priority is unestablished.
<!-- isomorphism-crossovers-round-two:end -->

<!-- four-isomorphism-proof-crossovers:start -->
[Four crossovers in isomorphism and proof complexity](IsomorphismProofCrossovers/AUDIT.md) — AI-assisted informal proofs. Shows every inconsistent polynomial system refutes at its maximum axiom degree in the published PC+INV proof-line degree model, giving degree-three geometric tensor nonisomorphism refutations and refuting Galesi–Grochow–Pitassi–She Conjecture 1.7. With charged circuit annotations, PC+INV and the Ideal Proof System have polynomial-size translations in both directions. Extends both perfect product quotient cases of Grochow–Qiao Theorem 7.1 to arbitrary abelian centers in polynomial Cayley-table time. Gives a balanced orthogonal and unitary d-to-3 tensor reduction of total side dimension O(n^ceil(d/3)), and explicit sparse closed symmetric quartic orbits requiring invariant degree Θ(n·2^n) to separate. Includes exact finite controls. Novelty remains subject to review.
<!-- four-isomorphism-proof-crossovers:end -->

<!-- central-extension-cosets:start -->
[Group isomorphism through central extension cosets](CentralExtensionCosets/PROOF.md) — AI-assisted informal proof, not Lean-verified; publication priority unestablished. Combines finite-ring unit orbits, prime-power subgroup transport, and extension cohomology to process solvable cosets of quotient maps in polynomial Cayley-table time for central kernels. For raw class-two groups, gives polynomial time times complete-flag counts for the equal-order cyclic blocks of the central quotient; in particular, polynomial time when those multiplicities are bounded, without a bound on total rank or exponents. Includes witnesses, full isomorphism cosets and exact counts. Does not claim an unrestricted record or closure of the general abelian-radical or TI versus SL-TI questions.
<!-- central-extension-cosets:end -->

<!-- abelian-extension-linearization:start -->
[Polynomial isomorphism of diagrams of abelian group extensions](AbelianExtensionLinearization/PROOF.md) — AI-assisted informal proof. Reduces simultaneous isomorphism of abelian extensions, with supplied quotient isomorphisms, commuting arrows, and marked elements, to one finite-module isomorphism instance. Decision and search are polynomial in the bit length of explicit quotient/action/cocycle data, with binary-encoded kernels. Cayley-table inputs also admit full cosets and exact counts without computing ring unit groups. Answers Skresanov’s quotient-generator question and the Theorem 6.11 extension requested in the first part of Grochow–Qiao Open Problem 8.1; does not settle its unrestricted polynomial-time question.
<!-- abelian-extension-linearization:end -->

<!-- group-graph-tensor-crossovers:start -->
[Group, graph, and tensor isomorphism crossovers](GroupGraphTensorCrossovers/PROOF.md) — AI-assisted informal proofs. Answers Skresanov's generator-bound question for lifting over arbitrary abelian kernels and the abelian-radical extension part of Grochow–Qiao Open Problem 8.1. Gives NP-completeness of succinct Fitting-free Group Epimorphism even on a family with polynomial-time isomorphism, exact epimorphism counting for coprime elementary-abelian layers from Cayley tables, and polynomial Frattini-coset lifting under bounded composition factors. The graph-tensor constructions preserve exact transporters and permutation parity, allow raw tensor decoding, and transfer a linear refutation-degree lower bound to sparse cubic-form equivalence.
<!-- group-graph-tensor-crossovers:end -->

<!-- group-isomorphism-and-epimorphisms:start -->
[Group isomorphism search, counting, and epimorphisms](GroupIsomorphismAndEpimorphisms/PROOF.md) — AI-assisted informal proofs. Search, exact counting, and automorphism generators reduce in polynomial time to isomorphism decision for every finite $p$-group, using only same-prime $p$-group queries. A separate reduction keeps Frattini-class-two queries inside that class. Answers Grochow–Srivastava–Thakkar Open Question 3(1), the constant-size clause of 3(2), and the cited odd generalized-Heisenberg quotient case of 3(3) with constructive algorithms and exact epimorphism counts.
<!-- group-isomorphism-and-epimorphisms:end -->

<!-- simple-quasigroups-and-circuit-bounds:start -->
[Simple quasigroup generators, Cayley circuit bounds, and graph multiplicities](SimpleQuasigroupsAndCircuitBounds/PROOF.md) — AI-assisted informal proofs. Answers Grochow–Kardeş–Levet's finite-simple-quasigroup generation question by constructing simple loops of order $8^m$ requiring exactly $2m$ generators. Extends Cayley-table lower bounds to depth-three circuits with bounded output fan-in. Gives a sublinear graph-size exponent for the multiplicity-obstruction part of Grochow–Urisman Question 1.10, with a separate degree-dependent factor, and proves the Carlson–Kovács factorization assertion for every finite $p$-group with central Frattini subgroup.
<!-- simple-quasigroups-and-circuit-bounds:end -->

<!-- cayley-circuits-and-decompositions:start -->
[Cayley-table lower bounds, quasigroup decomposition, and characteristic-two symmetrization](CayleyCircuitsAndDecompositions/PROOF.md) — AI-assisted informal proofs. Answers Grochow–Kardeş–Levet Question 7.1 and strengthens the bound for Question 7.3 with $2^{\Omega(\sqrt n)}$ lower bounds for both CNFs and DNFs on valid Abelian Cayley tables along an infinite sequence of orders $n=3^r$. Answers Johnson–Levet–Vojtěchovský–Widholm Question 7.4 with a deterministic polynomial-time algorithm for fully refined direct product decomposition of arbitrary quasigroups. Answers the symmetrization part of Ivanyos–Qiao's characteristic-two question constructively over every characteristic-two field. Also refutes Osterlund's Loewy-length conjecture for regular-module tensor products and resolves the Frattini-class-two case of Carlson–Kovács over arbitrary coefficient fields of characteristic $p$.
<!-- cayley-circuits-and-decompositions:end -->

<!-- cayley-table-and-group-algebra:start -->
[Cayley-table and modular group algebra results](CayleyTableAndGroupAlgebra/PROOF.md) — AI-assisted informal proofs answering Johnson, Levet, Vojtěchovský and Widholm’s Questions 7.1–7.3 and 7.5. They prove bounded count-free Weisfeiler–Leman dimension for uniquely decomposable groups, constant-round counting Weisfeiler–Leman without uniqueness, and deterministic logspace algorithms for fully refined group decomposition and central quasigroup isomorphism. The two Weisfeiler–Leman results apply to groups with boundedly generated indecomposable factors. They answer García-Lucas, del Río and Sakurai’s Remark 7 over all characteristic-p fields. The collection also gives sharp Cayley-table recovery bounds, including a negative answer to Huh’s Open Problem 2 under scalar tensor-entry sampling. The modular group algebra proof recovers Sakurai’s earlier answer to Question D.
<!-- cayley-table-and-group-algebra:end -->

<!-- hypoworlds-case-proofs:start -->
[HypoworldsCaseProofs/PROOF.md](HypoworldsCaseProofs/PROOF.md) — Five AI-assisted informal results using exhaustive case crossing. Gives a quasipolynomial versus $2^{\Theta((\log n)^3)}$ depth-three/DNF separation on the same canonical Group Isomorphism promise, sharp symmetric-group occurrence recovery in even degree, and $\Theta_2^{\mathrm P}$-completeness for both monophonic position colouring variants at diameter two. Also constructs an absolutely simple evolution-algebra Hasse counterexample over $\mathbb Q(\sqrt{-3})$ and classifies the maximal automorphism orders and equality types of simple evolution algebras over every field.
<!-- hypoworlds-case-proofs:end -->

<!-- isomorphism-and-graph-complexity:start -->
[IsomorphismAndGraphComplexity/PROOF.md](IsomorphismAndGraphComplexity/PROOF.md) — Abelian group isomorphism, symmetric-group occurrences, and two complexity classifications. Answers Grochow–Kardeş–Levet Question 7.3 with a quasipolynomial DNF lower bound on valid Abelian Cayley tables, and resolves the converse after Grochow–Urisman Lemma 6.11(2) with a counterexample and an exact sufficient padding bound. Reduces linear code equivalence to lattice isomorphism over every fixed non-prime finite field and proves $\Theta_2^{\mathrm P}$-completeness of Monophonic Position Set at diameter two. An additional note addresses the algorithmic clauses of Kaygorodov–Martín González–Viruel Question 50. AI-assisted informal proofs.
<!-- isomorphism-and-graph-complexity:end -->

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


<!-- lean-library-transfers-november-14:start -->
### Raw Determinant Profiles from Rectangular Pencil Components (informal)

[Proof](RectangularPencilDeterminantProfiles/Proof.md). Gives a polynomial-time ordinary-TI Turing reduction for the full determinant profile over every fixed finite field when factors of maximal minors on bounded indecomposable components supply covectors spanning to logarithmic codimension. An explicit growing balanced family over F₃ has identically zero full determinant and only rectangular indecomposable components.

### Eliminating Generic Auxiliary Inputs from Symmetric Arithmetic Circuits (informal)

[Proof](PermanentAuxiliaryInputSymmetrization/Proof.md). Gives a deterministic joint interpolation certificate for deleting many generic dense linear inputs while preserving an invariant polynomial. An exact injection-sum circuit symmetrizes marked-vertex linear inputs without listing their placements. These conclusions apply to the stated circuit representations and give restricted permanent lower bounds.

### Local Zariski Closures and Simultaneous Recurrence over Number Fields (informal)

[Proof](LocalZariskiClosureNumberFields/Proof.md). Uses Faltings and Mordell–Lang to describe local Zariski closures for projective curves and subvarieties of abelian varieties. It proves simultaneous-place recurrence outside a finite exceptional set for dimension-one Diophantine presentations and identifies Mordell–Weil input reusable in the Manin formalization.
<!-- lean-library-transfers-november-14:end -->


<!-- ti-determinant-profiles-literature:start -->
[Tensor Determinant Profiles](TensorDeterminantProfileMethods/PROOF.md) — Partial progress on Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9. Four informal methods give exact determinant tests on fixed-finite-field classes using unordered pencil factors, Frobenius frames, semisimple derivation envelopes and ordered form tuples. Includes polynomial-size ordinary-TI instances on the stated classes and an adaptive reduction for arbitrary split-factor matches with a small common kernel. Unrestricted SL-TI containment remains open.
<!-- ti-determinant-profiles-literature:end -->


<!-- raw-residue-determinant-tests:start -->
[Determinant Constraints on Raw Residue Tensors](RawResidueDeterminantTests/PROOF.md) — Partial progress on Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9. Informal proofs of one-instance reductions for intrinsic block graphs, semilinear adjoint fields and radical filtrations under explicit conditions. An additional exact polynomial-time algorithm uses low-rank moments and applies to a growing family with absolutely irreducible determinants and scalar stabilizers. The unrestricted reduction remains open.
<!-- raw-residue-determinant-tests:end -->


<!-- higher-order-measurements-and-algebra:start -->
[Higher-Order Measurements and Algebra](HigherOrderMeasurementsAndAlgebra/PROOF.md) — Four informal answers. Resolves Designolle–Farkas's algebraic versus spectral $k$-fold unbiasedness question and their maximal-eigenspace parent criterion at arbitrary order and rank. Answers Hu–van Melkebeek's Section 5 multilinear sparsity-lifting question with exact width in every ROABP order. Proves Kaygorodov–Martín González–Viruel Conjecture 8 on polynomial-on-residue-classes counts of perfect evolution algebras. A separate note corrects the characteristic-two distribution in the finite-field consequence of their Conjecture 2.
<!-- higher-order-measurements-and-algebra:end -->
