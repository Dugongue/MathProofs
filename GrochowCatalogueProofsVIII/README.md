# Grochow research catalogue proofs VIII

This packet gives written arguments for **21 additional catalogue entries**. The 196 counted entries in the preceding seven proof packets are excluded.

Each proof specifies the model or parameter regime in which its conclusion holds.

Oriented castling gives exact determinant images and special-linear transport over any finite field on the accepted class. Two compatible quotient isomorphisms lift through abelian Lie ideals by a deterministic module-isomorphism algorithm. Finite abelian groups have an exact count of minimum faithful actions, including the order-four elementary abelian cases. Doubling the ideal precision gives uniform NC normal forms for principal congruence groups over each fixed prime field. [Oriented castling](OrientedCastlingDeterminantImages.md) · [Simultaneous lifting](CompatibleLieQuotientLifts.md) · [Minimum actions](AbelianMinimumActionCounts.md) · [Parallel normal forms](PrincipalCongruenceParallelWords.md)

Lean checks two identities used in the parallel normal-form proof. The catalogue results have written proofs.

[Proof dependencies](DAG-Connections.md) · [Verification](Verification.json) · [Machine-readable index](Resolutions.json)

| Entry | Result | Scope |
| --- | --- | --- |
| [GP-0163](CriticalRectangularStabilizers.md) | Compute the full stabilizer law and all-target witness algorithm in the sharply rectangular critical window. | proved with scope |
| [GP-0243](SplitAlternatingPencilGenerators.md) | Construct full pseudo-isometry generators for regular split alternating pencils with supplied roots and field generator, including repeated blocks in characteristic two. | proved with scope |
| [GP-0280](OrientedCastlingDeterminantImages.md) | Compute the exact stabilizer determinant image and decide special-linear transport on a rank-certified castling class over every finite field. | proved with scope |
| [GP-0286](FullRankMatrixForestTransport.md) | Decide exact orthogonal or unitary transport on full-rank matrix forests with unbounded block sizes and rational Gram spectra. | proved with scope |
| [GP-0334](BinaryCodeIsometryExtensions.md) | Extend every isometry of a binary linear code under a checkable pair-sum condition, and give an explicit nonextendible example. | proved with scope |
| [GP-0359](DyadicFrattiniEpimorphisms.md) | Construct marked exponent-four epimorphisms onto targets with a one-dimensional Frattini subgroup using complete scalar square-form data. | proved with scope |
| [GP-0390](AbelianMinimumActionCounts.md) | Count all minimum-degree faithful actions of finite abelian groups, with the additional order-four elementary cases at the prime two. | proved with scope |
| [GP-0414](CompatibleLieQuotientLifts.md) | Lift two compatible quotient isomorphisms through abelian ideals over a finite field by constructive module isomorphism. | proved with scope |
| [GP-0421](PrincipalCongruenceParallelWords.md) | Compute normal forms and short presentations for principal congruence groups in uniform NC over a fixed prime field with an adapted filtration basis. | proved with scope |
| [GP-0505](SimpleProductMinimalTransitivity.md) | Recognize minimal transitivity in Cartesian products of supplied nonabelian simple actions, with fixed-parameter time in the largest point stabilizer order. | proved with scope |
| [GP-0581](RegularQuadraticPowers.md) | Construct regular determinant pencils for quadratic powers with sharp size along the stated powers and dimensions. | proved with scope |
| [GP-0607](PrimePowerScaledFactoring.md) | Lift prime-power factorizations to arbitrary precision in a recognized integral Newton scaling regime. | proved with scope |
| [GP-0690](HiddenWidthOneRecovery.md) | Recover exact rational affine coordinates of concise hidden width-one ROABPs in deterministic polynomial bit time. | proved with scope |
| [GP-0719](SignedBinomialPCBits.md) | Control proof bit size without raising polynomial-calculus degree for signed binomial axioms. | proved with scope |
| [GP-0753](FixedRankTorusSeparators.md) | Construct uniformly separating invariant monomials on every coordinate stratum for a fixed-rank binary-weight torus. | proved with scope |
| [GP-0863](LinearConnectedPermutationCanonization.md) | Canonize a connected tuple of permutations in linear time given the stated cycle-signature certificate or a transitive constituent cycle. | proved with scope |
| [GP-0864](LinearDisconnectedPermutationAssembly.md) | Assemble and deduplicate connected tuple canonizations in deterministic linear time, preserving the total input bound. | proved with scope |
| [GP-0878](ClusterPartialDeckThreshold.md) | Compute exact adversarial partial-deck thresholds of all cluster graphs against arbitrary competitors, together with ally thresholds. | proved with scope |
| [GP-0887](MonotoneWalkAndRefinementSeparators.md) | Build monotone polynomial-size invariants for ordinary refinement and for separation of a specified spectral twin class from every competitor. | proved with scope |
| [GP-0939](TwoTerminalMotifCounting.md) | Count induced motifs exactly on hosts with one- and two-terminal pieces and binary repetition counts. | proved with scope |
| [GP-0968](QuantumCompactTwinRefinement.md) | Decide quantum compactness and compute the quantum orbital partition when walk-seeded refinement separates twin classes. | proved with scope |

## Additional proofs

The following consequence is outside the main count.

- [GP-0391](AbelianMinimumActionCounts.md) For finite abelian groups, the number of minimum actions up to twisting is one plus the floor of half the number of direct order-two factors.
