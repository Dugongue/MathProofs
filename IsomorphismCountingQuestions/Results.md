# Four questions on homomorphism counts, code equivalence, and finite groups

The following are informal proofs. No publication-priority claim is made.

1. [Biclique homomorphism indistinguishability](Biclique.md) is \(\mathsf C_{=}\mathsf P\)-complete under deterministic polynomial-time many-one reductions. The hardness construction already gives uncolored bipartite targets. This answers the question before Theorem 7.1 of Curticapean–Neuen–Nikabadi–Seppelt–Young. It gives an unconditional many-one hardness result for homomorphism indistinguishability over cographs as well.
2. [A Spoiler–Duplicator game for dense Weisfeiler–Leman](DenseWL.md) answers the authors' §9 game question. A separate implementation improves the \(4^{kn}\operatorname{poly}(n,k)\) bound for stable dense refinement to \(2^{(k+1)n}\operatorname{poly}(n,k)\) for \(k\ge2\). The optimal exponential base remains open.
3. [Sum-rank code inequivalence without cyclic evaluation sets](RankDual.md) answers the §6 question of Santonastaso–Zullo about Theorem 5.20. It establishes all three comparisons in the paper's strong-equivalence model, including the printed divisibility condition in the third comparison.
4. [Power-root divisibility by the normalizer](NormalizerPowerRoots.md) answers Lazorec's question after Lemma 2.1 affirmatively. The proof uses conjugation orbits and Frobenius's per-target divisibility theorem and also handles simultaneous powers.

[Rank-metric extension](RankMetric.md) is a separate result. It classifies all single-block ambient formats over finite fields and records the earlier counterexample that already answered the general nondegenerate extension question in the negative.
