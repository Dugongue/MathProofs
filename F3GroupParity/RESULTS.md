# Even isomorphism of compact exponent-three groups

We use ordered commutator coordinates for special groups of class two and exponent three. A transporter has permutation sign equal to the product of its determinants on the central quotient and the center. The ordinary outputs can be read as symmetric-group conjugacy of the left-regular subgroups in the same compact model.

| Result | Scope and reduction |
| --- | --- |
| [Centroid decomposition and one comparison](CentroidProductParity.md) | One ordinary TI instance combines the signs of arbitrarily many intrinsic factors. A factor can use an odd quotient dimension or a logarithmic exterior-square kernel. Odd-dimensional additive factors may repeat freely. Repeated even-dimensional types must admit an odd automorphism or be handled by the polynomial-time factor extension below. |
| [Relative genus at most two](LocalCentroidGenus.md) | Deterministic polynomial bit time for arbitrary products with local relative genus at most two. Centroid radicals, extension degrees and multiplicities may grow. A canonical coefficient field exposes the alternating pencil without requiring the local centroid to be a field. |
| [Strict and centroid sign corrections](StabilizerAndGenus.md) | Exact polynomial-time tests for two subgroups that can supply an odd automorphism. Either positive test gives one ordinary comparison. The chapter gives the full relative genus-two algorithm, including singular pencils, and direct polynomial decision for sufficiently small centers. |
| [Logarithmic kernels, centers and radicals](CenterAndKernel.md) | A logarithmic exterior-square kernel gives one query. A logarithmic center with the stated scalar-form probes also gives one query. All logarithmic-dimensional centers admit a polynomial adaptive TI reduction. |
| [Intrinsic points and flags](IntrinsicFlagsAndPoints.md) | Polynomial adaptive TI reduction from invariant spanning point lists in the quotient or dual center, or from invariant flags with logarithmic graded widths. |

The many-one and adaptive claims have different hypotheses. The unrestricted compact $A_N$-to-$S_N$ reduction and the resulting equality $\mathsf{TI}=\mathsf{TI}_{\rm SL}$ over $\mathbb F_3$ remain open in this work. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

[Verification](Verification.json) records the independent Lean checks of the two Boolean and centroid lemmas, and the bounded computational controls. The group algorithms and reductions are written proofs.
