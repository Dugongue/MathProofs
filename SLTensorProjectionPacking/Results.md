# Safe projections and one-instance packing for SL tensor isomorphism

These informal proofs give deterministic single-instance reductions over F₃ on their stated domains. The unrestricted three-to-two reduction remains open.

- [Frobenius-stable factor dependencies](FrobeniusCircuits.md) use separate coefficient fields and trace relations to compute the product of the two matrix-mode signs. No common splitting field is required. The source determinant polynomial must be nonzero and split into absolute linear factors.
- [Centroid block packing](HostProfilePacking.md) handles arbitrary multiplicity, heterogeneous blocks and signed block permutations, given one ordinarily testable local character and the stated condition on its sign image. The case of a rigid character can use either the factor test or the determinant-sum test on every applicable local block.
- [Lie stabilizer and cubic supports](LieGraphSelectors.md) recovers the entire transporter sign profile on raw-recoverable properly three-edge-colored cubic supports, including when the diagonal automorphisms give no sign information. [Even cycles](EvenCycleMatrixSelectors.md) and [odd cycles](OddCycleCongruence.md) extend recovery to arbitrarily large intrinsic matrix blocks.
- [Determinant sums](DeterminantSum.md) and [signed histograms](DeterminantHistogram.md) give polynomial-time evaluation at logarithmic and square-root logarithmic total slice-rank excess, respectively. A nonzero sum or unequal sign counts determines the product of the matrix-mode signs.

Every ordinary transporter profile is empty or an affine coset in F₂³. Three prescribed two-sign projections determine the SL verdict. An unrestricted deterministic safe selector or unrestricted packing of those queries remains unresolved. [Prior exact projections](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md) · [Published endpoint question](https://arxiv.org/html/2306.03135v2#S1.SS5)

The proofs use the discipline of passing actual witness data through linked checks, motivated by the [pinned AgentAlphaXiv exact-verifier study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf). No archive code is included.

## A determinant-sum example with an absolutely irreducible factor

Take the three-by-three pencil whose rows are \((x,y,z)\), \((z,x,y)\), and \((y,-z,x)\). Its determinant is \(g=x^3+y^3-z^3-xyz\). The three partial derivatives vanish simultaneously in the projective plane only at the coordinate points, and \(g\) is nonzero there. Thus the projective cubic is smooth over the algebraic closure. It is absolutely irreducible because distinct projective plane components meet and repeated components are singular.

Over \(\mathbb F_3\), the equation \(g=0\) becomes \((1+xy)z=x+y\). Seven ordered pairs \((x,y)\) give one solution each. Two pairs have \(xy=-1\) and \(x+y=0\), and give three solutions each. There are therefore 13 zeros and 14 nonzeros among the 27 arguments. Use two copies of this pencil with the three shared labels and append \(m\) independent labelled blocks \(t_i I_2\). Their determinant is \(g^2\prod_i t_i^2\). The matrix size is \(6+2m\) and the displayed slice ranks sum to \(18+2m\), giving excess 12. The determinant sum is \(14\cdot 2^m\ne0\) in \(\mathbb F_3\). This supplies a growing family for the determinant-sum method outside the absolute linear-factor promise.
