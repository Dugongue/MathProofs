# Almost-all ordinary four-tensor isomorphism

For each fixed finite field $\mathbb F_q$, ordinary isomorphism of ordered $n\times n\times n\times n$ tensors has a deterministic polynomial-bit-time algorithm that recognizes a $1-o(1)$ fraction of uniform first inputs. On every recognized first input it decides correctly against every second input. It can abstain on exceptional first inputs and every returned answer is exact.

The old fixed-field recognizer used a singular pair flattening. An invertible flattening supplies a tensor in the four dual modes by inverse transpose. Crossed contractions and squared partial traces give one conjugation-equivariant matrix per mode. A common square-zero random shear and two polarized rank estimates show that each operator is close to a uniform matrix in the appropriate affine space. These marginal estimates suffice for the primary-decomposition and exact cyclic-quotient comparison.

- [Main decision proof and bit-time assembly](FullCoverage.md)
- [Marginal distribution proof over every fixed finite field](SingleAnchor.md)
- [Explicit transporters, determinant constraints over the residue field, and lifting to Galois rings](SearchAndLifting.md)
- [Inverse-polynomial rejection for any fixed requested power](SharperCoverage.md)
- [Distribution and primary-count details](Distribution.md)

An independent route using reciprocal cuts alone gives coverage $1-c(q)^5-o(1)$, where $c(q)=\prod_{j\ge1}(1-q^{-j})$. Over $\mathbb F_2$, this increases the earlier singular-cut coverage from $97.59\%$ to $99.80\%$. The [reciprocal-cut proof](Anchors.md) uses a matrix-inverse Fourier estimate and joint corank moments. The [mixed-ratio algorithm](MixedRatios.md) and [one-mode commutant algorithm](Operators.md) have simpler transporter recovery on their certified domains and include exact binary controls.

The proofs are informal. This extends the [previous fixed-field result](https://github.com/Dugongue/MathProofs/blob/main/FixedFieldOrdinaryFourTI/PROOF.md) for [Li–Li–Qiao–Tao–Wang, arXiv v2 Problem 1.7](https://arxiv.org/html/2604.00591v2). The recognition guarantee is for a uniform first tensor, with the target unrestricted.
