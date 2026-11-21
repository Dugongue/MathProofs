# GP-0279 · Rank-controlled reduction from arbitrary tensor order to order three

**Result.** Ordinary dense d-tensor isomorphism reduces to one ordinary three-tensor isomorphism instance whose mode dimensions and ordinary tensor ranks are bounded by a fixed polynomial in d and the two input tensor ranks. The degree of this polynomial stays fixed as d grows. The computation uses no rank decomposition or rank oracle. The proof is written.

Let T be a nonzero tensor in V_1⊗⋯⊗V_d. Replace each V_i by its contraction support U_i, the image of the flattening from the dual of all other modes. Their tensor product contains T. For an input pair with the same original mode dimensions, equivalence on these supports is equivalent to ambient equivalence: an ambient transporter must carry each contraction support to its counterpart, and conversely any isomorphisms on the supports extend to the original factors. Each dim U_i is at most the ordinary tensor rank of T.

For 1≤i≤d let P_i be the image of the prefix flattening into U_1⊗⋯⊗U_i. In particular P_d=F T. Put P_0=F. Every P_i has dimension at most ordinary tensor rank, since each pure summand contributes at most a rank-one matrix to this flattening. For every i there is a natural inclusion

    φ_i : P_i ↪ P_{i−1} ⊗ U_i.

Indeed, expand any suffix contraction as a vector in (⊗_{j<i} U_j)⊗U_i and examine its coordinates in a basis of U_i. Each coordinate is a contraction of T along modes i through d and belongs to P_{i−1}. The composite iterating these inclusions takes the element T of P_d to the original tensor T in the product of the U_i. Choose 1 as the basis of P_0 and T as the basis of P_d.

A product-mode transporter on the U_i induces unique maps on all P_i by restriction of the prefix products, respecting each inclusion and the endpoint bases. Conversely if such maps respect the inclusions and endpoint bases, compose the inclusions to recover the original transport equation. Dualizing gives bilinear maps

    B_i : P_{i−1}^* × U_i^* → P_i^*,

with fixed vectors the dual bases of P_0 and P_d. The isomorphism condition for this chain of indexed maps with its fixed endpoint vectors is therefore exactly the input orbit condition.

## Fixed-signature compression of all the bond maps

An application of a compiler for a growing number of tensor slots could obscure exponential dependence on d. Instead use one fixed-signature tensor system. Let X be the direct sum of all the P_i^* and U_i^* as distinguished blocks. Set C=F^{2d+1} with coordinatewise multiplication and ordered coordinate idempotents e_1,…,e_{2d+1}. Include the fixed linear endomorphism of C given by e_j↦e_{j+1} for j<2d+1 and e_{2d+1}↦0. An algebra automorphism of C permutes the e_j. Commuting with the endomorphism fixes the last idempotent and then every predecessor, so the automorphism is the identity. Include the bilinear action C×X→X with e_j acting by projection onto the j-th block. Preserving the action forces a linear isomorphism on X to preserve each block. Define one bilinear map X×X→X whose restrictions on the ordered pairs P_{i−1}^* × U_i^* are the B_i, extended by zero on all other block pairs. Include the two fixed endpoint vectors of X. This fixed list of tensors, of orders one, two and three, is isomorphic exactly when the bond system is isomorphic. All sorts, slots, and primal and dual occurrences are fixed independently of d.

Apply the fixed-signature compilation theorem of Futorny–Grochow–Sergeichuk, also presented in linear-model language by Grochow–Qiao, to reduce the isomorphism of these systems to ordinary three-tensor isomorphism over the same field. Since dim C=2d+1 and dim X ≤ (2d+1) r for r the input rank, the compiled dimensions of a paired instance are bounded by a fixed polynomial in d and the larger input rank. The ordinary rank of an order-three tensor is at most the product of any two of its mode dimensions, proving the stated rank bound. No rank assumption is needed by the reduction algorithm. It computes the supports and bond spaces with ordinary flattening ranks, and their bases and inclusions by Gaussian elimination. Over finite fields in the usual presentation this is polynomial bit time in the dense input. Over other fields the same construction is polynomial in field operations. Compare the original mode dimensions, handle zero tensors directly, and use fixed yes or no pairs when these basic tests already decide equivalence.

The use of all prefix flattenings adds a rank parameter to the earlier balanced order-reduction strategy. The coordinate algebra with a shift packages variable many labels in a signature to which a fixed-signature structural compiler actually applies.

[Futorny–Grochow–Sergeichuk, Theorem 1.1 and Remark 1.1](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Part I](https://arxiv.org/abs/1907.00309) · [Project fractional order reduction](https://github.com/Dugongue/MathProofs/tree/b0947ecc8675432a7292628b99e945b7d50b216e/FractionalTensorOrder)
