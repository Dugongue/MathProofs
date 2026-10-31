# Separate AI-Worker Audit of Affine Tensor Isomorphism

The explicit group Aff(n,K)=[[A,b],[0,1]] is the standard homogeneous-coordinate representation of the full affine group. The source Section 1.5 asks about TI_G for affine groups as a future family direction; it does not identify this as Open Question 1.8, 1.9, 1.10 or 1.11, and does not define a different affine representation that this proof would fail to cover. The artifact correctly avoids claiming those numbered questions solved.

The zero-padding lower reduction uses the invariant linear kernel of the last covector; translation columns have no action on tensors supported in that kernel. This covers every tensor, including zero and nonconcise tensors. In the upper reduction, fixing the covector as a value forces the final row to be exactly (0,...,0,1), rather than merely proportional. This is precisely the full affine group with no quotient-scale error. The source's tensor-system definition genuinely allows dual factors and order-one tensors, and Theorem 4.1 explicitly gives polynomial dimensions for fixed component count. Thus the four-component application is within the actual theorem, not an assumed compiler. The source preliminaries also justify constant-free, all-field reductions and representable-field bit complexity.

The optional variable-size pointwise-quotient family is valid too: the regular nilpotent plus cyclic-vector frame forces the entire auxiliary transporter to identity, and the projection tensor then fixes all quotient coordinates pointwise. There are ten components independent of quotient dimension, so the compiler's exponential dependence on component count stays constant. This does not assert equality for full parabolics, Borel groups, or form-preserving groups. It is a valid extension of the defined affine result.
Primary source verified directly: https://arxiv.org/html/2306.03135v2#S1.SS5, its Section 2 field conventions, Section 4 tensor systems and Theorem 4.1.

No new novelty search, exhaustive computation, kernel audit or publication-priority claim was performed for this outside audit. The conclusion is that the stated informal assembly proofs are sufficient for their frozen roots and are appropriately scoped, not that all adjacent named problems or stronger uniformity variants have been solved.

No independent human review or Lean verification is claimed.
