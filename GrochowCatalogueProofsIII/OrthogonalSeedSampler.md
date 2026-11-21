# Polylogarithmic seeds for dense orthogonal tensor instances

**GP-0146.** There are explicit samplers over F5 with O(log² n) uniformly random bits, constant entrywise support density in format n × n × n, and a deterministic polynomial-time product-orthogonal transporter algorithm against every target. If the sampler uses m bits, any union of K orthogonal isomorphism classes has probability at most K 2^{-m}. The family is a structured source ensemble. Its density claim concerns the fraction of entries that are nonzero.

Let n0 be the largest power of 4 at most n and m=floor(log₂² n0), with any fixed finite small sizes handled separately. For large n, decompose each of the last two axes on the first n0 coordinates into m coordinate blocks of pairwise distinct dimensions d_i, choosing d_i=i for i<m and d_m=n0−m(m−1)/2. For b∈{0,1}^m set a_i=1+b_i in F5 and form the source

```
S_b = Σ_i a_i e_i ⊗ I_{d_i},
```

where I_{d_i} lives in the corresponding rows and columns of the last two axes. Use the standard dot form on every axis. The sampler applies fixed orthogonal Walsh–Hadamard changes on the first and second axes, supported on the first n0 coordinates. A Sylvester Hadamard matrix H satisfies HHᵗ=n0 I. In F5 the scalar n0 is a nonzero square, since n0 is a power of 4. Rescale H by its inverse square root to obtain an orthogonal matrix with full support. For each third-axis coordinate j≤n0, the block containing j specifies exactly one summand i in the tensor. At each first-axis and second-axis coordinate in the first n0 positions, the new entry is the product of a_i and two nonzero Hadamard entries. Every such triple is nonzero, so the sampler's support density is at least (n0/n)³, which is greater than 1/64. Since the sampler transformation is fixed and orthogonal, the decision and dispersion proofs can use S_b.

## Algorithm against arbitrary targets

Write the first-axis slices of a target as maps M_j:V→W. Compute the left and right cross-product spaces span{M_j M_kᵗ} and span{M_jᵗ M_k}. These spaces transform by conjugacy in W and V, respectively, under any product-orthogonal transporter. In fact any invertible relabeling of the slices preserves the spans because the cross-products are bilinear in two independently ranging slices. For S_b the two spaces are the spans of the canonical projectors on the m blocks, with a common zero eigenspace on the orthogonal complement of the blocks.

Compute the common eigenspaces of a basis of each space by successively intersecting each current subspace with the kernels of M−λI for λ∈F5. Verify that these subspaces give full orthogonal decompositions with nondegenerate restrictions. The simultaneous eigenvalue zero subspace is the complement, so its dimension must be n−n0. For the remaining spaces, verify dimensions d_1,…,d_m on each side, hence matching by the unique dimension. Equivalently, form the projectors using the decompositions and verify the cross-product spaces equal the spans of the identified nonzero-block projectors. All these tests are necessary by covariance.

Check that every slice maps each V block to the matched W block and vanishes on the complement. In each block the restricted slices must span exactly one nonzero line. Choose a generator Z_i of that line. Then the target in the i-th block has the unique form f_i⊗Z_i, using the first-axis dot form to identify the coefficients of the line with a vector f_i. Check f_i·f_j=0 for i≠j and that every f_i·f_i is a nonzero square. Write f_i=c_i u_i with u_i of norm 1 and c_i²=f_i·f_i. Check whether Z_i is an invertible map between the two nondegenerate d_i-spaces and whether its restricted adjoint satisfies

```
Z_i* Z_i = (a_i/c_i)^2 I.
```

Finally check that the form on each V_i admits an orthonormal basis. These are all necessary properties of an equivalent target. They are polynomial-time checks over F5. For the last one perform diagonalization by choosing a vector of nonzero norm and passing to its orthogonal complement. In every nonzero nondegenerate space over F5 such a vector can be found among the basis vectors and pairwise sums. Rescale each diagonal entry to 1 or 2. Pairs of 2s can be converted to pairs of 1s by the two basis vectors (2,2) and (2,−2) in the corresponding 2-space. Exactly when the remaining number of 2s is even the form admits an orthonormal basis, with necessity following from its determinant square class.

For sufficiency, send the source e_i in the first axis to u_i. Extend to the first-axis complement by an orthogonal map. This is possible because the orthogonal complements have equal dimensions and determinant square classes, and the preceding diagonalization gives explicit maps. In each V_i choose an orthonormal basis by the same procedure, and as the W_i basis use its image under (c_i/a_i)Z_i. The adjoint condition makes this image orthonormal. Thus the three specified maps take every term a_i e_i⊗I_{d_i} to f_i⊗Z_i. Extend the last two maps orthogonally across the inactive complements, whose determinant square classes agree by the same argument. This produces a transporter. The total work is polynomial in n, including reading the target.

## Orbit dispersion

In an accepted target the quantity (f_i·f_i)t_i, where Z_i*Z_i=t_i I, is independent of the choice of generator Z_i and invariant under orthogonal equivalence. Orthogonal transport preserves the block index i because the cross-product block dimensions are distinct. For the sampler this quantity is a_i², which equals 1 or 4 according to b_i. Hence all 2^m seeds index different orbits and every orbit has probability zero or 2^{-m}. The algorithm property holds against arbitrary nonsampled targets. The theorem concerns the sampler distribution. The uniform-source density analyzed in [1] is a separate quantity.

## Reference

1. *On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields*, [arXiv:2604.00591](https://arxiv.org/abs/2604.00591).
