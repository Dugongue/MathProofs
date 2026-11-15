# Linear-length reductions for the five unitary tensor actions

Informal proof, November 14, 2026. The construction works uniformly over every finite field with its quadratic involution, including characteristic two. It also gives one proof for the real orthogonal and complex unitary cases. No publication priority is asserted.

Chen, Grochow, Qiao, Tang and Zhang ask in §1.5 of [Part III, arXiv:2306.03135v2](https://arxiv.org/html/2306.03135v2#S1.SS5) for linear-length reductions between the five actions for classical group families. Their Definition 1.2 specifies the actions. Their Theorem 1.6 establishes polynomial-time equivalence for real orthogonal and complex unitary groups. This proof gives the linear bound for those families and for the standard finite-field unitary family. It addresses the size of reductions between actions of the same family.

## Theorem

Let F be a field with an involution x ↦ x̄, which may be trivial, and let G(n) be the isometry group of the standard form h(x,y) = x̄ᵀy on Fⁿ. For any ordered pair of the five actions

1. (P, Q, R),
2. (P, P, Q),
3. (P, P⁻ᵀ, Q),
4. (P, P, P⁻ᵀ),
5. (P, P, P),

there is a polynomial-time many-one reduction from isomorphism under the first action in the pair to isomorphism under the second. For input side lengths n₁, n₂, n₃, each output side length is at most C(n₁ + n₂ + n₃), for an absolute C. In fixed standard coordinates, output entries are input entries or the constants 0 and 1. In particular, the construction is uniform over finite-field presentations and carries no cost in the characteristic beyond copying the represented coefficients.

The proof has three stages. The first encodes repeated and inverse-transpose occurrences using independent actions on labelled coordinate parts. The second removes all labels. The third uses the full mode supports produced by that removal to combine independent actions into any target sharing pattern.

Throughout, coordinate decompositions are orthogonal direct sums of standard-form spaces, so every coordinate subspace is nondegenerate, even in characteristic two. Direct sums of isometries are isometries, and restrictions of isometries to invariant coordinate subspaces are isometries for the restricted form. For g ∈ G(n), the equality g⁻ᵀ = ḡ also shows that g⁻ᵀ ∈ G(n).

## 1. Convert shared actions to independent actions on prescribed blocks

For every source matrix variable P of size n, create two coordinate blocks Pⱼ⁺ and Pⱼ⁻ of dimension n in each mode j ∈ {1,2,3}. Each mode also has a single common anchor line with basis vector zⱼ. A partitioned transporter acts by an independent standard-form isometry on each whole block and each anchor line. Embed the input tensor in the product of its chosen occurrence blocks, using the plus block for a direct action and the minus block for an inverse-transpose action.

Add the tensor z₁ ⊗ z₂ ⊗ z₃. For every variable P and every ordered pair i ≠ j of modes, add the identity tensor Σₐ eₐ ⊗ eₐ on Pᵢ⁺ and Pⱼ⁻, multiplied by zₖ in the remaining mode k. Put each term in its designated mode order. These fixed couplings, the anchor product, and the input tensor occupy distinct block triples.

Let tⱼ be the scalar on zⱼ in a partitioned transporter. The anchor product enforces t₁t₂t₃ = 1. Each tⱼ has form norm one. In mode j divide the action on each occurrence block by tⱼ. Call the resulting isometries Hⱼ⁺, Hⱼ⁻ for the variable P. Preservation of the coupling for (i,j) gives

    tₖ · (tᵢ Hᵢ⁺) · (tⱼ Hⱼ⁻)ᵀ = I,

which is precisely Hᵢ⁺(Hⱼ⁻)ᵀ = I. The coupling graph has six vertices, the three plus and three minus copies, with an edge across distinct modes. It is a connected six-cycle. Thus all normalized plus actions agree on one isometry P, and all normalized minus actions agree on P⁻ᵀ. The three factors of tⱼ on the data block multiply to one. This recovers exactly the source action. Conversely, any source transporter extends over the system using P on every plus copy, P⁻ᵀ on every minus copy, and 1 on each anchor line.

All mode dimensions are at most 2(n₁ + n₂ + n₃) + 1. Each mode has at most seven parts.

## 2. Remove one prescribed partition by ranks and supports

Suppose the current modes are U, V, W, with partitions into coordinate subspaces. Write the partition to be removed as U = ⊕ᵢ Uᵢ, with k parts, put s = dim U, and add m = 2k new marker slices, two for each part. Number these by j ∈ {1,…,m}, and let i(j) be the part for marker j. Set

    Rⱼ = (s+1)(m+j).

Add a private row block Pⱼ of dimension Rⱼ to U, a private column copy Cⱼ of Uᵢ₍ⱼ₎ and a private column block Dⱼ of dimension Rⱼ to V, and a tag line with basis zⱼ to W. All such added blocks are disjoint coordinate subspaces. On slice zⱼ place a matrix Mⱼ with identity blocks between Uᵢ₍ⱼ₎ and Cⱼ and between Pⱼ and Dⱼ, and zeros elsewhere. The original tensor occupies the original U, V, W. In the new problem there is no partition in the enlarged U. Enlarge the first part of each of the maintained V and W partitions by the auxiliary coordinates added to that mode, leaving the other parts alone.

**Recover the old third mode.** A third-mode covector annihilating the tag span contracts to an original slice combination of rank at most s. For any covector with nonzero tag coefficient aⱼ, the contraction contains the isolated Rⱼ × Rⱼ submatrix aⱼI on Pⱼ × Dⱼ, so its rank exceeds s. Thus the low-rank covectors are exactly the annihilator of the tag span. If an isometry triple carries one augmented tensor to the other, contraction ranks are preserved under the induced third-mode action on covectors. The triple therefore preserves the tag span in the third mode and, by preservation of the form, its orthogonal complement, the old W.

**Recover the individual tag lines.** Now restrict to covectors supported on the tag coordinates, an invariant summand of the dual. A nonzero contraction with tag coefficient support J has rank between the sum of Rⱼ over j ∈ J and that sum plus s. Indeed the private submatrix on the Pⱼ × Dⱼ blocks has rank equal to that sum, and the remaining contribution has rows in U. The singleton bands [Rⱼ, Rⱼ + s] are disjoint because their starting points are separated by s+1. Every combination supported on two or more tags has rank at least (2m+3)(s+1), greater than Rₘ + s. Consequently each tag dual line is recognized by its rank band. The primal tag lines are preserved as well.

**Recover the data blocks.** With the tags recognized, a transporter must preserve the column and row supports of each Mⱼ. The two marker column supports for Uᵢ intersect in Uᵢ, since they use private row blocks. The sum of all marker row supports is exactly the whole added column space, whose orthogonal complement is the old V. Thus each old Uᵢ and the old V and W are invariant, and the restricted maps preserve the original partitions on V and W. Restrict the augmented tensor equation to the data coordinates. The fixed marker tensors still lie in the tag summand, so the equation on the old spaces gives an isomorphism of the original partitioned objects.

**Lift any source transporter.** Use the original isometries on U, V, W, the inverse transpose of its Uᵢ₍ⱼ₎-matrix on Cⱼ, and the identity on Pⱼ, Dⱼ, zⱼ. These choices preserve every marker and the two maintained partitions. Thus this is a reduction in both directions of the isomorphism predicate, even for zero data.

**Coverage of all auxiliary coordinates.** Let the mode support of a tensor be the span of its contractions by covectors in the other two modes. The enlarged U has full support because the column supports of the markers cover it. Every old mode support embeds in the new support by contracting in the two old coordinate spaces in the other modes: every marker has auxiliary coordinates in at least one contracted mode. All auxiliary coordinates in V belong to its new support because the marker row supports cover the added column space. The auxiliary tag coordinates in W belong to its new support by contracting in matched private Pⱼ and Dⱼ coordinates. So a previously full mode stays full, and the newly unpartitioned mode becomes full.

Apply this construction in mode 1, then mode 2, then mode 3, treating an already unpartitioned mode as one part to be enlarged. The construction keeps the partition counts in the two maintained modes unchanged at each step. The result is an unpartitioned independent-action tensor with full support in each mode, often called concise. Each step adds O(k²(s+1)) coordinates in total, with k at most seven here. Indeed Σⱼ Rⱼ is O(m²(s+1)), the Cⱼ add 2s coordinates, and there are m tag lines. Hence the total side length after the three steps is linear in the original one. The same removal also applies when the number of parts grows, with polynomial dependence on the three part counts.

This construction uses the rank-marker idea of [Grochow–Qiao Part IV, §5](https://arxiv.org/html/2306.16317#S5). The use of orthogonal complements and two private supports per block replaces row and column cancellations. Those cancellations need not preserve the form and were a stated difficulty in Part III.

## 3. Convert independent actions to the requested shared action

Suppose the two concise arrays from stage 2 have three spaces E₁, E₂, E₃. For each target group variable, form the orthogonal direct sum of the Eⱼ on which that variable is meant to act, whether directly or by inverse transpose. For each mode embed the data in the corresponding constituent of this orthogonal direct sum, with zeros elsewhere. Thus each output side length is at most dim E₁ + dim E₂ + dim E₃.

For any independent transporter (g₁,g₂,g₃), use a block-diagonal matrix for a shared target variable, with block gⱼ for each direct occurrence and gⱼ⁻ᵀ for each inverse-transpose occurrence. This is an isometry and has precisely the required action on each data block. Conversely, full mode support means that, in each padded mode, its data constituent is the intrinsic mode support. A target transporter must carry this support onto itself. Its direct or inverse-transpose action there restricts to an isometry gⱼ, and the tensor equation on those supports gives the independent source transporter. This argument uses the coordinate standard forms on the whole data constituents, without requiring a unitary extension from an arbitrary subspace.

With positive side lengths, their sum is bounded by three times the number of dense input entries, and writing the output array therefore takes polynomial time. If a matching source format has an empty mode, the pair is always a YES instance and may be sent to a fixed one-dimensional YES pair. A pair of different input formats, if the decision format permits it, can be sent to a fixed NO pair. Each construction adds only fixed identity entries and zeros or copies coordinates of the input tensor. This completes the claimed reductions.
