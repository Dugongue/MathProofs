# How the four determinant tiers are linked

Work over the field of three elements and let P_i denote comparison of raw 3-tensors requiring determinant one in the first i modes, for i=0,1,2,3. Thus P_0 is ordinary TI and P_3 is SL-TI. The forward polynomial many-one arrows follow from adding an unused coordinate in a mode whose sign is not yet tested. The coordinate adds a free determinant correction and ordinary equivalence on the extended tensors still recovers the old transporters on the original supports. Where the old input already has an unused direction in an old tested mode, that same correction was already available. The previous sign projectors also supply the forward arrows while recovering exact sign sets.

**New consequence for the middle gap.** If there is a deterministic polynomial-time kernel reduction from P_2 to P_1, then all four tiers are polynomial-time many-one equivalent. Thus a proof applying one and the same object map to both endpoints of the middle gap would simultaneously settle all three decision gaps at the many-one level. The earlier five-object theorem gives the corresponding implication for a kernel reduction from P_3 to P_2.

## Three objects suffice for the middle gap

A kernel reduction applies a single polynomial-time function f to an object separately. The hypothesis is

    P_2(X,Y) iff P_1(f(X),f(Y)).

By the axis packing already proved in the earlier sign work, use a format-wise object map C(x,y) into the two-sign tier with

    P_2(C(x,y),C(x',y')) iff P_1(x,x') and P_1(y,y').

For completeness, the use of this object map in the present argument has only one variable format at a time. In a one-sign input pair with mismatched tested support dimensions reject. When the tested support has an unused complement, or the tested dimension is odd, the one-sign answer equals ordinary TI by an independent complement reflection or scalar correction. Compile this branch directly. Otherwise the even tested mode is full. For each individual tensor independently, pad the two free modes to odd dimension with a nonzero unused complement in each. Castling with a calibrated annihilator basis makes all three sides odd and converts the old tested determinant into the total sign. The presence of the full unused strips gives conciseness in both new dual free modes, and the new label space embeds into their tensor product. The earlier local-algebra construction stores that total sign in one selected mode with the other two signs neutral. Its scalar-residue local centroid makes the block intrinsically indecomposable. The two axis formats are chosen by the fixed input format and slot, so their direct-sum factors cannot be exchanged. This supplies C for the branch being used, with no pair-dependent choices in C. [Castling and axis packing](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/CastlingAndConjunction.md) · [Prior five-object argument](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

Apply f to the three objects

    C(x,x), C(x,y), C(y,x).

If P_1(x,y) holds, the three images are P_1-equivalent, hence ordinarily equivalent. If it fails, the three products are pairwise P_2-inequivalent by the exact conjunctive product property, so their images are pairwise P_1-inequivalent. An ordinary orbit contains at most two P_1-orbits because the tested determinant kernel has index at most two in the ordinary acting group. Therefore the three images cannot all be ordinarily equivalent. Two ordinary comparisons against a common reference decide P_1. Package both as one TI pair using ordinary conjunction. Every construction has polynomial size. Once P_1 reduces to P_0, the earlier seven-character decomposition and ordinary conjunction also reduce P_3 to P_0. This proves the claim. [Ordinary conjunction](https://github.com/Dugongue/MathProofs/blob/main/OneSignTensorComparison/Disjunction.md) · [Kernel reduction terminology](https://arxiv.org/abs/0907.4775)

The same argument works when any P_k with k>j is reduced objectwise to P_j, assuming the k tested axes are available in the existing packing, so k≤3 here. Choose 2^j+1 distinct length-k binary words and substitute x,y in the slots. Map the k-tuples to one P_k object each and then apply the given objectwise reduction. A positive input gives one ordinary class. A negative input gives more pairwise P_j-inequivalent images than can fit inside an ordinary orbit. For k=3,j=2 this is the earlier five-object argument. The conclusion is a reduction of a pair to one ordinary comparison. It need not yield an objectwise reduction to P_0.

## Decision closure and its precise current boundary

The three signed tiers already have the same polynomial-time Turing closure, even using a constant number of nonadaptive comparisons. P_2 uses three P_1 comparisons, P_3 uses three P_2 comparisons, and P_3 also uses seven P_1 comparisons directly. The companion profile theorem shows these counts are optimal for deterministic affine sign probes, even with adaptivity. This optimality theorem concerns projections of the sign profile and does not bound arbitrary algebraic reductions.

The conditional implications above are stronger than saying that two successive improvements would eventually compose. A kernel construction for just one of the upper adjacent gaps forces the ordinary many-one collapse. A merely pair-dependent reduction between those gaps is outside the argument. None of the new results proves or disproves an unrestricted reverse many-one arrow. The exact-lift theorem in this packet separates the corresponding faithful augmentation models, while the retained-sign compiler gives direct collapse on the stated raw families. This is informal mathematics. Priority for the new middle-gap implication has not been established. [Open Question 1.9 and reduction convention](https://arxiv.org/html/2306.03135v2#S1)
