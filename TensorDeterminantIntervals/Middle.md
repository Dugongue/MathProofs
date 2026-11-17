# Four determinant-correction problems between one and two signs

Work over F₃ on explicit dense three-tensors. Write O, A, B, S for ordinary, first-mode, first-two-mode and all-mode determinant-one TI. Write J for the conjunction of two independent A instances. For a raw comparison let D be its transporter sign profile in F₂³, with zero denoting determinant +1. If the profile is nonempty, write D=a+H, where H is the source stabilizer sign image and a can be any element of D. An empty D rejects in all four new problems. Where only two bits are used, D and H are first projected to those bits. None of the decision problems requires profiles, witnesses or subgroup generators as input.

| Problem | Acceptance rule for a nonempty profile |
| --- | --- |
| M | The projected two-bit profile contains zero or has nonzero direction. |
| T | If any stabilizer changes x or y, accept. Otherwise if some stabilizer changes z, require y=0. Otherwise require both x=y=0. |
| N | A first-positive relative transporter exists whose second sign can be corrected by an odd first-mode source automorphism. Explicitly require 0∈D+QH on the two-bit profile, with Q(x,y)=(0,x). A correction of zero is always allowed. |
| C | Independently require (some relative x=0 or some source stabilizer changes z) and (some relative y=0 or some source stabilizer changes x). |

Here x,y,z are the mode sign characters. In T the indicated signs are constant when tested. In C the two relative witnesses need not coincide. M can also be interpreted as allowing both cross-mode corrections, since 0∈D+QH+QᵗH exactly expresses its condition.

The following are deterministic polynomial-time many-one reductions on arbitrary raw inputs:

    O ≤ A ≤ M ≤ T ≤ N ≤ C ≤ J ≤ B ≤ S.

Only the arrows involving M,T,N,C are new here. The display gives nine ordered formulations. It keeps open whether adjoining them increases the number of distinct unrestricted many-one degrees.

## Exact reductions

Use the earlier MathProofs exact sign projection and tagged direct-sum assembly. For fixed binary linear maps they compile the profile L D + Σ L_i H into one actual relative tensor pair. Apply L to the relative pair and apply each L_i to its own independent self-comparison on the source. The direct sum gives the displayed Minkowski sum of profiles, preserves emptiness, and adds the actual determinant bits. This operation is polynomial for the constant number of summands here. All coordinates in the proof refer to the common physical sign coordinates of this assembly. If an output formula uses only two bits its third bit can be set identically zero.

A reduces to M by placing its single bit on one coordinate axis, with the other tested bit zero. A nonempty one-bit profile contains zero exactly when its singleton is zero or its direction is nonzero. M reduces to T by adjoining an identically zero third bit. T reduces to N by forming the two-bit profile

    D′ = {(y(d), x(d)) : d∈D} + e₁ x(H) + e₂ z(H).

If any h in H changes y, the first projection of D′ is flexible. If some h changes x, the first correction term also makes this projection flexible. In either case N accepts. To see this property of N, if its profile has a direction with first bit 1, QH contains e₂, and H+QH is the whole two-bit space. If x and y are rigid but z is flexible, D′ is a vertical affine line whose first bit is y, so N accepts exactly if y=0. If all three bits are rigid, N tests y=x=0.

N reduces to C by adjoining an identically zero third bit. If H changes x, both tests of C pass and N accepts. Otherwise x is constant, no correction QH occurs, and after requiring x=0 both definitions require that y can be zero. For C→J the first A query has sign set x(D)+z(H) and the second has y(D)+x(H). Use the same assembly to write these two queries in polynomial time. They check precisely the two clauses of C. The known J→B reduction puts the two independent live signs on two distinct axes.

## Twenty-five choices of stabilizer permissions

For each tested character x or y independently choose one of the five subspaces W containing it in the three-dimensional dual space. For x the explicit options are

    ⟨x⟩, ⟨x,y⟩, ⟨x,z⟩, ⟨x,y+z⟩, ⟨x,y,z⟩.

For y interchange x and y. For a pair (W_x,W_y), acceptance means that for each i=x,y, if all characters in W_i vanish on H, then i(a)=0. This gives 25 exact formulations. For each i, compute one A query with profile i(D)+Σ_{w∈basis W_i}w(H), which is a singleton only when i is rigid and every correction vanishes. Each formulation lies between A and J by that construction and the same rank-one embedding. J's earlier separate-witness presentation corresponds to the two singleton subspaces. M, T, N, C above correspond respectively to

    (⟨x,y⟩,⟨x,y⟩)
    (⟨x,y,z⟩,⟨x,y⟩)
    (⟨x⟩,⟨x,y⟩)
    (⟨x,z⟩,⟨x,y⟩).

The 25 predicates on actual raw sign profiles are pairwise different. If the choice in slot i differs, choose h in exactly one of the two annihilators in that slot, and an offset a with i(a)=1 and the other tested bit zero. The line a+⟨h⟩ distinguishes the two choices. Each annihilator is contained in the kernel of i, so i(h)=0 and the tested offset is constant on the line.

Some of the 25 reduce back to J directly. If x∉W_y and y∉W_x, choose vectors v∈W_y^⊥ with x(v)=1 and w∈W_x^⊥ with y(w)=1. Then y(v)=x(w)=0. Encode independent one-bit profiles on v,w. Flexibility of the first input cannot waive the second test, and flexibility of the second cannot waive the first. This recovers J exactly. These cases should be counted as alternate presentations of a known degree. The four displayed rungs differ by which stabilizer changes can repair a sign, including the case where third-mode flexibility repairs one sign but leaves the other live.

## Strictness for a stated compiler model

The following statement concerns only a single affine profile transformation, followed by the target predicate. The transformation takes independent relative and stabilizer witnesses, applies fixed affine-linear maps, and allows fixed independent affine slack. Thus on rigid nonempty inputs it produces La+b+K, with K a fixed linear subspace. With nonrigid inputs the output direction also contains Lh whenever one simultaneously changes all relative witnesses for that input by h and keeps the other witnesses fixed. The exact direction may be larger, depending on the extra independent witnesses. Its value depends on directions of the input profiles, independently of their offsets. This includes the direct sign projections and independent profile-sum compilations used above. It excludes reductions that use further structure of the original tensors. It also excludes several consecutive target probes.

All profiles used below occur on actual tensors. A zero cubic tensor with one-dimensional factors has full stabilizer sign image. Apply the exact sign projection with any prescribed image, then rebase the target by reflections to translate the affine offset. For several independent profiles perform this construction separately. The statements below give strictness of every reverse arrow from J back down through A in this specified one-shot model.

**M to A is impossible.** On rigid two-bit inputs, M accepts just 00. With fixed slack a one-bit equation either ignores both source bits or constrains a single character. So a branch accepting 00 accepts a nonzero point of its kernel. The argument permits disjunctions of finitely many affine branches.

**T to M is impossible.** Consider source profiles parallel to ⟨z⟩, on which T accepts precisely y=0, including the offset x=1,y=0. If the transformed two-bit direction is nonzero, M accepts every offset, including y=1. If it is zero, the output on x=1,y=0 agrees with the singleton at that offset, which T must reject. This also permits disjunctions.

**N to T is impossible.** On rigid two-bit inputs N accepts just 00. Any single affine branch accepting rigid 00 and avoiding the others must have invertible linear map on the projected tested target coordinates. Indeed on rigid inputs a fixed direction K leaves only some subset of the target's two equations, and excluding all three nonzero offsets requires two independent equations. This also rules out any nonzero fixed K for T. On the rejected source profile (1,0)+⟨(0,1)⟩, shifting all relative witnesses by (0,1) gives a direction with nonzero projection on the two tested target coordinates. T accepts every such profile, a contradiction. The argument permits disjunctions.

**C to N is impossible.** The rigid accepted set is exactly the z-axis. An affine transformation of these rigid inputs into N can enforce two independent rigid sign equations only if its fixed direction is zero and its linear part has rank two and kernel exactly the z-axis. Its offset must be zero to accept the origin. For profiles parallel to ⟨y⟩, C imposes exactly x=0. For profiles parallel to ⟨z⟩, C imposes exactly y=0. To implement a single equation on either direction, the output of N must have direction exactly the vertical line. A rigid output imposes two equations, and every other nonzero direction gives automatic acceptance. On the vertical line N always imposes the same first-coordinate equation, whose linear pullback cannot equal both x and y. This argument concerns one affine branch.

**J to C is impossible.** On a rigid product profile the accepted bit pair is only 00. A branch accepting it and avoiding the three negative singletons must leave both equations in C active, since any one equation accepts more than one rigid offset. In particular the fixed slack is zero, since the two correction subspaces of C together span the dual. The projected linear map of the rigid data onto the two tested coordinates must have rank two. Now hold one input rigid at 1 and let the other input be fully flexible. If the flexible direction changes the x-bit of the target, then both equations in C are automatically waived. The branch must reject both semirigid tests of this kind, once for each input varied. This forces the x-component of both columns of the projected linear map to vanish, contradicting rank two. The argument permits disjunctions.

**The middle catalogue has nine J presentations and sixteen candidates below J in the compiler model.** The two conditions x∉W_y and y∉W_x hold for three choices per slot, so there are nine exact J degrees by the embedding above. If x∈W_y then a direction changing x waives both target tests. To reject each product profile with one flexible input and the other rigid at 1, a branch accepting rigid 00 must send both source axes to directions with zero x component. This contradicts the rank two forced by the rigid tests. The same argument with y applies if y∈W_x.

**B to J is impossible in this model.** On rigid inputs, J would need two independent readouts ℓ₁ and ℓ₂ to accept just the zero offset, with zero auxiliary slack in both output readouts. On an affine input line opposite to zero with direction ker(ℓ₁+ℓ₂), varying the relative witness together in each readout flips both bits. Both one-bit profiles then contain zero, even though B rejects. This also rules out a disjunction since every branch accepting the rigid zero produces such a false positive.

**S to B is impossible in this model.** On rigid three-bit offsets, any affine branch with two output sign equations which accepts zero accepts a nonzero vector in their common linear kernel. Likewise A to O is impossible in this model because the affine transformation preserves nonemptiness, even on rigid negative singleton profiles.
The reverse failures above are statements about the specified affine compiler model. They do not establish inequality of the unrestricted polynomial many-one degrees of the new problems. The upper and lower reductions in the main chain are unrestricted. The motivating ordinary versus SL inclusion is [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
