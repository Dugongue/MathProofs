# A guarded stabilizer correction between two-sign and special-linear TI

Work over the field of three elements. Write D for the sign profile of the relative tensor comparison, and write H for the sign image of its source stabilizer. When D is nonempty it is an affine coset a+H in V=F_2³. A sign bit zero means determinant +1. Define the following single raw-pair comparison C:

    accept if there exist d∈D and h∈H with d₂=0, d₁=h₃, h₁=0.

Thus the first of two tested signs may be corrected by one source automorphism, but only if that same automorphism is positive in the first mode. The guard is applied to the corrective automorphism, while the second determinant still belongs to the relative transporter.

There are deterministic polynomial many-one reductions

    two-sign TI ≤ C ≤ SL-TI.

Moreover C is exactly a conjunction of two specific correlated two-sign probes. One such probe, and even any finite disjunction of independently affine-preprocessed two-sign probes, cannot decide C in the profile-access model below. In the same model no affine disjunction of C probes decides SL-TI. These are limitations on the profile model, with no unrestricted complexity separation claimed.

## Construct the reductions on raw pairs

The exact sign projection and tagged direct-sum constructions realize fixed linear transformations and sums of profiles of independent copies. A self-comparison (T,T) has profile H. The SL-TI comparison for C uses one relative copy with sign projection d↦(d₁,d₂,0) and one independent self-comparison with projection h↦(h₃,0,h₁). Pack their sum in one raw pair. Its attainable sign tuple zero is exactly the stated predicate. An ordinary no case has empty relative profile and makes the packed pair ordinary-negative. Conversely project any input two-sign instance to the first two bits, clearing the third bit on all witnesses. Its stabilizer then has h₃=0, so the correction is ineffective and C gives precisely the original two-sign verdict. The unmodified choice h=0 always satisfies the guard. [Prior exact sign projections and tagged sums](https://github.com/Dugongue/MathProofs/blob/main/TensorSignProjections/SignProjections.md)

For the stronger positive access result, use the two tests

    Q₁: there are d∈D,h∈H with d₂=0 and d₁=h₃;
    Q₂: there are d∈D,h∈H with d₂=0 and d₁=h₃+h₁.

Each is an ordinary two-sign comparison after fixed projections and one tagged sum. Let D₀ be the elements of D with d₂=0. If D₀ is empty, all three comparisons fail. If D₀ contains an element with d₁=0, all three succeed by h=0. The remaining case is nonempty D₀ with d₁=1 on all its elements. Then Q₁ and Q₂ say that the two functionals h₃ and h₃+h₁ are both nonzero on H. This is equivalent to h₃ not belonging to the linear span of h₁ as functionals on H. Equivalently h₃ is nonzero on H∩ker(h₁), since the annihilator of that kernel inside H* is exactly the span of h₁, including when h₁=0. Such a witness is precisely the one needed by C. This proves C=Q₁ AND Q₂ without assuming that independent successful probes used the same witnesses. Testing the two probes in random order or with early stopping is optional, and their whole list is generated without knowing H.

## The affine-copy access model

The input consists of a hidden profile a+H. An allowed preprocessor takes a fixed number of independent copies of the relative and self profiles, applies fixed linear maps, and adds them, with an optional fixed affine slack space. In coordinates its result is

    M a + b + E + Σ_i L_i H,

where M,L_i are fixed linear maps, b is fixed, E is a fixed linear subspace, and the displayed direction includes MH. In an actual copy construction M is the sum of the maps on relative copies, which gives this inclusion. Allowing the direction to be any such sum including MH can only strengthen the negative statement. A branch applies a target verdict to this profile. A disjunction accepts when at least one of finitely many branches accepts. Each sound branch must therefore have acceptance contained in the source's acceptance. These statements concern that access model, where the matrices are fixed. They do not restrict general algorithms using the raw entries of a tensor pair.

All affine profiles invoked below occur on actual raw tensors. The diagonal two-dimensional tensor Δ₂ has full three-bit stabilizer image. Independent diagonal operations in two modes give the even-total plane, and the common transposition adds (1,1,1). Project the profile (Δ₂,Δ₂) onto any desired H by the exact sign compiler and reflect the target along the bits of a to translate by a. [Affine profile realization](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/ProfileQueries.md)

## No disjunction of affine-copy two-sign branches realizes C

Write P:V→F_2² for the projection to (d₁,d₂), and write p,q for the two standard basis vectors in F_2². If H=⟨v⟩ is a line, the allowed offsets for C are exactly the preimage under P of

    R(v) = ⟨Pv⟩ + span{p if v₁=0 and v₃=1}.

If H=0 its allowed offsets are precisely ker P=⟨e₃⟩. The positive profile with H=⟨e₃⟩ and offset a=e₁ must be accepted by at least one sound branch. We show no branch can do so.

Postcompose the branch with the two tested output coordinates. Quotient its fixed slack. Its tests now have the form M a+b in the span of the displayed L_i H, together with MH, in an output space of dimension at most two. Suppose first that the branch accepts at least one offset for H=0. Its accepted offsets form an affine subspace of size at least two, contained by soundness in ⟨e₃⟩. Hence they are exactly that line. The output has dimension two, there is no residual slack, M has rank two, b=0, and after changing output coordinates M=P. Since M is onto, on every H=⟨v⟩ each copy map must satisfy L_i v∈R(v), or the branch would accept a forbidden offset. The vectors e₁,e₂,e₃ respectively force

    L_i e₁=α_i p,    L_i e₂=β_i q,    L_i e₃=γ_i p.

At v=e₁+e₂ the allowed direction is ⟨p+q⟩, forcing α_i=β_i. At v=e₁+e₂+e₃ the allowed direction is again ⟨p+q⟩, forcing α_i+γ_i=β_i. Thus γ_i=0 for every copy. On H=⟨e₃⟩ the branch cannot accept a=e₁.

Suppose instead that the branch accepts no offset for H=0, so b is outside im M in the quotient output. To accept a=e₁ for H=⟨e₃⟩ without accepting any a with a₂=1, its kernel must lie in the plane a₂=0. Since b is outside im M, M has rank at most one. It therefore has rank one, its kernel is exactly that plane, and the output has dimension two. Change output coordinates so M a=a₂q and b=p. On H=⟨e₃⟩ acceptance of a=e₁ requires some copy map to have nonzero p-coordinate at e₃. However on each of H=⟨e₁+e₂⟩ and H=⟨e₁+e₂+e₃⟩, the direction already contains q from MH. Any copy map having a nonzero p-coordinate there gives the full output plane and makes the branch accept every offset. That is unsound since R(v) is only ⟨p+q⟩ on each of these lines. Thus every copy map has zero p-coordinate on both generators and hence on their sum e₃. This is the required contradiction.

Neither kind of sound branch covers the specified positive profile, ruling out even a finite disjunction. The argument also rules out a single affine branch as the special case of a one-term disjunction.

## Why the other endpoint stays distinct in this model

For SL-TI at H=0, exactly the offset a=0 is accepted. Any affine-copy preprocessing of these singleton profiles has a fixed resulting direction E and offset M a+b. The C verdict projects this offset to two coordinates. Its allowed-offset condition is membership in a fixed direction generated by the projection of E and the guarded corrections in E. The accepted offsets are therefore either empty or an affine subspace of dimension at least one in F_2³. Thus no sound branch can accept a=0. This proves the exclusion for a single branch and for every finite disjunction.

The new comparison differs from the earlier examples that allow unrestricted linear images of source stabilizer signs. It filters the sign tuple of one corrective witness before using it, while scoring a two-dimensional relative offset. It has an exact two-query positive algorithm and lies between the given endpoints under actual many-one reductions. The reverse exclusions above are only for affine-copy access, and do not establish a new unrestricted degree. All proofs are informal. [Earlier operator-space correction comparisons](https://github.com/Dugongue/MathProofs/blob/main/TensorDeterminantIntervals/Upper.md)

## The corresponding intermediate between one and two signs

On the same raw input define J_guard by

    accept if there exist d∈D and h∈H with d₁=h₃ and h₂=0.

In particular, the guard uses the second stabilizer bit and never tests a second relative sign. The lower reduction from one-sign TI clears the second and third signs. For the upper reduction, compile the two tested bits as (d₁+h₃,h₂) by exact projection and tagged summation of one relative and one self copy. This gives one two-sign instance. Equivalently make two one-sign probes with sign profiles d₁(D)+h₃(H) and d₁(D)+(h₃+h₂)(H), and accept if both accept. If the first relative sign can vanish, both accept using the zero correction. If the only relative first bit is 1, the two tests say h₃ and h₃+h₂ are both nonzero on H, exactly the condition that h₃ is nonzero on H∩ker h₂. An empty relative profile rejects in all formulations.

In the affine-copy model above, no disjunction of one-sign branches computes J_guard. It suffices to consider the true profile with H=⟨e₃⟩ and a=e₁. After fixed slack is quotiented out, a sound one-sign branch uses at most one output bit. A zero-dimensional branch is rejected as unsound because it would accept every rigid offset. If the offset readout M of a remaining branch is nonzero, soundness on H=0 forces M(a)=a₁ and b=0, since the allowed rigid offsets are precisely ker(a₁). If M=0, soundness forces b=1. In either case the offset equation fails at a=e₁ until the output direction is nonzero. The input lines H=⟨e₂⟩ and H=⟨e₂+e₃⟩ both forbid a=e₁, since the guard forces the corrective element to be zero on these lines and the relative x-bit is rigid. Thus every copy map L_i vanishes at e₂ and at e₂+e₃, hence at their sum e₃. The branch cannot accept the chosen true profile.

Conversely, a nonempty output profile produced by affine preprocessing of rigid input offsets has a direction fixed independently of the offsets. J_guard on that family imposes at most one linear offset equation. At H=0, two-sign TI accepts exactly the offsets a₁=a₂=0. A sound branch for that problem cannot accept any offset using at most one equation, since its affine acceptance set would have codimension at most one. The same proof applies to every earlier middle predicate that imposes both relative equations on rigid profiles, including a conjunction of two independent rigid one-sign instances. These exclusions again concern the stated access model. Both one-sided reductions for J_guard work on arbitrary raw pairs.
