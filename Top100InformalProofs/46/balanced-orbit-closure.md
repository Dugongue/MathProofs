# Orbit-closure equivalence for balanced single-group tensor actions

This is the balanced-action classification in the stated reduction model.

## The question

Lysikov–Walter, arXiv:2411.04639 (FOCS 2025), after Theorem I.2:
> "There are three remaining cases… namely, OCI(V^{⊗2}⊗(V*)^{⊗2}; GL(V)), OCI(V^{⊗3}⊗(V*)^{⊗3}; GL(V)), and OCI(V^{⊗2}⊗(V*)^{⊗2} ⊕ V⊗V*; GL(V)). We conjecture that these are also TOCI-complete."

> **Question I.12.** Are [these] complete for TOCI? More generally, is any OCI problem for tensor tuple sequences either TOCI-complete, or efficiently solvable?

## Main theorem

**OCI(V^{⊗2}⊗V*^{⊗2}; GL(V)) is TOCI-complete.**

**Corollaries.**
- **All three cases.** By their Lemma V.16 (monotonicity), the other two cases are TOCI-complete as well, which settles their conjecture.
- **Dichotomy for single-GL balanced sequences.** A sequence (⊕_k V^{⊗a_k}⊗V*^{⊗a_k}; GL(V)) is
  - **TOCI-complete if some a_k ≥ 2**, and
  - **efficiently solvable otherwise**: all a_k ≤ 1 means simultaneous conjugation of matrix tuples, which is quiver-tame, as Lysikov–Walter note.

  This answers the "more generally" part of Question I.12 for this family, and it sharpens their Corollary V.17 (Σ a_k ≥ 4) to the optimal condition.

## Proof

**Step 0: a splitting of the target.** Let W be a vector space and identify W^{⊗2}⊗W*^{⊗2} = End(W)⊗End(W) = End(W⊗W), with GL(W) acting by conjugation. Since End(W) = sl(W) ⊕ ℂ·1,

  End(W)⊗End(W) = (End(W)⊗1) ⊕ C,  C := sl⊗sl ⊕ 1⊗sl,

with both summands GL(W)-stable. The equivariant projection onto the first is P(T) = (1/dim W)·Tr₂(T) ⊗ 1.

**Step 1: the marker.** Take W = X ⊕ Y and M = 1_X ⊕ 2·1_Y. Then:
- M is semisimple, so its conjugation orbit, and hence the orbit of M⊗1 in End(W)⊗1 ≅ End(W), is **closed**;
- Stab(M⊗1) = GL(X) × GL(Y) =: K, which is **reductive**;
- [checked] the stabiliser has dimension n_X² + n_Y².

**Step 2: the data.** The blocks Hom(X⊗Y, X⊗Y), Hom(X⊗Y, Y⊗X) and Hom(Y⊗X, X⊗Y) of End(W⊗W) are three distinct K-stable direct summands. Each is K-isomorphic to X⊗X*⊗Y⊗Y*. Let

  ι : (X⊗X*⊗Y⊗Y*)^{⊕3} → End(W⊗W)

place the three copies in these blocks. It is injective and K-equivariant, and so is π_C∘ι:
- **Why π_C∘ι is injective.** ker π_C = End(W)⊗1, and A⊗1_W meets the span of the three blocks only in 0. The second factor of A⊗1_X sends X to X, and of A⊗1_Y sends Y to Y, while every chosen block changes the second factor or sits in X⊗Y → X⊗Y with different first-factor support.
- [checked: rank 3(n_X n_Y)² for (n_X, n_Y) ∈ {(1,1), (1,2), (2,1), (2,2), (2,3)}]

**Step 3: the reduction.** Send (t₁, t₂, t₃) ↦ T := M⊗1 + π_C(ι(t₁, t₂, t₃)) ∈ End(W⊗W). This is affine-linear, of polynomial size, and an efficient algebraic reduction in Lysikov–Walter's sense.

**Step 4: correctness via the associated-bundle principle.**
1. **The principle.** Let H be reductive acting on M′ ⊕ Z, where M′ and Z are H-representations. Let m ∈ M′ have closed orbit and reductive stabiliser K. Then for z, z′ ∈ Z:

   cl(H·(m, z)) ∩ cl(H·(m, z′)) ≠ ∅ ⟺ cl(K·z) ∩ cl(K·z′) ≠ ∅.

   *Proof.*
   - H·m × Z is a closed H-stable subvariety, and since Z is an H-representation it is ≅ H ×_K Z ≅ H/K × Z.
   - Its H-invariants restrict isomorphically to the K-invariants of Z: F ↦ F(eK, ·), with inverse f ↦ ((hK, w) ↦ f(h⁻¹w)).
   - For reductive groups on affine varieties, closure equivalence is equality of invariants, and invariants restrict surjectively to closed invariant subvarieties. ∎
2. **Apply it** with H = GL(W), M′ = End(W)⊗1, Z = C and m = M⊗1. GL(W)-closure equivalence of T and T′ becomes K-closure equivalence of π_C ι(t) and π_C ι(t′).
3. **Then** injectivity and K-equivariance of π_C∘ι (their Corollary III.8 principle) turn this into K-closure equivalence of t and t′.
4. **Finally**, K = GL(X) × GL(Y) acting on (X⊗X*⊗Y⊗Y*)^{⊕3} is TOCI-complete by Lysikov–Walter Theorem V.11 (PEPS gauge equivalence, physical dimension 3).

Membership in TOCI holds by definition. ∎
