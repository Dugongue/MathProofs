import PrimaryTailPeel

namespace Mathproof.Problem17PrimaryTail
open Module LinearMap Polynomial
noncomputable section

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The preimage of an invariant quotient subspace combines the two restriction polynomials. -/
theorem lift_quotient_restriction (T : End K V) (S : Submodule K V) (hS : Preserves T S)
    (U : Submodule K (V ⧸ S)) (hU : Preserves (quotientBlock T S hS) U) :
    ∃ W : Submodule K V, ∃ hW : Preserves T W,
      (T.restrict hW).charpoly =
        (T.restrict hS).charpoly * ((quotientBlock T S hS).restrict hU).charpoly := by
  let W := U.comap S.mkQ
  let D := quotientBlock T S hS
  have hD (x : V) : D (S.mkQ x) = S.mkQ (T x) :=
    LinearMap.congr_fun (Submodule.mapQ_mkQ S S T (h := hS)) x
  have hW : Preserves T W := by
    intro x hx
    change S.mkQ (T x) ∈ U
    rw [← hD]
    exact hU _ hx
  let A := T.restrict hW
  let F := D.restrict hU
  let q : W →ₗ[K] U := (S.mkQ.comp W.subtype).codRestrict U fun x => x.property
  have hq : Function.Surjective q := by
    intro u
    obtain ⟨x, hx⟩ := S.mkQ_surjective u.val
    have hw : x ∈ W := show S.mkQ x ∈ U by rw [hx]; exact u.property
    exact ⟨⟨x, hw⟩, Subtype.ext hx⟩
  have hSq : S ≤ W := by
    intro x hx
    change S.mkQ x ∈ U
    have he : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
    rw [he]
    exact U.zero_mem
  let i : S →ₗ[K] W := Submodule.inclusion hSq
  let N := q.ker
  have hi : Function.Injective i := fun x y h =>
    Subtype.ext (congrArg (fun w : W => w.val) h)
  have hN : i.range = N := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero S).mpr s.property
    · intro hx
      have he : q x = 0 := hx
      have hs : x.val ∈ S :=
        (Submodule.Quotient.mk_eq_zero S).mp (congrArg (fun u : U => u.val) he)
      exact ⟨⟨x.val, hs⟩, Subtype.ext rfl⟩
  have hInter (x : W) : q (A x) = F (q x) :=
    Subtype.ext (hD x.val).symm
  have hAN : Preserves A N := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    rw [hInter, show q x = 0 from hx, map_zero]
  let e : S ≃ₗ[K] N := (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hN)
  let j : (W ⧸ N) ≃ₗ[K] U := q.quotKerEquivOfSurjective hq
  have he : e.conj (T.restrict hS) = A.restrict hAN := by
    apply LinearMap.ext
    intro x
    obtain ⟨s, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hj (x : W) : j (N.mkQ x) = q x := rfl
  have hf : j.conj (quotientBlock A N hAN) = F := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    rw [← hj x, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    have ha : quotientBlock A N hAN (N.mkQ x) = N.mkQ (A x) :=
      LinearMap.congr_fun (Submodule.mapQ_mkQ N N A (h := hAN)) x
    rw [ha, hj, hj, hInter]
  refine ⟨W, hW, ?_⟩
  change A.charpoly = (T.restrict hS).charpoly * F.charpoly
  rw [invariant_charpoly_split A N hAN, ← he, ← hf, LinearEquiv.charpoly_conj,
    LinearEquiv.charpoly_conj]

variable [Fintype K]

/-- Two irreducible blocks can be peeled together while retaining all remaining powers. -/
theorem exists_peel_two (T : End K V) (f : K[X]) (hf : f.Monic) (hi : Irreducible f)
    (k : ℕ) (hk : f ^ (k+2) ∣ T.charpoly) :
    ∃ W : Submodule K V, ∃ hW : Preserves T W, finrank K W = f.natDegree * 2 ∧
      (T.restrict hW).charpoly = f^2 ∧ f^k ∣ (quotientBlock T W hW).charpoly := by
  obtain ⟨S, hS, _, hA, hQ⟩ := exists_peel T f hf hi (k+1) hk
  obtain ⟨U, hU, _, hB, _⟩ := exists_peel (quotientBlock T S hS) f hf hi k hQ
  obtain ⟨W, hW, hp⟩ := lift_quotient_restriction T S hS U hU
  rw [hA, hB, ← pow_two] at hp
  refine ⟨W, hW, ?_, hp, ?_⟩
  · rw [← (T.restrict hW).charpoly_natDegree, hp, Polynomial.natDegree_pow, Nat.mul_comm]
  · rw [invariant_charpoly_split T W hW, hp, pow_add, mul_comm (f^k)] at hk
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hi.ne_zero)).mp hk

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.exists_peel_two
