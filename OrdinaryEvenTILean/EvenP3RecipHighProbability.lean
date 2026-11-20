import EvenP1ProbKernel

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical
open Module LinearMap Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne

noncomputable section

variable {K V M A : Type*} [Field K] [Fintype K]
variable [AddCommGroup V] [Module K V] [Fintype V]
variable [AddCommGroup M] [Module K M] [Fintype M] [Fintype A]

theorem linear_zero_fraction (f : V →ₗ[K] M) :
    uniformFraction V (fun x => f x = 0) =
      1 / (Fintype.card K : ℝ)^finrank K f.range := by
  let e : V ≃ (Fin 1 → V) :=
    { toFun := fun x _ => x
      invFun := fun x => x 0
      left_inv := fun _ => rfl
      right_inv := fun x => funext (fun i => congrArg x (Subsingleton.elim 0 i)) }
  have h := uniformFraction_equiv e (fun x => ∀ i, f (x i) = 0)
  have he : (fun x => ∀ i, f (e x i) = 0) = (fun x => f x = 0) := by
    funext x
    exact propext ⟨fun h => h 0, fun h _ => h⟩
  rw [he, zero_tuple_fraction f 1, one_mul] at h
  exact h

/-- For a sampled vector family, it suffices to bound the rank of each
nonzero relation's evaluation map. -/
theorem dependence_fraction_le (F : V → A → M)
    (G : (A → K) → V →ₗ[K] M)
    (hG : ∀ c x, G c x = ∑ a, c a • F x a) (r : ℕ)
    (hRank : ∀ c, c ≠ 0 → r ≤ finrank K (G c).range) :
    uniformFraction V (fun x => ¬ LinearIndependent K (F x)) ≤
      (Fintype.card K : ℝ)^Fintype.card A / (Fintype.card K : ℝ)^r := by
  let L := {c : A → K // c ≠ 0}
  letI : Fintype L := Fintype.ofFinite _
  have himp (x : V) (hx : ¬ LinearIndependent K (F x)) :
      ∃ c : L, G c.val x = 0 := by
    by_contra hn
    apply hx
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have hc' : c = 0 := by
      by_contra hne
      exact hn ⟨⟨c,hne⟩, (hG c x).trans hc⟩
    rw [hc']
    rfl
  refine (uniformFraction_le_of_imp himp).trans ((uniformFraction_exists_le _).trans ?_)
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := K)))
  have hq' : (0 : ℝ) < Fintype.card K := by linarith
  have hCard : Fintype.card L ≤ Fintype.card K ^ Fintype.card A :=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans_eq (Fintype.card_fun)
  calc
    _ ≤ ∑ c : L, 1 / (Fintype.card K : ℝ)^r := by
      apply Finset.sum_le_sum
      intro c _
      rw [linear_zero_fraction]
      exact one_div_le_one_div_of_le (pow_pos hq' _) (pow_le_pow_right₀ hq (hRank c.val c.property))
    _ = (Fintype.card L : ℝ) / (Fintype.card K : ℝ)^r := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hCard

#print axioms linear_zero_fraction
#print axioms dependence_fraction_le

end
end Mathproof.EvenTI.Reciprocal.Four
