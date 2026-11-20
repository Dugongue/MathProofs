import EvenP1ProbKernel
import EvenP1LawMass

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical
open Mathproof.EvenOrdinaryTISingular (uniformFraction uniformFraction_equiv)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_exists_le uniformFraction_le_one)
open Mathproof.EvenTI.Reciprocal.Sampling (uniformFraction_sigma)

noncomputable section

/-- A simultaneous estimate from one uniform per-label bound. -/
theorem uniformFraction_union_const {V A : Type*} [Fintype V] [Fintype A]
    (P : A → V → Prop) (p : ℝ) (h : ∀ a, uniformFraction V (P a) ≤ p) :
    uniformFraction V (fun v => ∃ a, P a v) ≤ (Fintype.card A : ℝ) * p := by
  refine (uniformFraction_exists_le P).trans ?_
  calc
    _ ≤ ∑ _ : A, p := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [nsmul_eq_mul]

/-- After exposing the columns, the bad-column mass and the uniform bound
on each good-column row fiber simply add. -/
theorem exposed_rows_bound {C R : Type*} [Fintype C] [Fintype R] [Nonempty C] [Nonempty R]
    (bad : C → Prop) (fail : C → R → Prop) (p : ℝ) (hp : 0 ≤ p)
    (h : ∀ c, ¬ bad c → uniformFraction R (fail c) ≤ p) :
    uniformFraction (C × R) (fun z => fail z.1 z.2) ≤ uniformFraction C bad + p := by
  let e := Equiv.sigmaEquivProd C R
  letI : Nonempty (Σ _ : C, R) := ⟨⟨Classical.choice ‹Nonempty C›, Classical.choice ‹Nonempty R›⟩⟩
  rw [← uniformFraction_equiv e, uniformFraction_sigma (fun _ _ => rfl)]
  change (∑ c : C, uniformFraction R (fail c)) / (Fintype.card C : ℝ) ≤ _
  have hC : (Fintype.card C : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (∑ c : C, ((if bad c then 1 else 0) + p)) / Fintype.card C := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : bad c
      · simp only [if_pos hc]
        exact (uniformFraction_le_one _).trans (le_add_of_nonneg_right hp)
      · simpa only [if_neg hc, zero_add] using h c hc
    _ = _ := by
      rw [Finset.sum_add_distrib, add_div, Finset.sum_boole, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hC]
      unfold uniformFraction
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

#print axioms uniformFraction_union_const
#print axioms exposed_rows_bound

end
end Mathproof.EvenTI.Reciprocal.Four