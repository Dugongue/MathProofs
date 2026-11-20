import EvenP1ProbAverage

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (fiberFailureAverage uniformFraction_le_one)

noncomputable section

/-- Bad first-stage samples may contribute their whole mass. Every other
sample contributes at most its uniform second-stage bound. -/
theorem bad_fiber_average_le {X : Type*} [Fintype X] [Nonempty X]
    {Y : X → Type*} (bad : X → Prop) (F : ∀ x, Y x → Prop) (p : ℝ)
    (hp : 0 ≤ p) (h : ∀ x, ¬ bad x → uniformFraction (Y x) (F x) ≤ p)
    [∀ x, Fintype (Y x)] : fiberFailureAverage F ≤ uniformFraction X bad + p := by
  unfold fiberFailureAverage
  calc
    _ ≤ (∑ x : X, ((if bad x then 1 else 0) + p)) / (Fintype.card X : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : bad x
      · simp only [if_pos hx]
        exact (uniformFraction_le_one _).trans (le_add_of_nonneg_right hp)
      · simpa only [if_neg hx, zero_add] using h x hx
    _ = _ := by
      have hcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
      rw [Finset.sum_add_distrib, add_div, Finset.sum_boole, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard]
      unfold uniformFraction
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

#print axioms bad_fiber_average_le

end
end Mathproof.EvenTI.Reciprocal.Four