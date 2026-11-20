import EvenP3SingularCoverage
import EvenP3RecipPrimary

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Matrix Classical
open Matrix EvenTI.Action EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Coverage
open Mathproof.EvenTI.Reciprocal.Coverage Mathproof.Problem17PrimaryTail

noncomputable section

private theorem fraction_subtype_to_raw_le {A : Type*} [Finite A]
    (R : A → Prop) (P : {a : A // R a} → Prop) :
    uniformFraction A (fun a => ∃ h : R a, P ⟨a,h⟩) ≤ uniformFraction {a : A // R a} P := by
  let e : {a : A // ∃ h : R a, P ⟨a,h⟩} ≃ {x : {a : A // R a} // P x} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact ⟨⟨x.val, Classical.choose x.property⟩, Classical.choose_spec x.property⟩
    · intro x
      exact ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
    · intro _
      exact Subtype.ext rfl
    · intro _
      exact Subtype.ext (Subtype.ext rfl)
  unfold uniformFraction
  rw [Nat.card_congr e]
  by_cases he : IsEmpty {a : A // R a}
  · letI : IsEmpty {x : {a : A // R a} // P x} := ⟨fun x => he.false x.val⟩
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div, le_rfl]
  · letI : Nonempty {a : A // R a} := not_isEmpty_iff.mp he
    have h : Nat.card {a : A // R a} ≤ Nat.card A :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    apply div_le_div_of_nonneg_left (by positivity) _ (by exact_mod_cast h)
    exact_mod_cast Nat.card_pos (α := {a : A // R a})

private theorem event_or_le {A : Type*} [Fintype A] (p q : A → Prop) :
    event (fun x => p x ∨ q x) ≤ event p + event q := by
  unfold event mean
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [hp,hq])) (by positivity)

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

def orderFourShapeAccepted (hn : 5 ≤ n) (T : Four K n) : Prop :=
  ((flatten T).det = 0 ∧ singularOrderFourAccepted T) ∨
    ∃ h : IsUnit (flatten T), Fintype.card K ^ squareReciprocalBudget hn ⟨T, h⟩ ≤ n

private def singularFailure (T : Four K n) : Prop :=
  (flatten T).det = 0 ∧ ¬ singularOrderFourAccepted T

private def reciprocalFailure (hn : 5 ≤ n) (T : InvertibleCut K 2 n) : Prop :=
  n < Fintype.card K ^ squareReciprocalBudget hn T

private def reciprocalFailureRaw (hn : 5 ≤ n) (T : Four K n) : Prop :=
  ∃ h : IsUnit (flatten T), reciprocalFailure hn ⟨T,h⟩

private theorem orderFourFailure_implies (hn : 5 ≤ n) (T : Four K n)
    (h : ¬ orderFourShapeAccepted hn T) : singularFailure T ∨ reciprocalFailureRaw hn T := by
  by_cases hz : (flatten T).det = 0
  · exact Or.inl ⟨hz, fun hS => h (Or.inl ⟨hz,hS⟩)⟩
  · have hu : IsUnit (flatten T) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hz)
    exact Or.inr ⟨hu, lt_of_not_ge (fun hS => h (Or.inr ⟨hu,hS⟩))⟩

private theorem orderFour_failure_union (hn : 5 ≤ n) :
    event (fun T : Four K n => ¬ orderFourShapeAccepted hn T) ≤
      event (singularFailure : Four K n → Prop) + event (reciprocalFailureRaw (K := K) hn) := by
  refine le_trans ?_ (event_or_le (singularFailure : Four K n → Prop) (reciprocalFailureRaw hn))
  apply mean_mono
  intro T
  by_cases h : ¬ orderFourShapeAccepted hn T
  · rw [if_pos h, if_pos (orderFourFailure_implies hn T h)]
  · rw [if_neg h]
    split <;> norm_num

private theorem reciprocal_failure_to_raw (hn : 5 ≤ n) :
    event (reciprocalFailureRaw hn : Four K n → Prop) ≤ event (reciprocalFailure (K := K) hn) := by
  rw [event_as_fraction, event_as_fraction]
  exact fraction_subtype_to_raw_le (fun T : Four K n => IsUnit (flatten (l := 2) (r := 2) T))
    (reciprocalFailure (K := K) hn)

/-- Both rank sectors of the same specified raw order-four cut pass
their actual spectral gates outside the sum of the explicit bounds. -/
theorem orderFour_shape_coverage (hn : 10^19 ≤ n) :
    event (fun T : Four K n => ¬ orderFourShapeAccepted (by omega) T) ≤
      (2 / (n : ℝ) + 8 / (↑(n/2) : ℝ)^2 +
        2 * (8 * (budgetConstant K + 1) + 34) * Real.log (Fintype.card K) / Real.log n) +
      4 * (budgetConstant K + (↑(n^2) : ℝ) * squareReciprocalError K n) *
        Real.log (Fintype.card K) / Real.log n := by
  let h5 : 5 ≤ n := (by decide : 5 ≤ 10^19).trans hn
  refine (orderFour_failure_union (K := K) h5).trans (add_le_add ?_ ?_)
  · exact orderFour_singular_coverage (K := K) (n := n) ((by decide : 1024 ≤ 10^19).trans hn)
  · exact (reciprocal_failure_to_raw (K := K) h5).trans (orderFour_reciprocal_gate (K := K) hn)

#print axioms orderFour_shape_coverage

end
end Mathproof.EvenTI.OrderFour
