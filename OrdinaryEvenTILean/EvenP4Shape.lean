import EvenP4Probability
import EvenP4HigherRecip
import EvenP2Coverage
import EvenP3Coverage

namespace Mathproof.EvenTI.GlobalCoverage

open scoped BigOperators Classical Matrix
open EvenTI.Action EvenTI.Primary Matrix
open Mathproof.EvenTI.OrderFour Mathproof.EvenTI.Reciprocal.Coverage
open Mathproof.EvenTI.Singular.Coverage Mathproof.Problem17PrimaryTail

noncomputable section

variable {K : Type} [Field K] [Fintype K] {d l n : ℕ}

/-- The actual higher-order spectral gates on the specified balanced cut. -/
def higherShapeAccepted (hn : 1 ≤ n) (T : Source K l n) : Prop :=
  ((flatten (l := l + 1) (r := l + 1) T).det = 0 ∧ singularShapeAccepted T) ∨
    higherReciprocalAccepted hn T

private theorem higher_shape_failure_implies (hn : 1 ≤ n) (T : Source K l n)
    (h : ¬ higherShapeAccepted hn T) : singularShapeBad T ∨ higherReciprocalBad hn T := by
  by_cases hz : (flatten (l := l + 1) (r := l + 1) T).det = 0
  · exact Or.inl ⟨hz, fun hs => h (Or.inl ⟨hz, hs⟩)⟩
  · have hu : IsUnit (flatten (l := l + 1) (r := l + 1) T) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hz)
    exact Or.inr ⟨hu, lt_of_not_ge (fun hb => h (Or.inr ⟨hu, hb⟩))⟩

theorem higher_shape_failure_le (hl : 2 ≤ l) (hn : 200 ≤ n) :
    event (fun T : Source K l n => ¬ higherShapeAccepted (by omega : 1 ≤ n) T) ≤
      (2 / (n : ℝ) + 2 / (Fintype.card K : ℝ)^n + spectralFailureBound K n) +
        (budgetConstant K + 9) * Real.log (Fintype.card K) / Real.log n := by
  have hp := higherOrder_singular_coverage (K := K) hl (by omega : 64 ≤ n)
  have hr := higherOrder_reciprocal_bad_le (K := K) hl hn
  have h := event_le_of_imp (higher_shape_failure_implies (K := K) (l := l) (by omega : 1 ≤ n))
  exact (h.trans (event_union_le _ _)).trans (add_le_add hp hr)

/-- The spectral part of the recognizer at even orders. Each of the two
clauses names its arithmetic order and transports the original tensor. -/
def sourceSpectralAccepted (T : Tensor K d n) : Prop :=
  (∃ hd : d = 4, ∃ hn : 5 ≤ n, orderFourShapeAccepted hn (hd ▸ T)) ∨
    ∃ l : ℕ, 2 ≤ l ∧ ∃ hd : d = (l + 1) + (l + 1), ∃ hn : 1 ≤ n,
      higherShapeAccepted hn (hd ▸ T)

theorem four_spectral_accepts (hn : 5 ≤ n) (T : Four K n)
    (h : orderFourShapeAccepted hn T) : sourceSpectralAccepted T :=
  Or.inl ⟨rfl, hn, h⟩

theorem higher_spectral_accepts (hl : 2 ≤ l) (hn : 1 ≤ n) (T : Source K l n)
    (h : higherShapeAccepted hn T) : sourceSpectralAccepted T :=
  Or.inr ⟨l, hl, rfl, hn, h⟩

theorem four_spectral_iff (hn : 5 ≤ n) (T : Four K n) :
    sourceSpectralAccepted T ↔ orderFourShapeAccepted hn T := by
  refine ⟨?_, four_spectral_accepts hn T⟩
  intro h
  rcases h with ⟨hd, hwidth, h⟩ | ⟨l, hl, hd, hwidth, h⟩
  · exact h
  · omega

theorem higher_spectral_iff (hl : 2 ≤ l) (hn : 1 ≤ n) (T : Source K l n) :
    sourceSpectralAccepted T ↔ higherShapeAccepted hn T := by
  refine ⟨?_, higher_spectral_accepts hl hn T⟩
  intro h
  rcases h with ⟨hd, hwidth, h⟩ | ⟨l', hl', hd, hwidth, h⟩
  · omega
  · have he : l' = l := by omega
    subst l'
    exact h

theorem even_order_as_balanced_halves (hd : 6 ≤ d) (he : Even d) :
    ∃ l : ℕ, 2 ≤ l ∧ d = (l + 1) + (l + 1) := by
  have hm := Nat.even_iff.mp he
  exact ⟨d / 2 - 1, by omega, by omega⟩

#print axioms higher_shape_failure_le
#print axioms four_spectral_accepts
#print axioms higher_spectral_accepts
#print axioms four_spectral_iff
#print axioms higher_spectral_iff
#print axioms even_order_as_balanced_halves

end
end Mathproof.EvenTI.GlobalCoverage
