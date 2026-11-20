import EvenP4Shape
import EvenP4OrderFourLimit
import EvenP4ScalarDensity

namespace Mathproof.EvenTI.GlobalCoverage

open scoped Classical
open EvenTI.Action EvenTI.Primary
open Mathproof.EvenTI.OrderFour Mathproof.EvenTI.Singular.Coverage
open Mathproof.Problem17PrimaryTail

noncomputable section

variable {K : Type} [Field K] [Fintype K] {d l n : ℕ}

def sourceAccepted (T : Tensor K d n) : Prop :=
  sourceSpectralAccepted T ∧ scalarAccepted T

noncomputable def sourceAccept (T : Tensor K d n) : Bool := decide (sourceAccepted T)

@[simp] theorem sourceAccept_eq_true (T : Tensor K d n) :
    sourceAccept T = true ↔ sourceAccepted T := by simp [sourceAccept]

theorem accepted_has_scalar_stabilizer (T : Tensor K d n) (hT : sourceAccept T = true) :
    scalarAccepted T := ((sourceAccept_eq_true T).mp hT).2

def coverageConstant (K : Type) [Field K] [Fintype K] : ℝ :=
  5 + (2 * budgetConstant K + 11) * Real.log (Fintype.card K)

theorem one_le_coverageConstant (K : Type) [Field K] [Fintype K] :
    1 ≤ coverageConstant K := by
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  have hb := budgetConstant_nonneg (K := K)
  have h : 0 ≤ (2 * budgetConstant K + 11) * Real.log (Fintype.card K) :=
    mul_nonneg (by linarith) (Real.log_nonneg hq)
  unfold coverageConstant
  linarith

private theorem scalar_failure_log_bound (hn : 5 ≤ n) (hd : 4 ≤ d) :
    event (fun T : Tensor K d n => ¬ scalarAccepted T) ≤ 1 / Real.log n := by
  refine (scalar_bad_le (K := K) hn hd).trans ?_
  apply inverse_pow_le_inv_log _ _ _ Fintype.one_lt_card (by omega)
  calc
    n = n * 1 := by simp
    _ ≤ n * n := Nat.mul_le_mul_left n (by omega)
    _ = n^2 := by rw [pow_two]

private theorem higher_failure_balanced_halves (hl : 2 ≤ l) (hn : 200 ≤ n) :
    event (fun T : Source K l n => ¬ sourceAccepted T) ≤ coverageConstant K / Real.log n := by
  have hs : event (fun T : Source K l n => ¬ sourceSpectralAccepted T) ≤
      event (fun T : Source K l n => ¬ higherShapeAccepted (by omega : 1 ≤ n) T) :=
    event_le_of_imp (fun T h => mt (higher_spectral_accepts hl (by omega) T) h)
  have hSpec := hs.trans (higher_shape_failure_le (K := K) hl hn)
  have hScalar := scalar_failure_log_bound (K := K) (n := n)
    (d := (l + 1) + (l + 1)) (by omega) (by omega)
  have hN := two_over_n_le_log n (by omega)
  have hPow : 2 / (Fintype.card K : ℝ)^n ≤ 2 / Real.log n := by
    have h := inverse_pow_le_inv_log (Fintype.card K) n n Fintype.one_lt_card (by omega) le_rfl
    simpa only [div_eq_mul_inv, one_mul] using
      (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2))
  have hA := failure_of_intersection_le (sourceSpectralAccepted : Source K l n → Prop) scalarAccepted
  have hB := (hA.trans (add_le_add hSpec hScalar))
  calc
    _ ≤ (2 / (n : ℝ) + 2 / (Fintype.card K : ℝ)^n + spectralFailureBound K n +
        (budgetConstant K + 9) * Real.log (Fintype.card K) / Real.log n) + 1 / Real.log n := hB
    _ ≤ (2 / Real.log n + 2 / Real.log n + spectralFailureBound K n +
        (budgetConstant K + 9) * Real.log (Fintype.card K) / Real.log n) + 1 / Real.log n :=
      add_le_add (add_le_add (add_le_add (add_le_add hN hPow) le_rfl) le_rfl) le_rfl
    _ = _ := by unfold coverageConstant spectralFailureBound; ring

/-- The logarithmic rate has one constant and one cutoff for all even
orders at least six over the fixed field. -/
theorem higher_order_source_failure_le (hd : 6 ≤ d) (he : Even d) (hn : 200 ≤ n) :
    event (fun T : Tensor K d n => ¬ sourceAccepted T) ≤ coverageConstant K / Real.log n := by
  obtain ⟨l, hl, rfl⟩ := even_order_as_balanced_halves hd he
  exact higher_failure_balanced_halves hl hn

theorem higherOrderRate (K : Type) [Field K] [Fintype K] :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ d n : ℕ, 6 ≤ d → Even d → N ≤ n →
      event (fun T : Tensor K d n => ¬ sourceAccepted T) ≤ C / Real.log n := by
  refine ⟨coverageConstant K, zero_lt_one.trans_le (one_le_coverageConstant K), 200, by decide, ?_⟩
  intro d n hd he hn
  exact higher_order_source_failure_le hd he hn

/-- This cutoff is independent of the even tensor order. -/
theorem uniformCoverage (K : Type) [Field K] [Fintype K]
    (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 2 ≤ N ∧ ∀ d n : ℕ, 4 ≤ d → Even d → N ≤ n →
      event (fun T : Tensor K d n => ¬ sourceAccepted T) ≤ ε := by
  have hHalf : 0 < ε / 2 := by positivity
  obtain ⟨N₄, hN₄, hFour⟩ := orderFour_shape_rejection_eventually_le K hHalf
  obtain ⟨Nh, hHigher⟩ := div_log_eventually_le (coverageConstant K) hHalf
  let N := max 200 (max N₄ Nh)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro d n hd he hn
  have h200 : 200 ≤ n := (le_max_left 200 _).trans hn
  have h4 : N₄ ≤ n := ((le_max_left N₄ Nh).trans (le_max_right 200 _)).trans hn
  have hH : Nh ≤ n := ((le_max_right N₄ Nh).trans (le_max_right 200 _)).trans hn
  have hHalfH := hHigher n hH
  by_cases hEq : d = 4
  · subst d
    have hs : event (fun T : Four K n => ¬ sourceSpectralAccepted T) ≤ ε/2 := by
      refine (event_le_of_imp (fun T h => mt (four_spectral_accepts (by omega) T) h)).trans ?_
      exact hFour n h4 (by omega)
    have hScalar := scalar_failure_log_bound (K := K) (n := n) (d := 4) (by omega) (by decide)
    have hLog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hScalarHalf := hScalar.trans ((div_le_div_of_nonneg_right (one_le_coverageConstant K) hLog).trans hHalfH)
    exact ((failure_of_intersection_le (sourceSpectralAccepted : Four K n → Prop) scalarAccepted).trans
      (add_le_add hs hScalarHalf)).trans (by linarith)
  · have h6 : 6 ≤ d := by have hm := Nat.even_iff.mp he; omega
    exact ((higher_order_source_failure_le (K := K) h6 he h200).trans hHalfH).trans (by linarith)

#print axioms accepted_has_scalar_stabilizer
#print axioms higherOrderRate
#print axioms uniformCoverage

end
end Mathproof.EvenTI.GlobalCoverage
