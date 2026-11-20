import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace ExactGLSeparatorDegrees

/-- A vanished interior weight makes the boundary weight a multiple of the cycle determinant. -/
theorem cycle_boundary (r : ℤ) (a : ℕ) (c : ℕ → ℤ)
    (step : ∀ i < a, c i = r * c (i + 1)) :
    r * c 0 - c a = (r ^ (a + 1) - 1) * c a := by
  have chain : c 0 = r ^ a * c a := by
    induction a with
    | zero => simp
    | succ i ih =>
      calc
        c 0 = r ^ i * c i := ih (fun j hj => step j (Nat.lt_succ_of_lt hj))
        _ = r ^ i * (r * c (i + 1)) := by rw [step i (Nat.lt_succ_self i)]
        _ = r ^ (i + 1) * c (i + 1) := by rw [pow_succ, mul_assoc]
  rw [chain, pow_succ]
  ring

/-- Multiplying a payload weight by the arity base does not relax the cycle divisibility. -/
theorem cancel_base_from_cycle (r t : ℤ) (m : ℕ)
    (multiple : (r ^ (m + 1) - 1) ∣ r * t) :
    (r ^ (m + 1) - 1) ∣ t := by
  obtain ⟨c, hc⟩ := multiple
  refine ⟨r ^ m * c - t, ?_⟩
  rw [pow_succ] at hc ⊢
  linear_combination (r ^ m) * hc

/-- The total number of opposed marker factors bounds the net reverse weight cost. -/
theorem balanced_total_degree (r t forward reverse : ℤ) (hr : 1 ≤ r)
    (hf : 0 ≤ forward) (balance : r * t = (r - 1) * (reverse - forward)) :
    (2 * r - 1) * t ≤ (r - 1) * (t + forward + reverse) := by
  have extra : 0 ≤ 2 * ((r - 1) * forward) :=
    mul_nonneg (by decide) (mul_nonneg (sub_nonneg.mpr hr) hf)
  calc
    (2 * r - 1) * t ≤ (2 * r - 1) * t + 2 * ((r - 1) * forward) :=
      le_add_of_nonneg_right extra
    _ = (r - 1) * (t + forward + reverse) := by linear_combination balance

end ExactGLSeparatorDegrees

#print axioms ExactGLSeparatorDegrees.cycle_boundary
#print axioms ExactGLSeparatorDegrees.cancel_base_from_cycle
#print axioms ExactGLSeparatorDegrees.balanced_total_degree
