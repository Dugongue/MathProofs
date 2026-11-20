import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DicksonSeparationWeights

/-- The weight at an endpoint is multiplied by the iterated Frobenius power. -/
theorem cyclic_weight_power (p : ℤ) (a : ℕ) (h : ℕ → ℤ)
    (step : ∀ i < a, h i = p * h (i + 1)) :
    p * h 0 - h a = (p ^ (a + 1) - 1) * h a := by
  have chain : h 0 = p ^ a * h a := by
    induction a with
    | zero => simp
    | succ i ih =>
      calc
        h 0 = p ^ i * h i := ih (fun j hj => step j (Nat.lt_succ_of_lt hj))
        _ = p ^ i * (p * h (i + 1)) := by rw [step i (Nat.lt_succ_self i)]
        _ = p ^ (i + 1) * h (i + 1) := by rw [pow_succ, mul_assoc]
  rw [chain, pow_succ]
  ring

/-- Discrete summation of the same recurrence gives the total auxiliary weight. -/
theorem cyclic_weight_total (p : ℤ) (a : ℕ) (h : ℕ → ℤ)
    (step : ∀ i < a, h i = p * h (i + 1)) :
    (p - 1) * (∑ i ∈ Finset.range (a + 1), h i) = p * h 0 - h a := by
  induction a with
  | zero => simp; ring
  | succ i ih =>
    rw [Finset.sum_range_succ, mul_add, ih (fun j hj => step j (Nat.lt_succ_of_lt hj))]
    linear_combination -step i (Nat.lt_succ_self i)

/-- The cost of opposed auxiliary records is at least the net weight cost. -/
theorem total_degree_bound (p d forward reverse : ℤ) (hp : 1 ≤ p) (hf : 0 ≤ forward)
    (hbalance : d = (p - 1) * (reverse - forward)) :
    p * d ≤ (p - 1) * (d + forward + reverse) := by
  have excess : 0 ≤ 2 * ((p - 1) * forward) := by
    exact mul_nonneg (by decide) (mul_nonneg (sub_nonneg.mpr hp) hf)
  calc
    p * d ≤ p * d + 2 * ((p - 1) * forward) := le_add_of_nonneg_right excess
    _ = (p - 1) * (d + forward + reverse) := by linear_combination hbalance

/-- In the absence of forward records the bound is an equality. -/
theorem reverse_degree_exact (p d reverse : ℤ)
    (hbalance : d = (p - 1) * reverse) :
    (p - 1) * (d + reverse) = p * d := by
  rw [hbalance]
  ring

end DicksonSeparationWeights
