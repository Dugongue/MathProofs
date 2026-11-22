import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem weightedRadiusValue {ι : Type*} (s : Finset ι) (a x y : ι → ℝ) (t c : ℝ) :
    c + (∑ i ∈ s, a i * ((1 - t) * x i + t * y i)) =
      (1 - t) * (c + ∑ i ∈ s, a i * x i) + t * (c + ∑ i ∈ s, a i * y i) := by
  calc
    _ = c + ∑ i ∈ s, ((1 - t) * (a i * x i) + t * (a i * y i)) := by
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
