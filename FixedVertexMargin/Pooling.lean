import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace FixedVertexMargin

theorem pooled_price_loss {ι : Type*} [Fintype ι] (m v : ι → ℝ) (u : ℝ)
    (centered : ∑ i, m i * (v i - u) = 0) :
    (∑ i, m i * v i ^ 2) - (∑ i, m i) * u ^ 2 =
      ∑ i, m i * (v i - u) ^ 2 := by
  calc
    _ = ∑ i, (m i * v i ^ 2 - m i * u ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ i, m i * (v i - u) ^ 2) + (∑ i, m i * (v i - u)) * (2 * u) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by rw [centered, zero_mul, add_zero]

end FixedVertexMargin
