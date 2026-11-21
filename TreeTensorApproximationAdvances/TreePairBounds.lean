import Mathlib.Tactic

namespace TreePairBounds

theorem pairedSaving (r u : ℝ) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    1 / (r + 3) ≤ max u ((1 - u) ^ 2 / (r + 1 - u)) := by
  have hrp : 0 < r + 3 := by linarith
  by_cases h : 1 / (r + 3) ≤ u
  · exact le_trans h (le_max_left _ _)
  · have hprod : u * (r + 3) ≤ 1 :=
      (le_div_iff₀ hrp).mp (le_of_lt (lt_of_not_ge h))
    have hthree : 3 * u ≤ 1 := by
      nlinarith only [hprod, mul_nonneg hu hr]
    have hden : 0 < r + 1 - u := by linarith
    have hdiff : 0 ≤ 2 - (2 * r + 5) * u := by
      nlinarith only [hprod, hu]
    have hsq : 0 ≤ (r + 3) * u ^ 2 := mul_nonneg (le_of_lt hrp) (sq_nonneg u)
    have hratio : 1 / (r + 3) ≤ (1 - u) ^ 2 / (r + 1 - u) := by
      apply (div_le_div_iff₀ hrp hden).2
      nlinarith only [hdiff, hsq]
    exact le_trans hratio (le_max_right _ _)

theorem orthogonalProjectionLoss {ι : Type*} [Fintype ι] (a y z : ι → ℝ)
    (orthogonal : (∑ i, (a i - y i) * z i) = 0) :
    (∑ i, (a i - (y i - z i)) ^ 2) =
      (∑ i, (a i - y i) ^ 2) + (∑ i, (z i) ^ 2) := by
  calc
    _ = ∑ i, ((a i - y i) ^ 2 + 2 * ((a i - y i) * z i) + (z i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, orthogonal]
      ring

theorem coverBound (mean unmarked count eps : ℝ)
    (positive : 0 < mean) (tol_nonneg : 0 ≤ eps)
    (mass : unmarked * ((1 + eps) * mean) < count * mean) :
    unmarked < count / (1 + eps) := by
  have denom_pos : 0 < 1 + eps := by linarith
  apply (lt_div_iff₀ denom_pos).2
  by_contra! h
  have hmul := mul_le_mul_of_nonneg_right h positive.le
  exact (not_lt_of_ge hmul) (by simpa only [mul_assoc] using mass)

end TreePairBounds
