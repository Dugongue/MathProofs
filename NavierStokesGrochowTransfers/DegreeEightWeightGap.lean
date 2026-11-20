import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem degreeEightWeightGap (u v : ℕ → ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hpair : ∀ j, j ≤ m → 4 * u j + 4 * v j = 0)
    (hstep : ∀ j, 1 ≤ j → j < m → 2 * u (j + 1) + 4 * v j + 2 * u 0 = 0)
    (hextra : 0 < 2 * u 1 + 2 * v 0 + 2 * u m + 2 * v m) :
    (2 : ℤ) ^ (m - 1) ≤ u m - u 0 := by
  have hOpp (j : ℕ) (hj : j ≤ m) : v j = -u j := by
    have h := hpair j hj
    omega
  have hStart : 1 ≤ u 1 - u 0 := by
    rw [hOpp 0 (Nat.zero_le _), hOpp m (Nat.le_refl _)] at hextra
    omega
  have hRec (j : ℕ) (hj : 1 ≤ j) (hj' : j < m) :
      u (j + 1) - u 0 = 2 * (u j - u 0) := by
    have h := hstep j hj hj'
    rw [hOpp j (Nat.le_of_lt hj')] at h
    omega
  have hClosed (k : ℕ) (hk : k + 1 ≤ m) :
      u (k + 1) - u 0 = 2 ^ k * (u 1 - u 0) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hRec (k + 1) (by omega) (by omega), ih (by omega), pow_succ]
        ring
  have hIndex : m - 1 + 1 = m := by omega
  have h := hClosed (m - 1) (by omega)
  rw [hIndex] at h
  rw [h]
  have hNonneg : 0 ≤ (2 : ℤ) ^ (m - 1) := Int.pow_nonneg (by omega)
  simpa only [mul_one] using (Int.mul_le_mul_of_nonneg_left hStart hNonneg)
