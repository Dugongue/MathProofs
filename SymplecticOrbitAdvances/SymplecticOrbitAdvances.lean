import Mathlib.Tactic

namespace SymplecticOrbitAdvances

theorem tagSpectrumBounds (m c s v : ℝ) (hm : 1 ≤ m)
    (hc : m * c ^ 2 < m + 1) (hs : m + 1 < s) (hv : 0 ≤ v) :
    2 * c ^ 2 < 2 * (m + 1) ∧
    2 * m * c ^ 2 < 2 * (m + 1) ∧
    2 * (m + 1) < 2 * s + v := by
  have hmc : c ^ 2 ≤ m * c ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hm (sq_nonneg c)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem cyclicWeightLabels {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ)
    (h : ∀ i < n, w (i + 1) = 2 * w i) :
    w n = 2 ^ n * w 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h n (Nat.lt_succ_self n), ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), pow_succ]
    ring

theorem separatorDegreeFromCounts (t f r d : ℕ) (m : ℕ)
    (hm : 0 < m) (ht : 0 < t) (hWeight : m ∣ 7 * t)
    (hBalance : r = 3 * t + f) (hCount : t + f + r ≤ d) :
    4 * m ≤ 7 * d := by
  obtain ⟨q, hq⟩ := hWeight
  have hqpos : 0 < q := by
    by_contra! hq0
    have hz : q = 0 := by omega
    simp [hz] at hq
    omega
  have hmq : m ≤ m * q := by
    simpa using Nat.mul_le_mul_left m (show 1 ≤ q by omega)
  omega

end SymplecticOrbitAdvances
