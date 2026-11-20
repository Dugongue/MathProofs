import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mathproof.EvenTI.Reciprocal.SquareLow

set_option maxRecDepth 4096 in
/-- For the square-cut row budget b floor(b/2), the simultaneous low-label
failure mass loses at least one full power q^n in the denominator. -/
theorem square_low_budget (n s : ℕ) (hn : 1000 ≤ n) (hs : 1000000*s ≤ n*n) :
    8*s + 2*n + 9 + n ≤ (n/5) * ((n/5)/2) := by
  let b := n / 5
  let r := b / 2
  have hbn : n ≤ 6*b := by dsimp [b]; omega
  have hbr : 6*b ≤ 18*r := by dsimp [r]; omega
  have hB : n*n ≤ 108*(b*r) :=
    (Nat.mul_le_mul hbn (hbn.trans hbr)).trans_eq (by ring)
  have hl : 2*(864*s) ≤ n*n := by omega
  have hr : 2*(324*n+972) ≤ n*n := by
    calc
      _ ≤ 2*(324*n+n) := Nat.mul_le_mul_left 2 (Nat.add_le_add_left (by omega) _)
      _ = 650*n := by ring
      _ ≤ _ := Nat.mul_le_mul_right n (by omega)
  change 8*s + 2*n + 9 + n ≤ b*r
  omega

/-- The cumulative count is sufficient for a fixed-rank Fourier slice. -/
theorem square_low_rank_slice (q : ℝ) (hq : 1 ≤ q) (n s : ℕ)
    (hn : 4 ≤ n) (hs : n-2 ≤ s) :
    q^(4*s+2*n+9) * (q^(15*s))⁻¹ ≤ (q^(9*n-31))⁻¹ := by
  have hb : (4*s+2*n+9)+(9*n-31) ≤ 15*s := by omega
  have hp : 0 < q := by linarith
  rw [← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ hq hb

theorem square_low_bad_mass_numeric (q : ℝ) (hq : 1 ≤ q) (n s B : ℕ)
    (hB : 8*s + 2*n + 9 + n ≤ B) :
    q^(4*s+2*n+9) * (4 * q^(4*s) * (1/q^B + 1/q^B)) ≤ 8/q^n := by
  have hp : 0 < q := by linarith
  calc
    _ = 8*q^(8*s+2*n+9)/q^B := by
      rw [show 8*s+2*n+9 = (4*s+2*n+9)+(4*s) by omega, pow_add]
      ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [mul_assoc, ← pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hB) (by norm_num)

#print axioms square_low_budget
#print axioms square_low_rank_slice
#print axioms square_low_bad_mass_numeric

end Mathproof.EvenTI.Reciprocal.SquareLow
