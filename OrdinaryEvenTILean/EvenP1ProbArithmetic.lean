import EvenSingularColumns

namespace Mathproof.EvenTI.Reciprocal.PartOne

/-- A single half-rank cutoff makes the union bound more than sufficient
uniformly for bundled dimensions at least n². The threshold is explicit. -/
theorem cutoff_union_bound (q : ℝ) (n m : ℕ) (hq : 2 ≤ q)
    (hn : 200 ≤ n) (hm : n^2 ≤ m) :
    let b := m/5
    let r := b/2
    q^((n-1)*(n^2-1)) *
      ((2:ℝ)^b / q^((b-r)*(m-b-r)) + 1/q^(b*r)) ≤ 1/q^(n^2) := by
  let b := m/5
  let r := b/2
  let L := (n-1)*(n^2-1)
  let T := (b-r)*(m-b-r)
  change q^L * ((2:ℝ)^b / q^T + 1/q^(b*r)) ≤ 1/q^(n^2)
  have h200n : 200*n ≤ n^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right n hn
  have hb : 40*n ≤ b := by
    dsimp [b]
    omega
  have hr : 20*n ≤ r := by
    dsimp [r]
    omega
  have hb6 : n^2 ≤ 6*b := by
    dsimp [b] at hb ⊢
    omega
  have hmult1 := Nat.mul_le_mul_right r hb6
  have hmult2 := Nat.mul_le_mul_left (n^2) hr
  have hpow : 2*n^3 ≤ b*r := by nlinarith only [hmult1, hmult2]
  have hn2 : 2*n^2 ≤ n^3 := by
    convert Nat.mul_le_mul_right (n^2) (show 2 ≤ n by omega) using 1 <;> ring
  have hone : 1 ≤ n^2 := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hL : L ≤ n^3 := by
    dsimp [L]
    calc
      _ ≤ n*n^2 := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = _ := by ring
  have hbudget : L+n^2+1 ≤ b*r := by omega
  have hT : b + b*r ≤ T := by
    have h1 : r ≤ b-r := by dsimp [r]; omega
    have h2 : b+3 ≤ m-b-r := by dsimp [r, b] at hb ⊢; omega
    have h3 : b ≤ 3*r := by dsimp [r]; omega
    calc
      _ ≤ r*(b+3) := by
        rw [Nat.mul_add, mul_comm r b, mul_comm r 3]
        omega
      _ ≤ _ := Nat.mul_le_mul h1 h2
  have h0 : 0 < q := by linarith
  have h1 : 1 ≤ q := by linarith
  have div_bound (s t : ℕ) (h : s+(n^2+1) ≤ t) :
      q^s / q^t ≤ 1 / q^(n^2+1) := by
    apply (div_le_div_iff₀ (pow_pos h0 _) (pow_pos h0 _)).mpr
    rw [one_mul, ← pow_add]
    exact pow_le_pow_right₀ h1 h
  calc
    _ = q^L * (2:ℝ)^b / q^T + q^L / q^(b*r) := by ring
    _ ≤ q^(L+b) / q^T + q^L / q^(b*r) := by
      rw [pow_add]
      gcongr
    _ ≤ 1 / q^(n^2+1) + 1 / q^(n^2+1) := by
      exact add_le_add (div_bound _ _ (by omega)) (div_bound _ _ (by omega))
    _ ≤ _ := by
      rw [← add_div, pow_succ]
      apply (div_le_div_iff₀ (mul_pos (pow_pos h0 _) h0) (pow_pos h0 _)).mpr
      simpa only [one_mul, mul_one, one_add_one_eq_two, mul_comm] using
        (mul_le_mul_of_nonneg_left hq (pow_nonneg h0.le (n^2)))

#print axioms cutoff_union_bound

end Mathproof.EvenTI.Reciprocal.PartOne
