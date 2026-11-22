import Mathlib.Data.Nat.Basic

theorem consecutive_fiber_counts (b n : ℕ) (hb : 2 ≤ b) (hn : b * b ≤ n) :
    ∃ u w : ℕ, n = b * u + (b - 1) * w ∧ w < b := by
  have hbpos : 0 < b := by omega
  let q := n / b
  let r := n % b
  have hr : r < b := Nat.mod_lt _ hbpos
  have hd : b * q + r = n := Nat.div_add_mod n b
  have hq : b ≤ q := (Nat.le_div_iff_mul_le hbpos).2 hn
  by_cases hzero : r = 0
  · exact ⟨q, 0, by simpa [hzero] using hd.symm, hbpos⟩
  · let w := b - r
    let u := q + 1 - w
    have hw : w < b := by dsimp [w]; omega
    have hwr : w + r = b := by dsimp [w]; omega
    have huw : u + w = q + 1 := by dsimp [u]; omega
    have hbpred : b - 1 + 1 = b := by omega
    have h₁ := congrArg (fun t : ℕ => b * t) huw
    have h₂ := congrArg (fun t : ℕ => t * w) hbpred
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at h₁ h₂
    refine ⟨u, w, ?_, hw⟩
    calc
      n = b * q + r := hd.symm
      _ = b * u + (b - 1) * w := by omega
