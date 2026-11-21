import Mathlib.Tactic

namespace MatrixPCAdvances

theorem failedPrefixIsOld (t h n l r : ℕ) (hf : t < h + n)
    (hh : h ≤ l) (hn : n ≤ l) (hr : 2 * l ≤ r + 1) : t ≤ r := by
  omega

theorem residualBudget (d s b q : ℕ) (hs : s ≤ b) (hd : d ≤ b + 1)
    (hq : d < 2 * q) :
    2 * ((d - s) / 2) ≤ b - s + 1 ∧ (d - s) / 2 < q := by
  omega

theorem gainedRowBudget (d s : ℕ) :
    (d - (s + 1)) / 2 = (d - 1 - s) / 2 := by
  omega

theorem lostRowBudget (d s : ℕ) (hs : 0 < s) (hd : s < d) :
    (d - (s - 1)) / 2 - 1 = (d - 1 - s) / 2 := by
  omega

theorem plateauWindow (n p q : ℕ) (hq : 0 < q) (hlo : 5 * q ≤ n + 4)
    (hhi : n + 3 ≤ p * q + 4 * q) :
    2 * q ≤ (n - q) / 2 + 2 ∧ (n - p * q) / 2 + 2 ≤ 2 * q := by
  omega

theorem nonsquarePowerContradiction {K : Type*} [Field K] {x c : K}
    (two_ne : (2 : K) ≠ 0) (n : ℕ) (hc : c ≠ 0)
    (hneg : c ^ n = -1) (hsq : x ^ 2 = c) (hpow : x ^ (2 * n + 1) = x) :
    False := by
  rw [pow_succ, pow_mul, hsq, hneg, neg_one_mul] at hpow
  have hx : (2 : K) * x = 0 := by linear_combination -hpow
  have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_left two_ne
  exact hc (by simpa [hx0] using hsq.symm)

end MatrixPCAdvances
