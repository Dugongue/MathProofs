import Mathlib.Data.Nat.Basic

namespace FirstRankDropFour

theorem isolate_rank_window {n s i j data extra : ℕ}
    (hn : 0 < n) (hd₁ : 1 ≤ data) (hd₂ : data ≤ n) (he : extra ≤ n)
    (hr : (s + i) * (2 * n + 1) + data + extra =
      (s + j) * (2 * n + 1) + 1) :
    i = j ∧ data = 1 ∧ extra = 0 := by
  have separated (a b : ℕ) (hab : a < b) :
      (s + a) * (2 * n + 1) + 2 * n < (s + b) * (2 * n + 1) := by
    have h : (s + a + 1) * (2 * n + 1) ≤ (s + b) * (2 * n + 1) :=
      Nat.mul_le_mul_right (2 * n + 1) (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have hgap := separated i j h
      omega
    · exact h
    · have hgap := separated j i h
      omega
  subst j
  exact ⟨rfl, by omega, by omega⟩

end FirstRankDropFour
