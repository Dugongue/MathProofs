import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Field.Basic

namespace Hypoworld

theorem truncation_length_shift (n : ℕ) :
    (n + 2).choose 2 % 2 = (n.choose 2 + 1) % 2 := by
  have h₁ : (n + 1).choose 2 = n.choose 1 + n.choose 2 :=
    Nat.choose_succ_succ' n 1
  have h₂ : (n + 2).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 :=
    Nat.choose_succ_succ' (n + 1) 1
  simp only [Nat.choose_one_right] at h₁ h₂
  omega

theorem four_line_anchor_recovers_scalar {K : Type*} [Field K]
    {a b c d w t u v : K} (ha : a ≠ 0) (hb : b = 0) (hc : c = 0)
    (h₃ : a + b = w ∧ c + d = w)
    (h₄ : a + b * u = t ∧ c + d * u = t * v) :
    a = d ∧ u = v := by
  have hw : a = w := by simpa only [hb, add_zero] using h₃.1
  have hd : d = w := by simpa only [hc, zero_add] using h₃.2
  have had : a = d := hw.trans hd.symm
  have ht : a = t := by simpa only [hb, zero_mul, add_zero] using h₄.1
  have huv : a * u = a * v := by
    simpa only [hc, zero_add, ← had, ← ht] using h₄.2
  exact ⟨had, mul_left_cancel₀ ha huv⟩

end Hypoworld
