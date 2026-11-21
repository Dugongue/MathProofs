import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-- The three allowed states of a negative binary gadget cancel, while state 00 has nonzero weight. -/
theorem negativeClauseCancellation {K : Type*} [Field K] (r s : K)
    (hr : 1 + r ≠ 0) (hs : 1 + s ≠ 0) (h : 1 + r + s = 0) :
    let a := r / (1 + r)
    let b := s / (1 + s)
    (1 - a) * (1 - b) ≠ 0 ∧ ((1 - a) * (1 - b) + a * (1 - b) + (1 - a) * b = 0) := by
  dsimp only
  have ha : 1 - r / (1 + r) = 1 / (1 + r) := by
    field_simp [hr] <;> ring
  have hb : 1 - s / (1 + s) = 1 / (1 + s) := by
    field_simp [hs] <;> ring
  rw [ha, hb]
  constructor
  · exact mul_ne_zero (one_div_ne_zero hr) (one_div_ne_zero hs)
  · calc
      _ = (1 + r + s) / ((1 + r) * (1 + s)) := by
        field_simp [hr, hs] <;> ring
      _ = 0 := by rw [h, zero_div]
