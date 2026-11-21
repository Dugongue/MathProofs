import Mathlib.Tactic

namespace DiagonalLocalGlobal

theorem signNormCoordinates {K : Type*} [Field K] (s u v : K)
    (hs : s * s = 1) (hu : u ≠ 0) (hv : v ≠ 0) :
    let d₁ := s * u
    let d₂ := s * v
    let d₃ := s * u * v
    d₁ * d₂ / d₃ = s ∧ d₁ / s = u ∧ d₂ / s = v := by
  change (s * u) * (s * v) / (s * u * v) = s ∧ (s * u) / s = u ∧ (s * v) / s = v
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  constructor
  · apply (div_eq_iff (mul_ne_zero (mul_ne_zero hs0 hu) hv)).2
    ring
  constructor
  · apply (div_eq_iff hs0).2
    exact mul_comm s u
  · apply (div_eq_iff hs0).2
    exact mul_comm s v

theorem fixedPointGap {ι : Type*} [Fintype ι] (x y : ι → ℤ) (bad : ι → Bool)
    (h : ∀ i, y i - x i = if bad i then 2 else 0) :
    (∑ i, x i) = (∑ i, y i) ↔ ∀ i, bad i = false := by
  classical
  have hnonneg (i : ι) : 0 ≤ y i - x i := by
    rw [h i]
    split <;> decide
  have hsum : (∑ i, (y i - x i)) = (∑ i, y i) - (∑ i, x i) :=
    Finset.sum_sub_distrib y x
  constructor
  · intro heq i
    have hzero : (∑ j, (y j - x j)) = 0 := by rw [hsum, heq, sub_self]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hnonneg j)).mp hzero i (Finset.mem_univ i)
    cases hb : bad i
    · rfl
    · simp [h i, hb] at hi
  · intro hgood
    have hzero : (∑ i, (y i - x i)) = 0 := by simp [h, hgood]
    omega

theorem normCharacterParity (a b c : ZMod 2)
    (ha : a + c = 0) (hb : b + c = 0) :
    a = b ∧ b = c := by
  have hc : c + c = 0 := by
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  exact ⟨add_right_cancel (ha.trans hb.symm), add_right_cancel (hb.trans hc.symm)⟩

end DiagonalLocalGlobal
