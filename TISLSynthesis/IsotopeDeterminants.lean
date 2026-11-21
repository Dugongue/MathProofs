import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group

namespace TensorOrientation

/-- The independent input and output determinants after isotope normalization. -/
theorem isotope_determinants {G : Type*} [CommGroup G] (x y h d e : G) :
    (x * h = d ∧ y * h = e ∧ x * y * h = 1) ↔
      (h = d * e ∧ x = e⁻¹ ∧ y = d⁻¹) := by
  constructor
  · rintro ⟨hd, he, hz⟩
    have hh : d * e = h := calc
      d * e = (x * y * h) * h := by rw [← hd, ← he]; ac_rfl
      _ = h := by rw [hz, one_mul]
    refine ⟨hh.symm, ?_, ?_⟩
    · calc
        x = (x * y * h) * (y * h)⁻¹ := by
          rw [show x * y * h = x * (y * h) by ac_rfl]
          exact (mul_inv_cancel_right x (y * h)).symm
        _ = e⁻¹ := by rw [hz, he, one_mul]
    · calc
        y = (x * y * h) * (x * h)⁻¹ := by
          rw [show x * y * h = y * (x * h) by ac_rfl]
          exact (mul_inv_cancel_right y (x * h)).symm
        _ = d⁻¹ := by rw [hz, hd, one_mul]
  · rintro ⟨rfl, rfl, rfl⟩
    constructor
    · calc
        e⁻¹ * (d * e) = d * (e⁻¹ * e) := by ac_rfl
        _ = d := by simp
    · constructor
      · calc
          d⁻¹ * (d * e) = (d⁻¹ * d) * e := by ac_rfl
          _ = e := by simp
      · calc
          e⁻¹ * d⁻¹ * (d * e) = (e⁻¹ * e) * (d⁻¹ * d) := by ac_rfl
          _ = 1 := by simp

end TensorOrientation
