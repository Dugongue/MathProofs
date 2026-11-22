import Mathlib.Tactic.Group

namespace PolyhedralHexagon

theorem determinant_evaluation {U : Type*} [CommGroup U]
    (H X t d : U) (matching : X = H ^ 3 * t) :
    H * X ^ 5 * d ^ 6 = H ^ 16 * d ^ 6 * t ^ 5 := by
  calc
    H * X ^ 5 * d ^ 6 = H ^ 16 * t ^ 5 * d ^ 6 := by
      rw [matching, mul_pow]
      group
    _ = H ^ 16 * d ^ 6 * t ^ 5 := by ac_rfl

theorem exact_determinant_range {U : Type*} [CommGroup U] (t u : U) :
    (∃ H d : U, H ^ 16 * d ^ 6 * t ^ 5 = u) ↔
      (∃ k : U, k ^ 2 * t = u) := by
  constructor
  · rintro ⟨H, d, rfl⟩
    refine ⟨H ^ 8 * d ^ 3 * t ^ 2, ?_⟩
    rw [mul_pow, mul_pow]
    group
  · rintro ⟨k, rfl⟩
    let a := k * (t ^ 2)⁻¹
    refine ⟨a⁻¹, a ^ 3, ?_⟩
    calc
      (a⁻¹) ^ 16 * (a ^ 3) ^ 6 * t ^ 5 = a ^ 2 * t ^ 5 := by group
      _ = k ^ 2 * t := by
        dsimp [a]
        rw [mul_pow]
        group

theorem determinant_one_iff_square {U : Type*} [CommGroup U] (t : U) :
    (∃ H d : U, H ^ 16 * d ^ 6 * t ^ 5 = 1) ↔
      (∃ k : U, k ^ 2 = t) := by
  rw [exact_determinant_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k⁻¹, ?_⟩
    calc
      (k⁻¹) ^ 2 = (k ^ 2)⁻¹ := by group
      _ = (k ^ 2)⁻¹ * (k ^ 2 * t) := by rw [hk, mul_one]
      _ = t := by group
  · rintro ⟨k, rfl⟩
    exact ⟨k⁻¹, by group⟩

end PolyhedralHexagon
