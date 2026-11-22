import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.Defs

theorem fixed_orbit_iff_fixed_lift {G X : Type*} [Group G] [MulAction G X]
    (J : Subgroup G) (g : G) (x : X) :
    (∃ j : J, g • x = (j : G) • x) ↔
      (∃ j : J, ((j : G) * g) • x = x) := by
  constructor
  · rintro ⟨j, h⟩
    refine ⟨j⁻¹, ?_⟩
    change ((j : G)⁻¹ * g) • x = x
    rw [mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  · rintro ⟨j, h⟩
    refine ⟨j⁻¹, ?_⟩
    change g • x = (j : G)⁻¹ • x
    calc
      g • x = (j : G)⁻¹ • (((j : G) * g) • x) := by
        rw [← mul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = (j : G)⁻¹ • x := by rw [h]
