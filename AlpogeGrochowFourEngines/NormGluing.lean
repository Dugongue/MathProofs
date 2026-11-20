import Mathlib.Algebra.Group.Hom.Basic

namespace TensorNormGluing

theorem triple_norm_fiber
    {G H : Type*} [CommGroup G] [CommGroup H]
    (N : G →* H) (z : G) (a b c : H) :
    (∃ u v w : G, N u = a ∧ N v = b ∧ N w = c ∧ u * v * w = z) ↔
      (∃ u : G, N u = a) ∧ (∃ v : G, N v = b) ∧ N z = a * b * c := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, h⟩
    refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ?_⟩
    rw [← h, map_mul, map_mul, hu, hv, hw]
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩, hz⟩
    refine ⟨u, v, (u * v)⁻¹ * z, hu, hv, ?_, ?_⟩
    · rw [map_mul, map_inv, map_mul, hu, hv, hz]
      simp [← mul_assoc]
    · simp [← mul_assoc]

end TensorNormGluing
