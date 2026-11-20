import Mathlib.Tactic.Group

namespace PeirceTransport

theorem normalized_corner_conjugation {U : Type*} [CommGroup U]
    (u v w a b z : U) :
    (((v / w) * a) * ((u / v) * b))⁻¹ * ((u / w) * z) = (a * b)⁻¹ * z := by
  have h : ((v / w) * a) * ((u / v) * b) = (u / w) * (a * b) := by
    calc
      _ = ((u / v) * (v / w)) * (a * b) := by ac_rfl
      _ = _ := by
        have hcancel : (u / v) * (v / w) = u / w := by
          simp only [div_eq_mul_inv]
          group
        rw [hcancel]
  have hc : (u / w)⁻¹ * ((u / w) * z) = z := by
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [h, mul_inv_rev, mul_assoc, hc]

theorem normalized_corner_composition {U : Type*} [CommGroup U]
    (a₁ a₂ b₁ b₂ z₁ z₂ : U) :
    ((a₁ * a₂) * (b₁ * b₂))⁻¹ * (z₁ * z₂) =
      ((a₁ * b₁)⁻¹ * z₁) * ((a₂ * b₂)⁻¹ * z₂) := by
  have h : (a₁ * a₂) * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by ac_rfl
  rw [h, mul_inv_rev]
  ac_rfl

theorem normalized_idempotent_unit {U : Type*} [Group U]
    (a : U) (h : a * a = a) : a = 1 := by
  have eq := congrArg (fun x => a⁻¹ * x) h
  simpa [← mul_assoc] using eq

end PeirceTransport

#print axioms PeirceTransport.normalized_corner_conjugation
#print axioms PeirceTransport.normalized_corner_composition
#print axioms PeirceTransport.normalized_idempotent_unit
