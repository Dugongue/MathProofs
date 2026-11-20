import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic

namespace EmbeddedSubgroupTransport

theorem alignment_ratio {U : Type*} [CommGroup U]
    (source middle target a b : U) :
    (middle / target * a) * (source / middle * b) =
      (source / target) * (a * b) := by
  have h : middle / target * (source / middle) = source / target := by
    rw [div_mul_div_comm, mul_comm middle source, mul_div_mul_right_eq_div]
  rw [mul_mul_mul_comm, h]

theorem normalize_alignment {U X : Type*} [CommGroup U] [MulAction U X]
    (source middle target a b : U) (z : X) :
    ((middle / target * a) * (source / middle * b))⁻¹ •
        ((source / target) • z) = (a * b)⁻¹ • z := by
  rw [alignment_ratio, ← mul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

theorem normalization_composition {U X : Type*} [CommGroup U] [MulAction U X]
    (a b a' b' : U) (z : X) :
    ((a' * a) * (b' * b))⁻¹ • z = (a' * b')⁻¹ • ((a * b)⁻¹ • z) := by
  rw [← mul_smul, mul_mul_mul_comm, mul_inv_rev, mul_comm ((a * b)⁻¹) ((a' * b')⁻¹)]

end EmbeddedSubgroupTransport

#print axioms EmbeddedSubgroupTransport.alignment_ratio
#print axioms EmbeddedSubgroupTransport.normalize_alignment
#print axioms EmbeddedSubgroupTransport.normalization_composition
