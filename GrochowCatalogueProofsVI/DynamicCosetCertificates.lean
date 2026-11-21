import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Action.Basic

namespace GrochowCatalogueSixth

/-- A common witness translates the intersection of two left cosets to the
    intersection of their stabilizer subgroups. -/
theorem common_coset {G : Type*} [Group G] (H K : Subgroup G) (u v w z : G)
    (hwH : u⁻¹ * w ∈ H) (hwK : v⁻¹ * w ∈ K) :
    (u⁻¹ * z ∈ H ∧ v⁻¹ * z ∈ K) ↔ w⁻¹ * z ∈ H ⊓ K := by
  change (u⁻¹ * z ∈ H ∧ v⁻¹ * z ∈ K) ↔ (w⁻¹ * z ∈ H ∧ w⁻¹ * z ∈ K)
  constructor
  · rintro ⟨hzH, hzK⟩
    constructor
    · simpa [mul_assoc] using H.mul_mem (H.inv_mem hwH) hzH
    · simpa [mul_assoc] using K.mul_mem (K.inv_mem hwK) hzK
  · rintro ⟨hzH, hzK⟩
    constructor
    · simpa [mul_assoc] using H.mul_mem hwH hzH
    · simpa [mul_assoc] using K.mul_mem hwK hzK

/-- An added point-image constraint slices a feasible coset to a translate
    of the remaining point stabilizer. -/
theorem point_constraint {G Ω : Type*} [Group G] [MulAction G Ω]
    (J : Subgroup G) (w g z : G) (x y : Ω) (hg : g ∈ J) (hy : (w * g) • x = y) :
    (∃ j ∈ J, z = w * j ∧ z • x = y) ↔
      ∃ k ∈ J, k • x = x ∧ z = (w * g) * k := by
  constructor
  · rintro ⟨j, hj, rfl, hz⟩
    refine ⟨g⁻¹ * j, J.mul_mem (J.inv_mem hg) hj, ?_, by simp [mul_assoc]⟩
    have eq : (w * g) • ((g⁻¹ * j) • x) = (w * g) • x := by
      rw [← mul_smul, hy]
      simpa [mul_assoc] using hz
    have cancelled := congrArg (fun t : Ω => (w * g)⁻¹ • t) eq
    have back (t : Ω) : (w * g)⁻¹ • ((w * g) • t) = t := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    simpa only [back] using cancelled
  · rintro ⟨k, hk, hfix, rfl⟩
    refine ⟨g * k, J.mul_mem hg hk, mul_assoc w g k, ?_⟩
    rw [mul_smul, hfix, hy]

end GrochowCatalogueSixth

#print axioms GrochowCatalogueSixth.common_coset
#print axioms GrochowCatalogueSixth.point_constraint
