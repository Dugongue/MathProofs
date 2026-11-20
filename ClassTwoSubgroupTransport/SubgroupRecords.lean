import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

namespace ClassTwoSubgroupTransport

variable {F : Type*} [Field F]
variable {A B W : Type*}
variable [AddCommGroup A] [Module F A]
variable [AddCommGroup B] [Module F B]
variable [AddCommGroup W] [Module F W]

theorem common_linear_correction (p : B →ₗ[F] A) (d : B →ₗ[F] W) :
    (∃ s : A →ₗ[F] W, s.comp p = d) ↔
      ∀ b, p b = 0 → d b = 0 := by
  constructor
  · rintro ⟨s, rfl⟩ b hb
    change s (p b) = 0
    rw [hb, map_zero]
  · intro h
    have hker : LinearMap.ker p ≤ LinearMap.ker d := fun b hb => h b hb
    let q := (LinearMap.ker p).liftQ d hker
    obtain ⟨s, hs⟩ := (q.comp p.quotKerEquivRange.symm.toLinearMap).exists_extend
    refine ⟨s, ?_⟩
    ext b
    have hb : p b ∈ LinearMap.range p := LinearMap.mem_range_self _ _
    have hz := LinearMap.congr_fun hs ⟨p b, hb⟩
    change s (p b) = q (p.quotKerEquivRange.symm ⟨p b, hb⟩) at hz
    have he := p.quotKerEquivRange_symm_apply_image b hb
    exact hz.trans (congrArg q he)

theorem triangle_correction (U V Z : Submodule F A)
    (d₁ : U →ₗ[F] W) (d₂ : V →ₗ[F] W) (d₃ : Z →ₗ[F] W) :
    (∃ x y : A →ₗ[F] W,
      (∀ u : U, y u = d₁ u) ∧ (∀ v : V, x v = d₂ v) ∧
        (∀ z : Z, x z + y z = d₃ z)) ↔
      ∀ (z : Z) (hu : (z : A) ∈ U) (hv : (z : A) ∈ V),
        d₁ ⟨z, hu⟩ + d₂ ⟨z, hv⟩ = d₃ z := by
  constructor
  · rintro ⟨x, y, hx, hy, hz⟩ z hu hv
    rw [← hx ⟨z, hu⟩, ← hy ⟨z, hv⟩, add_comm]
    exact hz z
  · intro h
    let pU : U × (V × Z) →ₗ[F] U := LinearMap.fst F U (V × Z)
    let pV : U × (V × Z) →ₗ[F] V :=
      (LinearMap.fst F V Z).comp (LinearMap.snd F U (V × Z))
    let pZ : U × (V × Z) →ₗ[F] Z :=
      (LinearMap.snd F V Z).comp (LinearMap.snd F U (V × Z))
    let p : U × (V × Z) →ₗ[F] A × A :=
      (V.subtype.comp pV + Z.subtype.comp pZ).prod
        (U.subtype.comp pU + Z.subtype.comp pZ)
    let d : U × (V × Z) →ₗ[F] W := d₁.comp pU + d₂.comp pV + d₃.comp pZ
    obtain ⟨s, hs⟩ := (common_linear_correction p d).mpr (by
      rintro ⟨u, v, z⟩ hz
      change ((v : A) + z, (u : A) + z) = (0, 0) at hz
      have hu : (u : A) = -(z : A) := eq_neg_of_add_eq_zero_left (congrArg Prod.snd hz)
      have hv : (v : A) = -(z : A) := eq_neg_of_add_eq_zero_left (congrArg Prod.fst hz)
      have hzu : (z : A) ∈ U := by rw [← neg_neg (z : A), ← hu]; exact U.neg_mem u.property
      have hzv : (z : A) ∈ V := by rw [← neg_neg (z : A), ← hv]; exact V.neg_mem v.property
      have eu : u = -(⟨z, hzu⟩ : U) := Subtype.ext hu
      have ev : v = -(⟨z, hzv⟩ : V) := Subtype.ext hv
      change d₁ u + d₂ v + d₃ z = 0
      rw [eu, ev, map_neg, map_neg, ← h z hzu hzv]
      abel)
    let x := s.comp (LinearMap.inl F A A)
    let y := s.comp (LinearMap.inr F A A)
    refine ⟨x, y, ?_, ?_, ?_⟩
    · intro u
      simpa [d, p, pU, pV, pZ, y] using LinearMap.congr_fun hs (u, 0, 0)
    · intro v
      simpa [d, p, pU, pV, pZ, x] using LinearMap.congr_fun hs (0, v, 0)
    · intro z
      have hz : s ((z : A), (z : A)) = d₃ z := by
        simpa [d, p, pU, pV, pZ] using LinearMap.congr_fun hs (0, 0, z)
      change s ((z : A), 0) + s (0, (z : A)) = d₃ z
      rw [← map_add]
      simpa using hz

#print axioms common_linear_correction
#print axioms triangle_correction

end ClassTwoSubgroupTransport
