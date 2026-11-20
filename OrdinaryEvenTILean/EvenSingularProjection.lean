import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

namespace Mathproof.EvenOrdinaryTISingular

open Module LinearMap
open scoped TensorProduct

noncomputable section

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Keep the physical vector and use the kernel form to turn the bundle
coordinate into a physical covector. -/
def kernelProjection (ell : Module.Dual K (V ⊗[K] W)) : V ⊗[K] W →ₗ[K] End K V :=
  (dualTensorHom K V V).comp
    ((TensorProduct.comm K V (Module.Dual K V)).toLinearMap.comp
      (TensorProduct.map LinearMap.id (TensorProduct.curry ell).flip))

theorem kernelProjection_tmul (ell : Module.Dual K (V ⊗[K] W)) (v : V) (w : W) (x : V) :
    kernelProjection ell (v ⊗ₜ[K] w) x = ell (x ⊗ₜ[K] w) • v := by
  simp [kernelProjection, dualTensorHom_apply, TensorProduct.curry_apply]

theorem kernelProjection_surjective [Module.Finite K V] (ell : Module.Dual K (V ⊗[K] W))
    (hell : Function.Surjective (TensorProduct.curry ell).flip) :
    Function.Surjective (kernelProjection ell) :=
  (dualTensorHomEquiv K V V).surjective.comp <|
    (TensorProduct.comm K V (Module.Dual K V)).surjective.comp <|
      TensorProduct.map_surjective (fun x => ⟨x, rfl⟩) hell

theorem kernelProjection_trace [Module.Finite K V] (ell : Module.Dual K (V ⊗[K] W)) :
    (LinearMap.trace K V).comp (kernelProjection ell) = ell := by
  apply TensorProduct.ext'
  intro v w
  have h : kernelProjection ell (v ⊗ₜ[K] w) = ((TensorProduct.curry ell).flip w).smulRight v := by
    ext x
    simp [kernelProjection_tmul, TensorProduct.curry_apply]
  change LinearMap.trace K V (kernelProjection ell (v ⊗ₜ[K] w)) = ell (v ⊗ₜ[K] w)
  rw [h, LinearMap.trace_smulRight]
  rfl

theorem kernelProjection_covariant (ell : Module.Dual K (V ⊗[K] W))
    (g : V ≃ₗ[K] V) (h : W ≃ₗ[K] W) :
    ∀ z : V ⊗[K] W,
      kernelProjection (ell.comp (TensorProduct.map g.symm.toLinearMap h.symm.toLinearMap))
          (TensorProduct.map g.toLinearMap h.toLinearMap z) =
        g.toLinearMap.comp ((kernelProjection ell z).comp g.symm.toLinearMap) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | tmul v w =>
    ext x
    simp [kernelProjection_tmul, map_smul]

private theorem finrank_quotient_map_le {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [Module.Finite K X]
    (f : X →ₗ[K] Y) (hf : Function.Surjective f) (P : Submodule K X) :
    finrank K (Y ⧸ P.map f) ≤ finrank K (X ⧸ P) := by
  let q := P.mapQ (P.map f) f (fun x hx => ⟨x, hx, rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (P.map f) y
    obtain ⟨x, rfl⟩ := hf y
    refine ⟨P.mkQ x, ?_⟩
    exact P.mapQ_apply (P.map f) f x
  exact LinearMap.finrank_le_finrank_of_surjective hq

/-- For a full-row-rank kernel form, projecting the annihilator of the kernel
space gives a trace-zero subspace with no increase of codimension. -/
theorem kernelProjection_annihilator_image [Module.Finite K V] [Module.Finite K W]
    (ell : Module.Dual K (V ⊗[K] W)) (hell : Function.Surjective (TensorProduct.curry ell).flip)
    (P : Submodule K (V ⊗[K] W)) (hP : P ≤ ell.ker) :
    P.map (kernelProjection ell) ≤ (LinearMap.trace K V).ker ∧
      finrank K (End K V ⧸ P.map (kernelProjection ell)) ≤ finrank K ((V ⊗[K] W) ⧸ P) := by
  refine ⟨?_, finrank_quotient_map_le _ (kernelProjection_surjective ell hell) _⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (LinearMap.congr_fun (kernelProjection_trace ell) z).trans (hP hz)

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.kernelProjection_surjective
#print axioms Mathproof.EvenOrdinaryTISingular.kernelProjection_covariant
#print axioms Mathproof.EvenOrdinaryTISingular.kernelProjection_annihilator_image
