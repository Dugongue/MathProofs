import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dual.Defs

open scoped TensorProduct

namespace LinearSignature

theorem preserve_product_forces_map
    {K V W V' W' : Type*} [CommSemiring K]
    [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid V'] [AddCommMonoid W']
    [Module K V] [Module K W] [Module K V'] [Module K W']
    (g : V →ₗ[K] V') (h : W →ₗ[K] W')
    (lift : V ⊗[K] W →ₗ[K] V' ⊗[K] W')
    (commutes : ∀ v w, lift (v ⊗ₜ[K] w) = g v ⊗ₜ[K] h w) :
    lift = TensorProduct.map g h := by
  apply TensorProduct.ext'
  intro v w
  rw [TensorProduct.map_tmul]
  exact commutes v w

theorem preserve_pairing_forces_dual
    {K V V' : Type*} [CommSemiring K]
    [AddCommMonoid V] [AddCommMonoid V'] [Module K V] [Module K V']
    (g : V ≃ₗ[K] V')
    (h : Module.Dual K V →ₗ[K] Module.Dual K V')
    (commutes : ∀ (f : Module.Dual K V) v, (h f) (g v) = f v)
    (f : Module.Dual K V) :
    h f = f.comp g.symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  simpa using commutes f (g.symm v)

end LinearSignature
