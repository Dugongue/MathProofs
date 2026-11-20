import TracePairing
import TensorEscape
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Bilinear

namespace Mathproof.Problem17PolarAssembly
open scoped TensorProduct Matrix
open Module LinearMap
open Matrix
open Mathproof.Problem17TracePairing
open Mathproof.Problem17TensorEscape Mathproof.Problem17Anticommutator

section General
variable {K V W : Type*} [Field K]
variable [AddCommMonoid V] [Module K V] [Module.Finite K V]
variable [AddCommMonoid W] [Module K W] [Module.Finite K W]

set_option maxHeartbeats 800000 in
theorem rank_pullback_le (B : LinearMap.BilinForm K V) (e : W →ₗ[K] V) :
    finrank K (B.compl₁₂ e e).range ≤ finrank K B.range := by
  let post : Module.Dual K V →ₗ[K] Module.Dual K W := LinearMap.lcomp K K e
  have he : B.compl₁₂ e e = post.comp (LinearMap.comp B e) := by
    apply LinearMap.ext fun x => ?_
    apply LinearMap.ext fun y => ?_
    rfl
  rw [he]
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

theorem rank_pullback_equiv (B : LinearMap.BilinForm K V) (e : W ≃ₗ[K] V) :
    finrank K (B.compl₁₂ e.toLinearMap e.toLinearMap).range = finrank K B.range := by
  apply le_antisymm (rank_pullback_le _ _)
  have h := rank_pullback_le (B.compl₁₂ e.toLinearMap e.toLinearMap) e.symm.toLinearMap
  have he : (B.compl₁₂ e.toLinearMap e.toLinearMap).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap = B := by
    ext x y
    simp
  rwa [he] at h

theorem rank_comp_pairing (E : V ≃ₗ[K] W) (f : End K V) :
    finrank K (E.toLinearMap.comp f).range = finrank K f.range := by
  rw [LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq E _

end General

section Pairings
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

noncomputable def pairingProject (B : LinearMap.BilinForm K V)
    (S : Submodule K V) (h : (B.restrict S).Nondegenerate) : V →ₗ[K] S :=
  ((B.restrict S).toDual h).symm.toLinearMap.comp (B.compl₂ S.subtype)

theorem pairingProject_pair (B : LinearMap.BilinForm K V)
    (S : Submodule K V) (h : (B.restrict S).Nondegenerate) (x : V) (y : S) :
    B (pairingProject B S h x).val y.val = B x y.val := by
  have he := ((B.restrict S).toDual h).apply_symm_apply (B.compl₂ S.subtype x)
  exact LinearMap.congr_fun he y

theorem pairingProject_split (B : LinearMap.BilinForm K V)
    (S : Submodule K V) (h : (B.restrict S).Nondegenerate) :
    (pairingProject B S h).comp S.subtype = LinearMap.id := by
  apply LinearMap.ext fun x => ?_
  apply ((B.restrict S).toDual h).injective
  ext y
  exact pairingProject_pair B S h x.val y

noncomputable def tensorPairing (B : LinearMap.BilinForm K V) (D : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (hD : D.Nondegenerate) : V ⊗[K] W ≃ₗ[K] Module.Dual K (V ⊗[K] W) :=
  (TensorProduct.congr (B.toDual hB) (D.toDual hD)).trans (TensorProduct.dualDistribEquiv K V W)

theorem tensorPairing_tmul (B : LinearMap.BilinForm K V) (D : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (hD : D.Nondegenerate) (x x' : V) (y y' : W) :
    tensorPairing B D hB hD (x ⊗ₜ[K] y) (x' ⊗ₜ[K] y') = B x x' * D y y' := by
  simp [tensorPairing, TensorProduct.dualDistribEquiv, TensorProduct.dualDistribEquivOfBasis,
    TensorProduct.dualDistrib_apply, LinearMap.BilinForm.toDual_def]

end Pairings

section Matrix
variable {K i j : Type*} [Field K] [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]

abbrev Mat (K : Type*) (i : Type*) := Matrix i i K

def matAnti (P : Mat K i) : End K (Mat K i) :=
  LinearMap.mulLeft K P + LinearMap.mulRight K P

theorem matAnti_apply (P X : Mat K i) : matAnti P X = P * X + X * P := rfl

theorem matAnti_escape (P : Mat K i) (hP : ∀ c : K, P ≠ c • (1 : Mat K i)) :
    ∃ (a : Module.Dual K (i → K) →ₗ[K] Mat K i) (b : Mat K i →ₗ[K] Module.Dual K (i → K)),
      b.comp a = 0 ∧ b.comp ((matAnti P).comp a) = LinearMap.id := by
  let E : Mat K i ≃ₐ[K] End K (i → K) := Matrix.toLinAlgEquiv'
  have hEP : ∀ c : K, E P ≠ c • LinearMap.id := by
    intro c h
    apply hP c
    apply E.injective
    have h1 : E (1 : Mat K i) = LinearMap.id := map_one E
    simpa only [map_smul, h1] using h
  obtain ⟨v, hv⟩ := exists_outside_line (E P) hEP
  obtain ⟨a, b, hk, hr⟩ := shifted_escape (E P) 0 v hv
  refine ⟨E.symm.toLinearEquiv.toLinearMap.comp a, b.comp E.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · apply LinearMap.ext fun x => ?_
    apply LinearMap.ext fun y => ?_
    have h := LinearMap.congr_fun hk x
    change (b (E (E.symm (a x)))) y = 0
    simpa using congrArg (fun l : Module.Dual K (i → K) => l y) h
  · apply LinearMap.ext fun x => ?_
    apply LinearMap.ext fun y => ?_
    have he (X : Mat K i) : E (matAnti P X) = shifted (E P) 0 (E X) := by
      change E (P * X + X * P) = _
      rw [map_add, map_mul, map_mul]
      simp [shifted]
      rfl
    change (b (E (matAnti P (E.symm (a x))))) y = x y
    rw [he, E.apply_symm_apply]
    exact congrArg (fun l : Module.Dual K (i → K) => l y) (LinearMap.congr_fun hr x)

theorem rank_compressed_matAnti (P : Mat K i) (hP : ∀ c : K, P ≠ c • (1 : Mat K i))
    (S : Submodule K (Mat K i)) (T : Submodule K (Mat K j)) (M : End K T)
    (p : Mat K i →ₗ[K] S) (hp : p.comp S.subtype = LinearMap.id) :
    (Fintype.card i - 2 * finrank K (Mat K i ⧸ S)) * finrank K T ≤
      finrank K (tensorSum (p.comp ((matAnti P).comp S.subtype)) M).range := by
  obtain ⟨a, b, hk, hr⟩ := matAnti_escape P hP
  have h := compressed_tensorSum_rank_ge (matAnti P) M a b hk hr S p hp
  simpa only [Subspace.dual_finrank_eq, Module.finrank_pi, Module.finrank_self, mul_one] using h

end Matrix
end Mathproof.Problem17PolarAssembly

#print axioms Mathproof.Problem17PolarAssembly.rank_compressed_matAnti








