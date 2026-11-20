import EvenNextAnchorMatrix
import EvenFlattening
import EvenSingularProjection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The singular projection associated to one actual dense coordinate kernel
form and one physical mode. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module LinearMap EvenTI.Action
open scoped TensorProduct
noncomputable section

variable {K : Type*} [Field K] {l n : ℕ}

abbrev PhysicalModule (K : Type*) (n : ℕ) := Fin n → K
abbrev BundleModule (K : Type*) (l n : ℕ) := Coord l n → K

/-- Regroup one physical mode separately from all other modes on its cut side. -/
def regroupCoordinates (i : Fin (l+1)) :
    (Coord (l+1) n → K) ≃ₗ[K]
      (PhysicalModule K n ⊗[K] BundleModule K l n) :=
  (LinearEquiv.funCongrLeft K K (retainedMode i)).trans
    ((Pi.basisFun K (Fin n)).tensorProduct (Pi.basisFun K (Coord l n))).equivFun.symm

/-- The linear functional represented by the chosen dense kernel row, in
the regrouped coordinates. -/
def regroupKernelForm (i : Fin (l+1)) (ell : Coord (l+1) n → K) :
    Dual K (PhysicalModule K n ⊗[K] BundleModule K l n) :=
  (dotProductEquiv K _ ell).comp (regroupCoordinates i).symm.toLinearMap

/-- The singular-anchor projection of the selected physical mode. -/
def physicalKernelProjection (i : Fin (l+1)) (ell : Coord (l+1) n → K) :
    (Coord (l+1) n → K) →ₗ[K] End K (PhysicalModule K n) :=
  (kernelProjection (regroupKernelForm i ell)).comp (regroupCoordinates i).toLinearMap

theorem physicalKernelProjection_surjective (i : Fin (l+1)) (ell : Coord (l+1) n → K)
    (h : Function.Surjective (TensorProduct.curry (regroupKernelForm i ell)).flip) :
    Function.Surjective (physicalKernelProjection i ell) :=
  (kernelProjection_surjective _ h).comp (regroupCoordinates i).surjective

theorem kernelRow_vanishes_on_image {S : Submodule K (Coord (l+1) n → K)}
    {ell : Coord (l+1) n → K} (hell : ell ∈ S) (x : imageFromLeftKernel S) :
    dotProductEquiv K _ ell x.val = 0 :=
  (Submodule.mem_dualCoannihilator x.val).mp x.property _
    (Submodule.mem_map.mpr ⟨ell, hell, rfl⟩)

theorem finrank_imageFromLeftKernel_quotient {M : Type*} [Fintype M] [DecidableEq M]
    (S : Submodule K (M → K)) : finrank K ((M → K) ⧸ imageFromLeftKernel S) = finrank K S := by
  have h1 := Submodule.finrank_quotient_add_finrank (imageFromLeftKernel S)
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (S.map (dotProductEquiv K M).toLinearMap)
  have h3 := LinearEquiv.finrank_map_eq (dotProductEquiv K M) S
  change finrank K (S.map (dotProductEquiv K M).toLinearMap) +
    finrank K (imageFromLeftKernel S) = finrank K (M → K) at h2
  omega

/-- For an exact kernel row of full contraction rank, the physical crop of
the opposite annihilator is trace zero and loses at most the original
coordinate-kernel dimension. -/
theorem physicalKernelProjection_trace_codim
    (i : Fin (l+1)) (S : Submodule K (Coord (l+1) n → K)) (ell : Coord (l+1) n → K)
    (hell : ell ∈ S)
    (hs : Function.Surjective (TensorProduct.curry (regroupKernelForm i ell)).flip) :
    (imageFromLeftKernel S).map (physicalKernelProjection i ell) ≤
        (LinearMap.trace K (PhysicalModule K n)).ker ∧
      finrank K (End K (PhysicalModule K n) ⧸
        (imageFromLeftKernel S).map (physicalKernelProjection i ell)) ≤ finrank K S := by
  letI : Module.Finite K (PhysicalModule K n ⊗[K] BundleModule K l n) :=
    Module.Finite.of_basis ((Pi.basisFun K (Fin n)).tensorProduct (Pi.basisFun K (Coord l n)))
  let E := regroupCoordinates (K := K) (n := n) i
  let L := imageFromLeftKernel S
  have hz : L.map E.toLinearMap ≤ (regroupKernelForm i ell).ker := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change (dotProductEquiv K _ ell) (E.symm (E x)) = 0
    rw [E.symm_apply_apply]
    exact kernelRow_vanishes_on_image hell (⟨x, hx⟩ : L)
  have h := kernelProjection_annihilator_image (regroupKernelForm i ell) hs _ hz
  change L.map ((kernelProjection (regroupKernelForm i ell)).comp E.toLinearMap) ≤ _ ∧
    finrank K (End K (PhysicalModule K n) ⧸
      L.map ((kernelProjection (regroupKernelForm i ell)).comp E.toLinearMap)) ≤ _
  rw [Submodule.map_comp]
  refine ⟨h.1, h.2.trans_eq ?_⟩
  calc
    _ = finrank K ((Coord (l+1) n → K) ⧸ L) := by
      have hSrc := Submodule.finrank_quotient_add_finrank L
      have hDst := Submodule.finrank_quotient_add_finrank (L.map E.toLinearMap)
      have hMap := LinearEquiv.finrank_map_eq E L
      have hDim := E.finrank_eq
      omega
    _ = _ := finrank_imageFromLeftKernel_quotient S

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.physicalKernelProjection_surjective
#print axioms Mathproof.EvenOrdinaryTISingular.physicalKernelProjection_trace_codim
