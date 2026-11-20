import EvenP3SingularLiveCrop
import EvenP2CropTransport

namespace Mathproof.EvenOrdinaryTISingular
open scoped Matrix TensorProduct
open Matrix Module EvenTI.Action
noncomputable section

variable {K : Type*} [Field K] {l r n a b : ℕ}

private def liveImageDecode {p d : ℕ} (S : Submodule K (Coord p n → K))
    (f : (Coord p n → K) →ₗ[K] CropMat K d) :
    (Fin (finrank K (cropImage S f)) → K) →ₗ[K] CropMat K d :=
  (cropImage S f).subtype.comp (basisOfCrop (imageFromLeftKernel S) f).symm.toLinearMap

/-- Decoding a sampled live block recovers the literal projections of the
original dense tensor. -/
theorem rawLiveCrop_embedded_eq
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (pL : (Coord l n → K) →ₗ[K] CropMat K a)
    (pR : (Coord r n → K) →ₗ[K] CropMat K b)
    (A : DenseKernelFiber R S) :
    TensorProduct.map (cropImage S pL).subtype (cropImage R pR).subtype
      (rawLiveCrop R S pL pR A) =
      TensorProduct.map pL pR (matrixTensorEquiv K _ _ (flatten A.val)) := by
  let C := coordinateCropMatrix (imageFromLeftKernel S) pL
  let D := coordinateCropMatrix (imageFromLeftKernel R) pR
  let M := flatten A.val
  have hL : M.toLin'.range ≤ imageFromLeftKernel S := by
    have h := range_le_oppositeAnnihilator M
    have hS : Mᵀ.toLin'.ker = S := A.property.2
    rwa [hS] at h
  have hR : Mᵀ.toLin'.range ≤ imageFromLeftKernel R := by
    have h := range_le_oppositeAnnihilator Mᵀ
    have hR : M.toLin'.ker = R := A.property.1
    rwa [Matrix.transpose_transpose, hR] at h
  let e := (LinearEquiv.curry K K (Fin a) (Fin a)).symm
  let f := (LinearEquiv.curry K K (Fin b) (Fin b)).symm
  have hC x (hx : x ∈ M.toLin'.range) :
      liveImageDecode S pL (C.toLin' x) = pL x :=
    coordinateCropMatrix_decodes (imageFromLeftKernel S) pL ⟨x, hL hx⟩
  have hD x (hx : x ∈ Mᵀ.toLin'.range) :
      liveImageDecode R pR (D.toLin' x) = pR x :=
    coordinateCropMatrix_decodes (imageFromLeftKernel R) pR ⟨x, hR hx⟩
  let cL := (basisOfCrop (imageFromLeftKernel S) pL).symm
  let cR := (basisOfCrop (imageFromLeftKernel R) pR).symm
  change ((TensorProduct.map (cropImage S pL).subtype
      (cropImage R pR).subtype).comp (TensorProduct.map cL.toLinearMap cR.toLinearMap))
    (matrixTensorEquiv K _ _ (C * M * Dᵀ)) = _
  rw [← TensorProduct.map_comp]
  exact tensor_crop_decode_eq e f pL pR (liveImageDecode S pL) (liveImageDecode R pR)
    C D M hC hD

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.rawLiveCrop_embedded_eq
