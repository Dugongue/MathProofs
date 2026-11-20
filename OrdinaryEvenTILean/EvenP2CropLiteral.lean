import EvenP2CropTransport

namespace Mathproof.EvenOrdinaryTISingular
open scoped Matrix TensorProduct
open Matrix Module EvenTI.Action
noncomputable section
variable {K : Type*} [Field K] {l r n : ℕ}

abbrev PhysicalMatrix (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K

def physicalMatrixProjection (i : Fin (l + 1)) (ell : Coord (l + 1) n → K) :
    (Coord (l + 1) n → K) →ₗ[K] PhysicalMatrix K n :=
  (physicalEndMatrix K n).toLinearMap.comp (physicalKernelProjection i ell)

/-- The literal physical projection applies the two kernel contractions to
the dense input, in the standard matrix coordinates on the physical modes. -/
def literalSingularProjection
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : Tensor K ((l + 1) + (r + 1)) n) :
    PhysicalMatrix K n ⊗[K] PhysicalMatrix K n :=
  TensorProduct.map (physicalMatrixProjection i ell) (physicalMatrixProjection j rho)
    (matrixTensorEquiv K _ _ (flatten A))

private def imageDecodeMap
    (S : Submodule K (Coord (l + 1) n → K)) (i : Fin (l + 1))
    (ell : Coord (l + 1) n → K) :
    (Fin (retainedImageWidth S i ell) → K) →ₗ[K] PhysicalMatrix K n :=
  (physicalMatrixImage S i ell).subtype.comp (imageTensorCoordinates S i ell).toLinearMap

private theorem imageDecodeMap_apply_crop
    (S : Submodule K (Coord (l + 1) n → K)) (i : Fin (l + 1))
    (ell : Coord (l + 1) n → K) (x : imageFromLeftKernel S) :
    imageDecodeMap S i ell
        ((coordinateCropMatrix (imageFromLeftKernel S) (physicalKernelProjection i ell)).toLin' x.val) =
      physicalMatrixProjection i ell x.val := by
  exact congrArg (physicalEndMatrix K n)
    (coordinateCropMatrix_decodes (imageFromLeftKernel S) (physicalKernelProjection i ell) x)

/-- Interpreting the small coordinate crop in ambient matrix coordinates
recovers the literal projection. Hence the crop estimate applies to the
square and partial traces of the actual projected tensor. -/
theorem rawSingularCrop_embedded_eq
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : DenseKernelFiber R S) :
    TensorProduct.map (physicalMatrixImage S i ell).subtype
        (physicalMatrixImage R j rho).subtype (rawSingularCrop R S i j ell rho A) =
      literalSingularProjection i j ell rho A.val := by
  let C := coordinateCropMatrix (imageFromLeftKernel S) (physicalKernelProjection i ell)
  let D := coordinateCropMatrix (imageFromLeftKernel R) (physicalKernelProjection j rho)
  let M := flatten A.val
  have hL : M.toLin'.range ≤ imageFromLeftKernel S := by
    have h := range_le_oppositeAnnihilator M
    have hS : Mᵀ.toLin'.ker = S := A.property.2
    rw [hS] at h
    exact h
  have hR : Mᵀ.toLin'.range ≤ imageFromLeftKernel R := by
    have h := range_le_oppositeAnnihilator Mᵀ
    have hR : M.toLin'.ker = R := A.property.1
    rwa [Matrix.transpose_transpose, hR] at h
  let e := (LinearEquiv.curry K K (Fin n) (Fin n)).symm
  have hC x (hx : x ∈ M.toLin'.range) :
      imageDecodeMap S i ell (C.toLin' x) = physicalMatrixProjection i ell x :=
    imageDecodeMap_apply_crop S i ell ⟨x, hL hx⟩
  have hD x (hx : x ∈ Mᵀ.toLin'.range) :
      imageDecodeMap R j rho (D.toLin' x) = physicalMatrixProjection j rho x :=
    imageDecodeMap_apply_crop R j rho ⟨x, hR hx⟩
  let cL := imageTensorCoordinates S i ell
  let cR := imageTensorCoordinates R j rho
  change ((TensorProduct.map (physicalMatrixImage S i ell).subtype
      (physicalMatrixImage R j rho).subtype).comp (TensorProduct.map cL.toLinearMap cR.toLinearMap))
    (matrixTensorEquiv K _ _ (C * M * Dᵀ)) = _
  rw [← TensorProduct.map_comp]
  exact tensor_crop_decode_eq e e (physicalMatrixProjection i ell) (physicalMatrixProjection j rho)
    (imageDecodeMap S i ell) (imageDecodeMap R j rho) C D M hC hD

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.rawSingularCrop_embedded_eq
