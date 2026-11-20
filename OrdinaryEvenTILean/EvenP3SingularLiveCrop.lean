import EvenP3SingularCropLaw
import EvenNextAnchorProjection
import EvenNextAnchorCoordinates
import EvenNextAnchorRight
import EvenP2CropTensor

namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module EvenTI.Action
open scoped Matrix TensorProduct
noncomputable section

variable {K : Type*} [Field K] {l r n a b : ℕ}
abbrev CropMat (K : Type*) (a : ℕ) := Matrix (Fin a) (Fin a) K

abbrev cropImage {p d : ℕ} (S : Submodule K (Coord p n → K))
    (P : (Coord p n → K) →ₗ[K] CropMat K d) :=
  (imageFromLeftKernel S).map P

/-- The live cut expressed in bases of the two projected annihilators. -/
def livePairCrop
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (pL : (Coord l n → K) →ₗ[K] CropMat K a)
    (pR : (Coord r n → K) →ₗ[K] CropMat K b)
    (A : Tensor K (l+r) n) :
    Matrix (Fin (finrank K (cropImage S pL))) (Fin (finrank K (cropImage R pR))) K :=
  coordinateCropMatrix (imageFromLeftKernel S) pL *
    flatten A *
    (coordinateCropMatrix (imageFromLeftKernel R) pR)ᵀ

def liveCropImageEquiv
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (pL : (Coord l n → K) →ₗ[K] CropMat K a)
    (pR : (Coord r n → K) →ₗ[K] CropMat K b) :
    Matrix (Fin (finrank K (cropImage S pL))) (Fin (finrank K (cropImage R pR))) K ≃ₗ[K]
      (cropImage S pL ⊗[K] cropImage R pR) :=
  (matrixTensorEquiv K _ _).trans
    (TensorProduct.congr (basisOfCrop (imageFromLeftKernel S) pL).symm
      (basisOfCrop (imageFromLeftKernel R) pR).symm)

def rawLiveCrop
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (pL : (Coord l n → K) →ₗ[K] CropMat K a)
    (pR : (Coord r n → K) →ₗ[K] CropMat K b) (A : DenseKernelFiber R S) :
    cropImage S pL ⊗[K] cropImage R pR :=
  liveCropImageEquiv R S pL pR (livePairCrop R S pL pR A.val)

theorem cropImage_trace_codim {p d : ℕ} (S : Submodule K (Coord p n → K))
    (ell : Coord p n → K) (hell : ell ∈ S)
    (f : (Coord p n → K) →ₗ[K] CropMat K d) (hf : Function.Surjective f)
    (htrace : (Matrix.traceLinearMap (α := K) (Fin d) K).comp f = dotProductEquiv K _ ell) :
    cropImage S f ≤ (Matrix.traceLinearMap (α := K) (Fin d) K).ker ∧
      finrank K (CropMat K d ⧸ cropImage S f) ≤ finrank K S := by
  let L := imageFromLeftKernel S
  refine ⟨?_,?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change ((Matrix.traceLinearMap (α := K) (Fin d) K).comp f) x = 0
    rw [htrace]
    exact (Submodule.mem_dualCoannihilator x).mp hx _
      (Submodule.mem_map.mpr ⟨ell, hell, rfl⟩)
  · let q := L.mapQ (L.map f) f (fun x hx => ⟨x, hx, rfl⟩)
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (L.map f) y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨L.mkQ x, L.mapQ_apply (L.map f) f x⟩
    exact (LinearMap.finrank_le_finrank_of_surjective hq).trans_eq
      (finrank_imageFromLeftKernel_quotient S)

variable [Fintype K]

/-- The full exact kernel fiber is dominated by four times the uniform law
on the actual live tensor product, with no assumption on either rank. -/
theorem uniformFraction_rawLiveCrop_le_four
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (pL : (Coord l n → K) →ₗ[K] CropMat K a)
    (pR : (Coord r n → K) →ₗ[K] CropMat K b)
    (A₀ : DenseKernelFiber R S) (P : cropImage S pL ⊗[K] cropImage R pR → Prop) :
    uniformFraction (DenseKernelFiber R S) (fun A => P (rawLiveCrop R S pL pR A)) ≤
      4 * uniformFraction (cropImage S pL ⊗[K] cropImage R pR) P := by
  let C := coordinateCropMatrix (imageFromLeftKernel S) pL
  let D := coordinateCropMatrix (imageFromLeftKernel R) pR
  let w := finrank K (cropImage R pR)
  have hD : Function.Surjective (D.toLin'.comp (imageFromLeftKernel R).subtype) :=
    coordinateCropMatrix_surjective _ _
  have hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype) :=
    coordinateCropMatrix_surjective _ _
  have hind := independent_rows_mod_kernel_of_surjective R D hD
  have hw : w ≤ finrank K ((Coord r n → K) ⧸ R) := by
    simpa only [Fintype.card_fin] using hind.fintype_card_le_finrank
  let t := finrank K ((Coord r n → K) ⧸ R) - w
  have hR : w+t = finrank K ((Coord r n → K) ⧸ R) := Nat.add_sub_of_le hw
  have hA₀ : MatrixKernelFiber R (coordinateLeftKernel (imageFromLeftKernel S)) :=
    ⟨flatten A₀.val, A₀.property.1,
      A₀.property.2.trans (coordinateLeftKernel_imageFromLeftKernel S).symm⟩
  let e := toKernelRangeEquiv R (imageFromLeftKernel S)
    (twoKernelsEquiv R (imageFromLeftKernel S)
      (matrixTwoKernelsEquiv R (imageFromLeftKernel S) hA₀))
  have hL : w+t = finrank K (imageFromLeftKernel S) := hR.trans e.finrank_eq
  let E := liveCropImageEquiv R S pL pR
  have h := uniformFraction_denseKernel_crop_le_four R S C D hind hR hL hC (fun A => P (E A))
  have hE : uniformFraction _ (fun A => P (E A)) = uniformFraction _ P :=
    uniformFraction_equiv E.toEquiv P
  rw [hE] at h
  exact h

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.cropImage_trace_codim
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_rawLiveCrop_le_four
