import EvenNextAnchorProjection
import EvenNextAnchorCoordinates
import EvenNextAnchorDense
import EvenNextAnchorRight
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual ranked singular crop in coordinates of the two projected
image subspaces. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module EvenTI.Action
open scoped Matrix
noncomputable section

variable {K : Type*} [Field K] [Fintype K] {l r n : ℕ}

abbrev retainedImageWidth {p : ℕ} (S : Submodule K (Coord (p+1) n → K))
    (i : Fin (p+1)) (ell : Coord (p+1) n → K) : ℕ :=
  finrank K ((imageFromLeftKernel S).map (physicalKernelProjection i ell))

theorem retainedImageWidth_le_square {p : ℕ} (S : Submodule K (Coord (p+1) n → K))
    (i : Fin (p+1)) (ell : Coord (p+1) n → K) :
    retainedImageWidth S i ell ≤ n ^ 2 := by
  have hEnd : finrank K (End K (PhysicalModule K n)) = n ^ 2 := by
    calc
      _ = finrank K (Matrix (Fin n) (Fin n) K) :=
        (LinearMap.toMatrix' :
          End K (PhysicalModule K n) ≃ₗ[K] Matrix (Fin n) (Fin n) K).finrank_eq
      _ = _ := by rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, pow_two]
  exact (Submodule.finrank_le _).trans_eq hEnd

/-- This block uses image bases, so its coordinates describe the projection
to the smaller tensor product, including forms with nontrivial radicals. -/
def physicalPairCrop
    (R : Submodule K (Coord (r+1) n → K)) (S : Submodule K (Coord (l+1) n → K))
    (i : Fin (l+1)) (j : Fin (r+1)) (ell : Coord (l+1) n → K) (rho : Coord (r+1) n → K)
    (A : Tensor K ((l+1)+(r+1)) n) :
    Matrix (Fin (retainedImageWidth S i ell)) (Fin (retainedImageWidth R j rho)) K :=
  coordinateCropMatrix (imageFromLeftKernel S) (physicalKernelProjection i ell) *
    flatten A *
    (coordinateCropMatrix (imageFromLeftKernel R) (physicalKernelProjection j rho))ᵀ

/-- Conditional crop error on the literal dense tensor fiber, with no
independence or surjectivity premises for the chosen coordinate matrices.
These are consequences of choosing bases of the restricted images. -/
theorem uniformFraction_physicalPairCrop
    (R : Submodule K (Coord (r+1) n → K)) (S : Submodule K (Coord (l+1) n → K))
    (i : Fin (l+1)) (j : Fin (r+1)) (ell : Coord (l+1) n → K) (rho : Coord (r+1) n → K)
    (A₀ : DenseKernelFiber R S)
    (P : Matrix (Fin (retainedImageWidth S i ell)) (Fin (retainedImageWidth R j rho)) K → Prop) :
    |uniformFraction (DenseKernelFiber R S) (fun A => P (physicalPairCrop R S i j ell rho A.val)) -
      uniformFraction (Matrix (Fin (retainedImageWidth S i ell))
        (Fin (retainedImageWidth R j rho)) K) P| ≤
      ((Fintype.card K : ℝ)^(retainedImageWidth R j rho) - 1) /
        ((Fintype.card K : ℝ)^(finrank K ((Coord (r+1) n → K) ⧸ R)) *
          ((Fintype.card K : ℝ) - 1)) := by
  let C := coordinateCropMatrix (imageFromLeftKernel S) (physicalKernelProjection i ell)
  let D := coordinateCropMatrix (imageFromLeftKernel R) (physicalKernelProjection j rho)
  let b := retainedImageWidth R j rho
  have hD : Function.Surjective (D.toLin'.comp (imageFromLeftKernel R).subtype) :=
    coordinateCropMatrix_surjective _ _
  have hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype) :=
    coordinateCropMatrix_surjective _ _
  have hind := independent_rows_mod_kernel_of_surjective R D hD
  have hb : b ≤ finrank K ((Coord (r+1) n → K) ⧸ R) := by
    simpa only [Fintype.card_fin] using hind.fintype_card_le_finrank
  let t := finrank K ((Coord (r+1) n → K) ⧸ R) - b
  have hR : b+t = finrank K ((Coord (r+1) n → K) ⧸ R) := Nat.add_sub_of_le hb
  have hA₀ : MatrixKernelFiber R (coordinateLeftKernel (imageFromLeftKernel S)) :=
    ⟨flatten A₀.val, A₀.property.1,
      A₀.property.2.trans (coordinateLeftKernel_imageFromLeftKernel S).symm⟩
  let e := toKernelRangeEquiv R (imageFromLeftKernel S)
    (twoKernelsEquiv R (imageFromLeftKernel S)
      (matrixTwoKernelsEquiv R (imageFromLeftKernel S) hA₀))
  have hL : b+t = finrank K (imageFromLeftKernel S) := hR.trans e.finrank_eq
  have hCrop := uniformFraction_denseKernel_crop R S C D hind hR hL hC P
  change |uniformFraction (DenseKernelFiber R S) (fun A => P (C * flatten A.val * Dᵀ)) -
    uniformFraction (Matrix (Fin (retainedImageWidth S i ell)) (Fin b) K) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(b+t) * ((Fintype.card K : ℝ) - 1)) at hCrop
  rw [hR] at hCrop
  exact hCrop

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.retainedImageWidth_le_square
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_physicalPairCrop
