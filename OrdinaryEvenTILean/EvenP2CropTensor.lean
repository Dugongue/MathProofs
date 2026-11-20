import EvenP2CropBound
import EvenNextAnchorFullRank

namespace Mathproof.EvenOrdinaryTISingular
open scoped Matrix TensorProduct
open Matrix Module EvenTI.Action
noncomputable section
variable {K : Type*} [Field K] {l r n : ℕ}

def physicalEndMatrix (K : Type*) [Field K] (n : ℕ) :
    End K (PhysicalModule K n) ≃ₗ[K] Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix (Pi.basisFun K _) (Pi.basisFun K _)

def physicalMatrixImage
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (ell : Coord (l + 1) n → K) :
    Submodule K (Matrix (Fin n) (Fin n) K) :=
  ((imageFromLeftKernel S).map (physicalKernelProjection i ell)).map
    (physicalEndMatrix K n).toLinearMap

theorem physicalMatrixImage_trace_codim
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (ell : Coord (l + 1) n → K)
    (hell : ell ∈ S) (h : (retainedForm i ell).rank = n) :
    physicalMatrixImage S i ell ≤ (Matrix.traceLinearMap (α := K) (Fin n) K).ker ∧
      finrank K (Matrix (Fin n) (Fin n) K ⧸ physicalMatrixImage S i ell) ≤ finrank K S := by
  obtain ⟨hTrace, hc⟩ := fullRank_retainedForm_projection_trace_codim i S ell hell h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change Matrix.trace ((physicalEndMatrix K n) x) = 0
    rw [physicalEndMatrix, ← LinearMap.trace_eq_matrix_trace]
    exact hTrace hx
  · let X := (imageFromLeftKernel S).map (physicalKernelProjection i ell)
    let E := physicalEndMatrix K n
    have h1 := X.finrank_quotient_add_finrank
    have h2 := (X.map E.toLinearMap).finrank_quotient_add_finrank
    have h3 := LinearEquiv.finrank_map_eq E X
    have h4 := E.finrank_eq
    change finrank K (_ ⧸ X.map E.toLinearMap) ≤ _
    change finrank K (_ ⧸ X) ≤ _ at hc
    omega

def imageTensorCoordinates
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (ell : Coord (l + 1) n → K) :
    (Fin (retainedImageWidth S i ell) → K) ≃ₗ[K] physicalMatrixImage S i ell :=
  (basisOfCrop (imageFromLeftKernel S) (physicalKernelProjection i ell)).symm.trans
    ((physicalEndMatrix K n).submoduleMap _)

def matrixTensorEquiv (K M N : Type*) [Field K]
    [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N] :
    Matrix M N K ≃ₗ[K] ((M → K) ⊗[K] (N → K)) :=
  (LinearEquiv.curry K K M N).symm.trans
    ((Pi.basisFun K M).tensorProduct (Pi.basisFun K N)).equivFun.symm

def cropImageTensorEquiv
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K) :
    Matrix (Fin (retainedImageWidth S i ell)) (Fin (retainedImageWidth R j rho)) K ≃ₗ[K]
      (physicalMatrixImage S i ell ⊗[K] physicalMatrixImage R j rho) :=
  (matrixTensorEquiv K _ _).trans
    (TensorProduct.congr (imageTensorCoordinates S i ell) (imageTensorCoordinates R j rho))

/-- Literal dense crop decoded into the tensor product of the two physical images. -/
def rawSingularCrop
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : DenseKernelFiber R S) :
    physicalMatrixImage S i ell ⊗[K] physicalMatrixImage R j rho :=
  cropImageTensorEquiv R S i j ell rho (physicalPairCrop R S i j ell rho A.val)

variable [Fintype K]

theorem uniformFraction_rawSingularCrop_small
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A₀ : DenseKernelFiber R S) (hr : 2 ≤ r) (hn : 3 ≤ n)
    (hc : finrank K R ≤ n) (P : physicalMatrixImage S i ell ⊗[K] physicalMatrixImage R j rho → Prop) :
    |uniformFraction (DenseKernelFiber R S) (fun A => P (rawSingularCrop R S i j ell rho A)) -
      uniformFraction (physicalMatrixImage S i ell ⊗[K] physicalMatrixImage R j rho) P| ≤
      ((Fintype.card K : ℝ) ^ (n ^ 2))⁻¹ := by
  let E := cropImageTensorEquiv R S i j ell rho
  have h := uniformFraction_physicalPairCrop_small R S i j ell rho A₀ hr hn hc (fun A => P (E A))
  have hE : uniformFraction _ (fun A => P (E A)) = uniformFraction _ P :=
    uniformFraction_equiv E.toEquiv P
  rw [hE] at h
  exact h

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.physicalMatrixImage_trace_codim
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_rawSingularCrop_small
