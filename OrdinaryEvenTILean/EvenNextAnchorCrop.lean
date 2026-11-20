import EvenNextAnchorMatrix
import EvenLiveSingularEstimate

/-! Quantitative crop law for the actual matrix product C * A * D.transpose. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module
open scoped Matrix
noncomputable section

variable {K M N H : Type*} [Field K] [Fintype K] [Fintype M] [Fintype N] [Fintype H]
  [DecidableEq M] [DecidableEq N] [DecidableEq H]

/-- The column of the literal cropped matrix is the observation of the
corresponding right probe vector under the original matrix. -/
theorem crop_columns_toLin {b : ℕ} (A : Matrix M N K) (C : Matrix H M K)
    (D : Matrix (Fin b) N K) (j : Fin b) :
    (C * A * Dᵀ).col j = C.toLin' (A.toLin' (D.row j)) := by
  change (C * A) *ᵥ (D.row j) = C *ᵥ (A *ᵥ (D.row j))
  exact (Matrix.mulVec_mulVec _ _ _).symm

/-- The column functions, in column-major order, of a matrix block. -/
def columnsEquiv (b : ℕ) : (Fin b → H → K) ≃ Matrix H (Fin b) K where
  toFun z i j := z j i
  invFun A j i := A i j
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual cropped matrix, conditioned on both exact coordinate kernels,
has every event probability close to that of a uniform block. The inputs
are a row projection surjective on the exact image and independent right
probes in the exact quotient by the right kernel. -/
theorem uniformFraction_matrixKernel_crop {b t : ℕ}
    (R : Submodule K (N → K)) (L : Submodule K (M → K))
    (C : Matrix H M K) (D : Matrix (Fin b) N K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((N → K) ⧸ R))
    (hL : b+t = finrank K L)
    (hC : Function.Surjective (C.toLin'.comp L.subtype))
    (P : Matrix H (Fin b) K → Prop) :
    |uniformFraction (MatrixKernelFiber R (coordinateLeftKernel L))
        (fun A => P (C * A.val * Dᵀ)) - uniformFraction (Matrix H (Fin b) K) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(b+t) * ((Fintype.card K : ℝ) - 1)) := by
  let y : Independent K ((N → K) ⧸ R) b := ⟨fun j => R.mkQ (D.row j), hind⟩
  let e := matrixTwoKernelsEquiv R L
  let f := C.toLin'.comp L.subtype
  let Q (z : Fin b → H → K) := P (columnsEquiv b z)
  let P' (x : TwoKernels R L.dualAnnihilator) :=
    Q (fun j => f (toKernelRangeEquiv R L (twoKernelsEquiv R L x) (y.val j)))
  have hcols (A : MatrixKernelFiber R (coordinateLeftKernel L)) (j : Fin b) :
      f (toKernelRangeEquiv R L (twoKernelsEquiv R L (e A)) (y.val j)) =
        (C * A.val * Dᵀ).col j := by
    rw [crop_columns_toLin]
    change C.toLin' ((toKernelRangeEquiv R L (twoKernelsEquiv R L (e A))
      (R.mkQ (D.row j)) : L) : M → K) = C.toLin' (A.val.toLin' (D.row j))
    exact congrArg C.toLin' (toKernelRangeEquiv_mk R L (twoKernelsEquiv R L (e A)) _)
  have hevent :
      (fun A : MatrixKernelFiber R (coordinateLeftKernel L) => P (C * A.val * Dᵀ)) =
        fun A => P' (e A) := by
    funext A
    apply congrArg P
    ext i j
    exact (congrFun (hcols A j) i).symm
  rw [hevent, uniformFraction_equiv e P', ← uniformFraction_equiv (columnsEquiv b) P]
  exact uniformFraction_twoKernels_crop R L y hR hL f hC Q

/-- The crop law can also be stated with a literally specified transpose kernel. -/
theorem uniformFraction_matrixKernel_crop_left {b t : ℕ}
    (R : Submodule K (N → K)) (S : Submodule K (M → K))
    (C : Matrix H M K) (D : Matrix (Fin b) N K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((N → K) ⧸ R))
    (hL : b+t = finrank K (imageFromLeftKernel S))
    (hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype))
    (P : Matrix H (Fin b) K → Prop) :
    |uniformFraction (MatrixKernelFiber R S) (fun A => P (C * A.val * Dᵀ)) -
        uniformFraction (Matrix H (Fin b) K) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(b+t) * ((Fintype.card K : ℝ) - 1)) := by
  let e : MatrixKernelFiber R S ≃ MatrixKernelFiber R (coordinateLeftKernel (imageFromLeftKernel S)) :=
    Equiv.subtypeEquivRight (fun A => by
      change (A.toLin'.ker = R ∧ Aᵀ.toLin'.ker = S) ↔
        (A.toLin'.ker = R ∧ Aᵀ.toLin'.ker = coordinateLeftKernel (imageFromLeftKernel S))
      rw [coordinateLeftKernel_imageFromLeftKernel])
  have he := uniformFraction_equiv e
    (fun A => P (C * A.val * Dᵀ))
  change uniformFraction (MatrixKernelFiber R S) (fun A => P (C * A.val * Dᵀ)) =
    uniformFraction (MatrixKernelFiber R (coordinateLeftKernel (imageFromLeftKernel S)))
      (fun A => P (C * A.val * Dᵀ)) at he
  rw [he]
  exact uniformFraction_matrixKernel_crop R (imageFromLeftKernel S) C D hind hR hL hC P

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.crop_columns_toLin
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_matrixKernel_crop
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_matrixKernel_crop_left
