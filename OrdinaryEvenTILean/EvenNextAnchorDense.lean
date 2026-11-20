import EvenNextAnchorCrop
import EvenFlattening

/-! Transfer the quantitative crop law to uniform samples of the literal
dense source tensors having the two prescribed coordinate kernels. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module EvenTI.Action
open scoped Matrix
noncomputable section

variable {K H : Type*} [Field K] [Fintype K] [Fintype H] [DecidableEq H]
  {l r n : ℕ}

def tensorFlattenEquiv : Tensor K (l+r) n ≃ Matrix (Coord l n) (Coord r n) K where
  toFun := flatten
  invFun A z := A (cutEquiv.symm z).1 (cutEquiv.symm z).2
  left_inv A := by
    funext z
    change A (cutEquiv ((cutEquiv.symm z).1, (cutEquiv.symm z).2)) = A z
    exact congrArg A (cutEquiv.apply_symm_apply z)
  right_inv A := by
    ext i j
    change A (cutEquiv.symm (cutEquiv (i, j))).1 (cutEquiv.symm (cutEquiv (i, j))).2 = A i j
    rw [Equiv.symm_apply_apply]

abbrev DenseKernelFiber
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K)) :=
  {A : Tensor K (l+r) n // (flatten A).toLin'.ker = R ∧ (flatten A)ᵀ.toLin'.ker = S}

def denseKernelFiberEquiv
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K)) :
    DenseKernelFiber R S ≃ MatrixKernelFiber R S :=
  tensorFlattenEquiv.subtypeEquiv fun _ => Iff.rfl

/-- A uniform dense tensor conditioned on its exact two cut kernels has an
almost-uniform literal cropped matrix. The event may test any statistic of
that matrix, including the square and partial traces used by the anchors. -/
theorem uniformFraction_denseKernel_crop {b t : ℕ}
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (C : Matrix H (Coord l n) K) (D : Matrix (Fin b) (Coord r n) K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((Coord r n → K) ⧸ R))
    (hL : b+t = finrank K (imageFromLeftKernel S))
    (hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype))
    (P : Matrix H (Fin b) K → Prop) :
    |uniformFraction (DenseKernelFiber R S) (fun A => P (C * flatten A.val * Dᵀ)) -
        uniformFraction (Matrix H (Fin b) K) P| ≤
      ((Fintype.card K : ℝ)^b - 1) /
        ((Fintype.card K : ℝ)^(b+t) * ((Fintype.card K : ℝ) - 1)) := by
  have e := uniformFraction_equiv (denseKernelFiberEquiv R S)
    (fun A : MatrixKernelFiber R S => P (C * A.val * Dᵀ))
  change uniformFraction (DenseKernelFiber R S) (fun A => P (C * flatten A.val * Dᵀ)) =
    uniformFraction (MatrixKernelFiber R S) (fun A => P (C * A.val * Dᵀ)) at e
  rw [e]
  exact uniformFraction_matrixKernel_crop_left R S C D hind hR hL hC P

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.denseKernelFiberEquiv
#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_denseKernel_crop
