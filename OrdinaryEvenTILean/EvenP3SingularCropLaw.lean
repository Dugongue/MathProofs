import EvenP3SingularDomination
import EvenNextAnchorDense

namespace Mathproof.EvenOrdinaryTISingular
open Matrix Module EvenTI.Action
open scoped Matrix
noncomputable section

section Columns
variable {K V W : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W]
variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [Module.Finite K A] [Fintype B]

/-- Domination for every surjective observation of an exact two-kernel fiber. -/
theorem uniformFraction_twoKernels_crop_le_four {b t : ℕ}
    (R : Submodule K A) (L : Submodule K B)
    (y : Independent K (A ⧸ R) b) (hR : b+t = finrank K (A ⧸ R))
    (hL : b+t = finrank K L) (f : L →ₗ[K] W) (hf : Function.Surjective f)
    (P : (Fin b → W) → Prop) :
    uniformFraction (TwoKernels R L.dualAnnihilator)
      (fun x => P (fun i => f (toKernelRangeEquiv R L (twoKernelsEquiv R L x) (y.val i)))) ≤
      4 * uniformFraction (Fin b → W) P := by
  letI : Fintype L := Fintype.ofFinite _
  let g := LinearEquiv.ofFinrankEq (A ⧸ R) L (hR.symm.trans hL)
  letI : Nonempty (Independent K L b) :=
    ⟨⟨g ∘ y.val, y.property.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)⟩⟩
  rw [uniformFraction_twoKernels_retained R L y hR hL f P]
  have hb : b ≤ finrank K L := hL ▸ Nat.le_add_right b t
  exact uniformFraction_independent_observation_le_four (K := K) hb f hf P

end Columns
section Matrices
variable {K M N H : Type*} [Field K] [Fintype K] [Fintype M] [Fintype N] [Fintype H]
  [DecidableEq M] [DecidableEq N] [DecidableEq H]
theorem uniformFraction_matrixKernel_crop_le_four {b t : ℕ}
    (R : Submodule K (N → K)) (L : Submodule K (M → K))
    (C : Matrix H M K) (D : Matrix (Fin b) N K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((N → K) ⧸ R))
    (hL : b+t = finrank K L)
    (hC : Function.Surjective (C.toLin'.comp L.subtype))
    (P : Matrix H (Fin b) K → Prop) :
    uniformFraction (MatrixKernelFiber R (coordinateLeftKernel L))
      (fun A => P (C * A.val * Dᵀ)) ≤ 4 * uniformFraction (Matrix H (Fin b) K) P := by
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
  exact uniformFraction_twoKernels_crop_le_four R L y hR hL f hC Q

/-- The crop law can also be stated with a literally specified transpose kernel. -/
theorem uniformFraction_matrixKernel_crop_left_le_four {b t : ℕ}
    (R : Submodule K (N → K)) (S : Submodule K (M → K))
    (C : Matrix H M K) (D : Matrix (Fin b) N K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((N → K) ⧸ R))
    (hL : b+t = finrank K (imageFromLeftKernel S))
    (hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype))
    (P : Matrix H (Fin b) K → Prop) :
    uniformFraction (MatrixKernelFiber R S) (fun A => P (C * A.val * Dᵀ)) ≤
      4 * uniformFraction (Matrix H (Fin b) K) P := by
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
  exact uniformFraction_matrixKernel_crop_le_four R (imageFromLeftKernel S) C D hind hR hL hC P

end Matrices
section Dense
variable {K H : Type*} [Field K] [Fintype K] [Fintype H] [DecidableEq H] {l r n : ℕ}
theorem uniformFraction_denseKernel_crop_le_four {b t : ℕ}
    (R : Submodule K (Coord r n → K)) (S : Submodule K (Coord l n → K))
    (C : Matrix H (Coord l n) K) (D : Matrix (Fin b) (Coord r n) K)
    (hind : LinearIndependent K (fun j => R.mkQ (D.row j)))
    (hR : b+t = finrank K ((Coord r n → K) ⧸ R))
    (hL : b+t = finrank K (imageFromLeftKernel S))
    (hC : Function.Surjective (C.toLin'.comp (imageFromLeftKernel S).subtype))
    (P : Matrix H (Fin b) K → Prop) :
    uniformFraction (DenseKernelFiber R S) (fun A => P (C * flatten A.val * Dᵀ)) ≤
      4 * uniformFraction (Matrix H (Fin b) K) P := by
  have e := uniformFraction_equiv (denseKernelFiberEquiv R S)
    (fun A : MatrixKernelFiber R S => P (C * A.val * Dᵀ))
  change uniformFraction (DenseKernelFiber R S) (fun A => P (C * flatten A.val * Dᵀ)) =
    uniformFraction (MatrixKernelFiber R S) (fun A => P (C * A.val * Dᵀ)) at e
  rw [e]
  exact uniformFraction_matrixKernel_crop_left_le_four R S C D hind hR hL hC P

end Dense
end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.uniformFraction_denseKernel_crop_le_four
