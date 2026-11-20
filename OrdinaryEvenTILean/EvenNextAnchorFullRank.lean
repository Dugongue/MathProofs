import EvenNextAnchorProjection
import EvenNextRetainedCovariance

/-! The ordinary matrix full-rank criterion for the retained dense form supplies the
surjectivity hypothesis of the physical kernel projection. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module LinearMap EvenTI.Action
open scoped Matrix TensorProduct
noncomputable section

variable {K : Type*} [Field K] {l n : ℕ}

theorem regroupCoordinates_inverse_basis (i : Fin (l+1)) (x : Fin n) (y : Coord l n) :
    (regroupCoordinates i (K := K)).symm
        ((Pi.basisFun K (Fin n)) x ⊗ₜ[K] (Pi.basisFun K (Coord l n)) y) =
      Pi.basisFun K (Coord (l+1) n) (retainedMode i (x,y)) := by
  let B := (Pi.basisFun K (Fin n)).tensorProduct (Pi.basisFun K (Coord l n))
  have hB : B.equivFun ((Pi.basisFun K (Fin n)) x ⊗ₜ[K] (Pi.basisFun K (Coord l n)) y) =
      Pi.single (x,y) 1 := by
    have hT : B (x,y) = (Pi.basisFun K (Fin n)) x ⊗ₜ[K]
        (Pi.basisFun K (Coord l n)) y := Module.Basis.tensorProduct_apply _ _ x y
    rw [← hT]
    funext z
    rw [B.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  change (LinearEquiv.funCongrLeft K K (retainedMode i)).symm
      (B.equivFun ((Pi.basisFun K (Fin n)) x ⊗ₜ[K] (Pi.basisFun K (Coord l n)) y)) = _
  rw [hB, LinearEquiv.funCongrLeft_symm]
  funext z
  change (Pi.single (x,y) (1 : K) : (Fin n × Coord l n) → K) ((retainedMode i).symm z) =
    (Pi.basisFun K _ (retainedMode i (x,y))) z
  by_cases hz : z = retainedMode i (x,y)
  · subst z
    simp [Pi.basisFun_apply, Pi.single_apply]
  · have hsz : (retainedMode i).symm z ≠ (x,y) := by
      intro h
      apply hz
      simpa only [Equiv.apply_symm_apply] using congrArg (retainedMode i) h
    simp [Pi.basisFun_apply, Pi.single_apply, hz, hsz, Ne.symm hz, Ne.symm hsz]

theorem regroupKernelForm_contraction (i : Fin (l+1)) (ell : Coord (l+1) n → K) :
    (dotProductEquiv K (Fin n)).symm.toLinearMap.comp
        (TensorProduct.curry (regroupKernelForm i ell)).flip =
      (retainedForm i ell).toLin' := by
  apply (Pi.basisFun K (Coord l n)).ext
  intro y
  apply (dotProductEquiv K (Fin n)).injective
  change dotProductEquiv K (Fin n) ((dotProductEquiv K (Fin n)).symm
      ((TensorProduct.curry (regroupKernelForm i ell)).flip ((Pi.basisFun K _) y))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply (Pi.basisFun K (Fin n)).ext
  intro x
  change (regroupKernelForm i ell)
        ((Pi.basisFun K (Fin n)) x ⊗ₜ[K] (Pi.basisFun K (Coord l n)) y) =
    ((retainedForm i ell).toLin' ((Pi.basisFun K (Coord l n)) y)) ⬝ᵥ ((Pi.basisFun K (Fin n)) x)
  rw [regroupKernelForm, LinearMap.comp_apply]
  change (dotProductEquiv K _ ell) ((regroupCoordinates i).symm
      ((Pi.basisFun K (Fin n)) x ⊗ₜ[K] (Pi.basisFun K (Coord l n)) y)) = _
  rw [regroupCoordinates_inverse_basis]
  change ell ⬝ᵥ (Pi.basisFun K _ (retainedMode i (x,y))) = _
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    dotProduct_single_one, Matrix.toLin'_apply, Matrix.mulVec_single_one, dotProduct_single_one] <;> rfl

theorem fullRank_retainedForm_contraction_surjective (i : Fin (l+1))
    (ell : Coord (l+1) n → K) (h : (retainedForm i ell).rank = n) :
    Function.Surjective (TensorProduct.curry (regroupKernelForm i ell)).flip := by
  let A := retainedForm i ell
  have hm : A.mulVecLin = A.toLin' := LinearMap.ext (fun x => by rfl)
  have hr : finrank K A.toLin'.range = n := by
    change finrank K A.mulVecLin.range = n at h
    rwa [hm] at h
  have hsur : Function.Surjective A.toLin' :=
    LinearMap.range_eq_top.mp <| Submodule.eq_top_of_finrank_eq <| by
      simpa using hr
  intro phi
  obtain ⟨w, hw⟩ := hsur ((dotProductEquiv K (Fin n)).symm phi)
  refine ⟨w, (dotProductEquiv K (Fin n)).symm.injective ?_⟩
  exact (LinearMap.congr_fun (regroupKernelForm_contraction i ell) w).trans hw

theorem fullRank_retainedForm_projection_trace_codim
    (i : Fin (l+1)) (S : Submodule K (Coord (l+1) n → K)) (ell : Coord (l+1) n → K)
    (hell : ell ∈ S) (h : (retainedForm i ell).rank = n) :
    (imageFromLeftKernel S).map (physicalKernelProjection i ell) ≤
        (LinearMap.trace K (PhysicalModule K n)).ker ∧
      finrank K (End K (PhysicalModule K n) ⧸
        (imageFromLeftKernel S).map (physicalKernelProjection i ell)) ≤ finrank K S :=
  physicalKernelProjection_trace_codim i S ell hell
    (fullRank_retainedForm_contraction_surjective i ell h)

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.regroupKernelForm_contraction
#print axioms Mathproof.EvenOrdinaryTISingular.fullRank_retainedForm_projection_trace_codim
