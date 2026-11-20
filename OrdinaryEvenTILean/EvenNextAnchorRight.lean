import EvenNextAnchorMatrix

/-! Surjectivity of a right crop on the exact right annihilator supplies the
independent probe family in the quotient by the exact right kernel. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module
open scoped Matrix
noncomputable section

variable {K N : Type*} [Field K] [Fintype N] [DecidableEq N]

theorem independent_rows_mod_kernel_of_surjective {b : ℕ}
    (R : Submodule K (N → K)) (D : Matrix (Fin b) N K)
    (hD : Function.Surjective (D.toLin'.comp (imageFromLeftKernel R).subtype)) :
    LinearIndependent K (fun j => R.mkQ (D.row j)) := by
  let f : (Fin b → K) →ₗ[K] ((N → K) ⧸ R) := R.mkQ.comp Dᵀ.toLin'
  have hf : f.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    change R.mkQ (Dᵀ.toLin' x) = 0 at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    apply (dotProductEquiv K (Fin b)).injective
    rw [map_zero]
    apply LinearMap.ext
    intro z
    obtain ⟨v, hv⟩ := hD z
    change D *ᵥ v.val = z at hv
    have hphi : dotProductEquiv K N (Dᵀ.toLin' x) ∈ R.map (dotProductEquiv K N).toLinearMap :=
      Submodule.mem_map.mpr ⟨Dᵀ.toLin' x, hx, rfl⟩
    have hzero := (Submodule.mem_dualCoannihilator v.val).mp v.property _ hphi
    change x ⬝ᵥ z = 0
    rw [← hv, ← Matrix.dotProduct_transpose_mulVec D v.val x,
      dotProduct_comm v.val (Dᵀ *ᵥ x)]
    exact hzero
  have heq : f ∘ (Pi.basisFun K (Fin b)) = fun j => R.mkQ (D.row j) := by
    funext j
    change R.mkQ (Dᵀ *ᵥ (Pi.basisFun K (Fin b)) j) = R.mkQ (D.row j)
    rw [Pi.basisFun_apply, Matrix.mulVec_single_one]
    rfl
  rw [← heq]
  exact (Pi.basisFun K (Fin b)).linearIndependent.map' f hf

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.independent_rows_mod_kernel_of_surjective
