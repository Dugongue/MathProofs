import EvenP3RecipHighEvaluation

namespace Mathproof.EvenTI.Reciprocal.Four

open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.PartOne

noncomputable section

variable {K I B L : Type*} [Field K] [Fintype I] [Fintype B] [Fintype L]
variable [DecidableEq I] [DecidableEq B] [DecidableEq L]

abbrev matrixAnnihilator (U : L → Matrix I B K) : Submodule K (Matrix B I K) :=
  (evalTrace U).ker

theorem matrixAnnihilator_codim (U : L → Matrix I B K) :
    finrank K (Matrix B I K ⧸ matrixAnnihilator U) ≤ Fintype.card L := by
  rw [(evalTrace U).quotKerEquivRange.finrank_eq]
  exact (Submodule.finrank_le _).trans_eq (by simp [Module.finrank_pi])

theorem matrixAnnihilator_trace (U : L → Matrix I B K) (V : matrixAnnihilator U) (i : L) :
    (U i * V.val).trace = 0 := by
  have h := congrFun (LinearMap.mem_ker.mp V.property) i
  exact h

/-- Convert between the concrete matrix fiber used by the sandwich rank proof
and the abstract dual fiber sampled by the existing reciprocal rows law. -/
def matrixAnnihilatorEquiv (U : L → Matrix I B K) : matrixAnnihilator U ≃ₗ[K] Ann U where
  toFun v := ⟨rectDual v.val, by
    apply (Submodule.mem_dualAnnihilator _).mpr
    have h : primalSpan U ≤ (rectDual v.val).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact matrixAnnihilator_trace U v i
    intro x hx
    exact h hx⟩
  invFun f := ⟨rectDual.symm f.val, by
    apply LinearMap.mem_ker.mpr
    funext i
    exact ann_mul_trace U f i⟩
  left_inv v := by apply Subtype.ext; exact rectDual.symm_apply_apply v.val
  right_inv f := by apply Subtype.ext; exact rectDual.apply_symm_apply f.val
  map_add' v w := by apply Subtype.ext; exact rectDual.map_add v.val w.val
  map_smul' c v := by apply Subtype.ext; exact rectDual.map_smul c v.val

#print axioms matrixAnnihilator_codim
#print axioms matrixAnnihilator_trace
#print axioms matrixAnnihilatorEquiv

end
end Mathproof.EvenTI.Reciprocal.Four