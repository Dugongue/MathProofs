import EvenP1ProbLabel

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenOrdinaryTISingular

noncomputable section

variable {K I B A : Type*} [Field K]
variable [Fintype I] [Fintype B] [Fintype A] [DecidableEq I] [DecidableEq B] [DecidableEq A]

def evalTrace (L : A → Matrix I B K) : Matrix B I K →ₗ[K] (A → K) :=
  LinearMap.pi fun a => LinearMap.applyₗ' K (L a) ∘ₗ rectDual.toLinearMap

theorem evalTrace_apply (L : A → Matrix I B K) (v : Matrix B I K) (a : A) :
    evalTrace L v a = (L a * v).trace := rfl

/-- The rank of pairing with a list of rectangular matrices is the span
of that list. Restricting the argument loses at most the codimension. -/
theorem evalTrace_restricted_rank (L : A → Matrix I B K)
    (W : Submodule K (Matrix B I K)) :
    finrank K (Submodule.span K (Set.range L)) ≤
      finrank K ((evalTrace L).comp W.subtype).range + finrank K (Matrix B I K ⧸ W) := by
  let F := Fintype.linearCombination K L
  let ev := (Pi.basisFun K A).dualBasis.equivFun
  have h : evalTrace L = ev.toLinearMap.comp (F.dualMap.comp rectDual.toLinearMap) := by
    ext v a
    change (L a * v).trace = ev (F.dualMap (rectDual v)) a
    rw [Basis.dualBasis_equivFun, Pi.basisFun_apply]
    change (L a * v).trace = rectDual v (F (Pi.single a 1))
    dsimp only [F]
    rw [Fintype.linearCombination_apply_single, one_smul, rectDual_apply]
  have hrange : (F.dualMap.comp (rectDual (K := K) (I := I) (B := B)).toLinearMap).range =
      F.dualMap.range := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have hdim : finrank K (evalTrace L).range = finrank K (Submodule.span K (Set.range L)) := by
    rw [h, LinearMap.range_comp, hrange, LinearEquiv.finrank_map_eq,
      LinearMap.finrank_range_dualMap_eq_finrank_range, Fintype.range_linearCombination]
  have hr := precompose_rank_loss W.subtype (evalTrace L)
  rw [Submodule.range_subtype, hdim] at hr
  have hW := W.finrank_quotient_add_finrank
  omega

#print axioms evalTrace_apply
#print axioms evalTrace_restricted_rank

end
end Mathproof.EvenTI.Reciprocal.Four