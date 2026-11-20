import EvenP3RecipLowGrid
import EvenNextRecipPolar

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped Matrix BigOperators
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

variable {K H L J R I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype R] [Fintype I] [Fintype B]
variable [DecidableEq J] [DecidableEq R] [DecidableEq I]

private def extendInputs :
    Restricted K H L J →ₗ[K] Restricted K H L (J ⊕ R) :=
  LinearMap.pi (Sum.elim (fun j => LinearMap.proj j) (fun _ => 0))

@[simp] private theorem extendInputs_inl (x : Restricted K H L J) (j : J) :
    extendInputs (R := R) x (Sum.inl j) = x j := rfl

@[simp] private theorem extendInputs_inr (x : Restricted K H L J) (r : R) :
    extendInputs x (Sum.inr r) = 0 := rfl

variable (U : (Sum H L × Option (J ⊕ R)) → Matrix I B K)
variable (V : (Sum H L × Option (J ⊕ R)) → Matrix B I K)
variable (S : Submodule K (Matrix I I K))
variable (hS : ∀ t x, rowLinear U V t x ∈ S)

/-- Read only rows with target labels in the selected summand. -/
def smallRows : (H → L → K) →ₗ[K] (J → S) :=
  LinearMap.pi fun t => (rowLinear U V (Sum.inl t)).codRestrict S (hS (Sum.inl t))

private def smallGrid : Restricted K H L J →ₗ[K] Grid J S :=
  LinearMap.pi fun p => ((LinearMap.proj p.2).comp (smallRows U V S hS)).comp (LinearMap.proj p.1)

private theorem fullGrid_inl (x : Restricted K H L J) (u t : J) :
    gridRows U V S hS (extendInputs x) (.inl u,.inl t) =
      smallGrid U V S hS x (u,t) := rfl

private theorem fullGrid_inr (x : Restricted K H L J) (u : R) (t : J ⊕ R) :
    gridRows U V S hS (extendInputs x) (.inr u,t) = 0 := by
  change ((rowLinear U V t).codRestrict S (hS t)) (extendInputs x (Sum.inr u)) = _
  rw [extendInputs_inr, map_zero]

private theorem gridForm_small (C : LinearMap.BilinForm K S) (x y : Restricted K H L J) :
    gridForm C (gridRows U V S hS (extendInputs x)) (gridRows U V S hS (extendInputs y)) =
      gridForm C (smallGrid U V S hS x) (smallGrid U V S hS y) := by
  simp only [gridForm_apply, Fintype.sum_prod_type, Fintype.sum_sum_type, Prod.swap_prod_mk,
    fullGrid_inl, fullGrid_inr, map_zero, LinearMap.zero_apply, Finset.sum_const_zero, zero_add,
    add_zero]

private theorem diag_small (x : Restricted K H L J) :
    diagFold (K := K) (gridRows U V S hS (extendInputs x)) =
      diagFold (K := K) (smallGrid U V S hS x) := by
  change (∑ j : J ⊕ R, gridRows U V S hS (extendInputs x) (j,j)) =
    ∑ j : J, smallGrid U V S hS x (j,j)
  simp only [Fintype.sum_sum_type, fullGrid_inl, fullGrid_inr, Finset.sum_const_zero, add_zero]

set_option maxHeartbeats 1600000 in
/-- The selected target labels suffice for a rank bound on the full
physical shear, including its forced distinguished diagonal block. -/
theorem shear_polar_rank_of_small_quotient (c : Module.Dual K (Matrix I I K))
    (hs : ∀ x y, labelForm S c x y = labelForm S c y x)
    (h : Function.Surjective
      ((LinearMap.compLeft (labelForm S c).rangeRestrict J).comp (smallRows U V S hS))) :
    (Fintype.card J ^ 2 - 1) * finrank K (labelForm S c).range ≤
      finrank K (squarePolar (deltaLinear U V) (traceBlocks c)).range := by
  let C := labelForm S c
  let A := squarePolar (deltaLinear U V) (traceBlocks c)
  let G := smallGrid U V S hS
  let F := (gridForm C + C.compl₁₂ (diagFold (J := J)) diagFold).compl₁₂ G G
  have hG : Function.Surjective ((LinearMap.compLeft C.rangeRestrict (J × J)).comp G) := by
    intro y
    choose x hx using fun u : J => h (fun t => y (u,t))
    refine ⟨x, ?_⟩
    funext p
    exact congrFun (hx p.1) p.2
  have hc := rank_of_grid_and_radical_quotient C hs G hG
  have hF : (A.compl₁₂ includeShear includeShear).compl₁₂ extendInputs extendInputs = F := by
    rw [show A = squarePolar (deltaLinear U V) (traceBlocks c) from rfl, restricted_polar U V S hS c]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change gridForm C (gridRows U V S hS (extendInputs x)) (gridRows U V S hS (extendInputs y)) +
      C (diagFold (gridRows U V S hS (extendInputs x))) (diagFold (gridRows U V S hS (extendInputs y))) =
      gridForm C (G x) (G y) + C (diagFold (G x)) (diagFold (G y))
    rw [gridForm_small U V S hS, diag_small U V S hS, diag_small U V S hS]
  have hp := rank_pullback_le (A.compl₁₂ includeShear includeShear) extendInputs
  rw [hF] at hp
  exact hc.trans (hp.trans (rank_pullback_le A includeShear))

#print axioms shear_polar_rank_of_small_quotient

end Mathproof.EvenTI.Reciprocal.SquareLow
