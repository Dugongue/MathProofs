import EvenP1Dense
import EvenP1Marginal

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped Matrix BigOperators Classical
open Matrix EvenTI.Action EvenTI.Primary Mathproof.EvenTI.Reciprocal.Next

noncomputable section

theorem marginalError_equiv_source {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (e : X ≃ Y) (f : Y → Z) :
    marginalError (f ∘ e) = marginalError f := by
  apply Finset.sum_congr rfl
  intro z _
  congr 2
  change mean (fun x => if f (e x) = z then 1 else 0) =
    mean (fun y => if f y = z then 1 else 0)
  unfold mean
  rw [Equiv.sum_comp e (fun y => if f y = z then (1 : ℝ) else 0), Fintype.card_congr e]

variable {K H L J I B : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J]
variable [DecidableEq I] [DecidableEq B]
variable {s n : Nat}

local notation "Rows" => (Sum H L × Option J)
local notation "Cols" => (I × B)
local notation "Bases" => BasisPairs K Rows Cols
local notation "Source" => InvertibleCut K s n
local notation "Target" => AnchorTrace K Rows I
local notation "Full" => (⊤ : Submodule K (Matrix I I K))

/-- Compute the actual reciprocal anchor on a dense source by
reindexing its cut and the inverse transpose of that cut. -/
def denseAnchor (left : Rows ≃ Coord s n) (right : Cols ≃ Coord s n)
    (T : Source) : Matrix I I K :=
  Small.partialTraceRight ((crossed
    (matrixPrimal ((flatten T.val).submatrix left right))
    (matrixDual (((flatten T.val)⁻¹).transpose.submatrix left right))) ^ 2)

theorem denseAnchor_eq (left : Rows ≃ Coord s n) (right : Cols ≃ Coord s n)
    (T : Source) : denseAnchor left right T = Small.anchor (invertibleCutEquivPairs left right T) := by
  simp [denseAnchor, Small.anchor, Small.contraction]

def denseTraceAnchor [CharP K 2] (left : Rows ≃ Coord s n) (right : Cols ≃ Coord s n)
    (T : Source) : Target :=
  ⟨denseAnchor left right T, by rw [denseAnchor_eq, Small.trace_anchor_charTwo]⟩

theorem denseTrace_marginal_of_bad_mass [CharP K 2] [Nonempty I]
    [Fintype Source] [Fintype Bases] [Nonempty Bases]
    [Fintype (traceKernel (K := K) (I := I))] [Fintype Target]
    (left : Rows ≃ Coord s n) (right : Cols ≃ Coord s n)
    (hJ : Fintype.card J = Fintype.card I - 1) (hn : 8 ≤ Fintype.card I) :
    marginalError (denseTraceAnchor left right : Source → Target) ≤
      anchorError K I + 2 * event (fun A : Bases => ¬ Function.Surjective (baselineRows A)) := by
  have he : (denseTraceAnchor left right : Source → Target) =
      traceAnchor ∘ invertibleCutEquivPairs left right := by
    funext T
    exact Subtype.ext (denseAnchor_eq left right T)
  rw [he, marginalError_equiv_source]
  exact trace_marginal_of_bad_mass hJ hn

theorem denseOdd_marginal_of_bad_mass [Nonempty I] [Fintype Source]
    [Fintype Bases] [Nonempty Bases] [Fintype Full]
    (left : Rows ≃ Coord s n) (right : Cols ≃ Coord s n)
    (hJ : Fintype.card J = Fintype.card I - 1) (hn : 8 ≤ Fintype.card I) (h₂ : (2 : K) ≠ 0) :
    marginalError (denseAnchor left right : Source → Matrix I I K) ≤
      anchorError K I + 2 * event (fun A : Bases => ¬ Function.Surjective (baselineRows A)) := by
  have he : (denseAnchor left right : Source → Matrix I I K) =
      Small.anchor ∘ invertibleCutEquivPairs left right := funext (denseAnchor_eq left right)
  rw [he, marginalError_equiv_source]
  exact odd_marginal_of_bad_mass hJ hn h₂

#print axioms denseAnchor_eq
#print axioms denseTrace_marginal_of_bad_mass
#print axioms denseOdd_marginal_of_bad_mass

end
end Mathproof.EvenTI.Reciprocal.Coverage
