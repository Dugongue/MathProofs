import EvenP3RecipHighGrid

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

noncomputable section

variable {K H L C R I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype C] [Fintype R] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq C] [DecidableEq R]
variable [DecidableEq I] [DecidableEq B]

local notation "Groups" => (C ⊕ R)
local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option Groups) (I := I) (B := B)
local notation "W" => (traceKernel (K := K) (I := I))

def reciprocalBlock (A : Bases) (t : Groups) : (H → L → K) →ₗ[K] W :=
  (rowLinear (matrixPrimal A.val.1) (matrixDual A.val.2) t).codRestrict W
    (baseline_row_trace_zero A t)

/-- A rank certification on the column/row cross submatrix transfers to
the polar form of the actual reciprocal anchor. -/
theorem reciprocal_polar_rank_of_cross_groups (A : Bases)
    (c : Module.Dual K (Matrix I I K))
    (h : ∀ y : C → H → L → K,
      (∀ (t : R) (x : H → L → K), (∑ u : C, labelForm W c
        (reciprocalBlock A (.inr t) (y u)) (reciprocalBlock A (.inl u) x)) = 0) →
      y = 0) :
    finrank K (C → H → L → K) - finrank K (labelForm W c).range ≤
      finrank K ((squarePolar (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2))
        (traceBlocks c)).range) := by
  let U := matrixPrimal A.val.1
  let V := matrixDual A.val.2
  have hr := corrected_grid_rank_of_cross_groups (reciprocalBlock A) (labelForm W c) h
  change _ ≤ finrank K ((gridForm (labelForm W c) + (labelForm W c).compl₁₂ diagFold diagFold).compl₁₂ (gridRows U V W (baseline_row_trace_zero A))
      (gridRows U V W (baseline_row_trace_zero A))).range at hr
  rw [← restricted_polar U V W (baseline_row_trace_zero A) c] at hr
  exact hr.trans (rank_pullback_le _ includeShear)

#print axioms reciprocal_polar_rank_of_cross_groups

end
end Mathproof.EvenTI.Reciprocal.Four
