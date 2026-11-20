import EvenNextRecipBlocks
import EvenReciprocalLaw

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators Matrix
open Matrix
open Mathproof.EvenTI.Reciprocal

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)

/-- The selected primal and inverse-transpose rows have different labels.
Their rectangular product therefore has trace zero. -/
theorem reciprocal_coefficient_trace_zero (A : Bases) (a : H) (b : L) (t : J) :
    ((matrixPrimal A.val.1 (.inr b, none)) * (matrixDual A.val.2 (.inl a, some t))).trace = 0 := by
  have h := congrFun (congrFun A.property.1 (Sum.inr b, none)) (Sum.inl a, some t)
  simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, matrixPrimal, matrixDual, Fintype.sum_prod_type] using h

theorem oneRow_reciprocal_trace_zero (A : Bases) (x : H → L → K) (t : J) :
    Matrix.trace (fun i j : I => oneRow (matrixPrimal A.val.1) (matrixDual A.val.2) x t i j) = 0 := by
  change (∑ i : I, ∑ a : H, ∑ b : L, x a b *
    (matrixPrimal A.val.1 (.inr b, none) * matrixDual A.val.2 (.inl a, some t)) i i) = 0
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.mul_sum]
  change x a b * ((matrixPrimal A.val.1 (.inr b, none)) *
    (matrixDual A.val.2 (.inl a, some t))).trace = 0
  rw [reciprocal_coefficient_trace_zero, mul_zero]

#print axioms reciprocal_coefficient_trace_zero
#print axioms oneRow_reciprocal_trace_zero

end Mathproof.EvenTI.Reciprocal.Next
