import EvenP4HigherRecip
import EvenP3RecipRegroup
import EvenNextQuadraticCovariance

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix
open Matrix EvenTI.Action EvenTI.AnchorCovariance Mathproof.EvenTI.Reciprocal.Next
noncomputable section

variable {K H L J I B : Type*} [Field K]
  [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
  [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "A" => Sum H L

private def shuffle : ((A × B) × (J × I)) ≃ ((A × J) × (I × B)) where
  toFun p := ((p.1.1, p.2.1), (p.2.2, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.1.2, p.2.1))
  left_inv := by rintro ⟨⟨a,b⟩,⟨j,i⟩⟩; rfl
  right_inv := by rintro ⟨⟨a,j⟩,⟨i,b⟩⟩; rfl

private def regroupVec (U : Matrix (A × J) (I × B) K) : (A × B) × (J × I) → K :=
  fun p => U (shuffle p).1 (shuffle p).2

private theorem regroupVec_action
    (a : Matrix A A K) (p : Matrix J J K) (q : Matrix I I K) (b : Matrix B B K)
    (U : Matrix (A × J) (I × B) K) :
    regroupVec (kronecker a p * U * (kronecker q b)ᵀ) =
      (kronecker (kronecker a b) (kronecker p q)).mulVec (regroupVec U) := by
  funext x
  change _ = ∑ z, kronecker (kronecker a b) (kronecker p q) x z * regroupVec U z
  rw [← (shuffle (H := H) (L := L) (B := B) (J := J) (I := I)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [regroupVec, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  change (a x.1.1 y.1 * p x.2.1 y.2 * U y z) * (q x.2.2 z.1 * b x.1.2 z.2) =
    (a x.1.1 y.1 * b x.1.2 z.2 * (p x.2.1 y.2 * q x.2.2 z.1)) * U y z
  ac_rfl

private theorem crossed_regroupVec (U V : Matrix (A × J) (I × B) K) :
    crossed (matrixPrimal U) (matrixDual V) =
      partialTraceRight (Matrix.vecMulVec (regroupVec U) (regroupVec V)) := by
  ext x y
  change (∑ a : A, ∑ b : B, U (a, x.1) (x.2, b) * V (a, y.1) (y.2, b)) =
    ∑ z : A × B, U (z.1, x.1) (x.2, z.2) * V (z.1, y.1) (y.2, z.2)
  rw [Fintype.sum_prod_type]

private theorem kronecker_inv_val {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (a : (Matrix X X K)ˣ) (b : (Matrix Y Y K)ˣ) :
    Matrix.kronecker a.inv b.inv * Matrix.kronecker a.val b.val = 1 := by
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, a.inv_val, b.inv_val, Matrix.one_kronecker_one]

/-- The actual crossed reciprocal contraction is conjugated by the two
retained physical changes.  The other two changes cancel by partial trace. -/
theorem crossed_reciprocal_transport
    (a : (Matrix A A K)ˣ) (p : (Matrix J J K)ˣ)
    (q : (Matrix I I K)ˣ) (b : (Matrix B B K)ˣ)
    (U V : Matrix (A × J) (I × B) K) :
    crossed
        (matrixPrimal (kronecker a.val p.val * U * (kronecker q.val b.val)ᵀ))
        (matrixDual (kronecker a.invᵀ p.invᵀ * V * (kronecker q.invᵀ b.invᵀ)ᵀ)) =
      kronecker p.val q.val * crossed (matrixPrimal U) (matrixDual V) * kronecker p.inv q.inv := by
  rw [crossed_regroupVec, crossed_regroupVec, regroupVec_action, regroupVec_action]
  let P := kronecker (kronecker a.val b.val) (kronecker p.val q.val)
  let Q := kronecker (kronecker a.inv b.inv) (kronecker p.inv q.inv)
  change partialTraceRight (vecMulVec (P.mulVec (regroupVec U)) (Qᵀ.mulVec (regroupVec V))) = _
  have h : vecMulVec (P.mulVec (regroupVec U)) (Qᵀ.mulVec (regroupVec V)) =
      P * vecMulVec (regroupVec U) (regroupVec V) * Q := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]
  rw [h]
  exact partialRight_conjugate _ _ _ _ _ (kronecker_inv_val a b)

/-- Squaring and taking the remaining partial trace preserves conjugacy by
the selected physical mode on the right. -/
theorem reciprocal_twice_trace_transport
    (a : (Matrix A A K)ˣ) (p : (Matrix J J K)ˣ)
    (q : (Matrix I I K)ˣ) (b : (Matrix B B K)ˣ)
    (U V : Matrix (A × J) (I × B) K) :
    Small.partialTraceRight (crossed
        (matrixPrimal (kronecker a.val p.val * U * (kronecker q.val b.val)ᵀ))
        (matrixDual (kronecker a.invᵀ p.invᵀ * V * (kronecker q.invᵀ b.invᵀ)ᵀ)) ^ 2) =
      q.val * Small.partialTraceRight (crossed (matrixPrimal U) (matrixDual V) ^ 2) * q.inv := by
  rw [crossed_reciprocal_transport]
  exact (quadratic_covariant (crossed (matrixPrimal U) (matrixDual V))
    p.val p.inv q.val q.inv p.inv_val q.inv_val).2

end
end Mathproof.EvenTI.Reciprocal.Coverage

#print axioms Mathproof.EvenTI.Reciprocal.Coverage.crossed_reciprocal_transport
#print axioms Mathproof.EvenTI.Reciprocal.Coverage.reciprocal_twice_trace_transport
