import EvenNextKernelTransport
import Mathlib.LinearAlgebra.Matrix.Rank

namespace EvenTI.Action

open Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {d n : Nat}

/-- Pull a form apart at a specified physical factor. -/
def retainedForm (i : Fin (d + 1)) (T : Tensor K (d + 1) n) :
    Matrix (Fin n) (Coord d n) K :=
  fun x u => T (retainedMode i (x, u))

theorem retainedForm_act (i : Fin (d + 1)) (g : Changes K (d + 1) n)
    (T : Tensor K (d + 1) n) :
    retainedForm i (act g T) =
      (g i).val * retainedForm i T * (productMatrix (fun j => g (i.succAbove j))).transpose := by
  ext x u
  change (∑ a : Coord (d + 1) n, productMatrix g (retainedMode i (x, u)) a * T a) = _
  rw [← (retainedMode i).sum_comp, Fintype.sum_prod_type]
  simp only [retained_productMatrix, Matrix.mul_apply, Matrix.transpose_apply, retainedForm,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  ac_rfl

theorem retainedForm_rank_act (i : Fin (d + 1)) (g : Changes K (d + 1) n)
    (T : Tensor K (d + 1) n) :
    (retainedForm i (act g T)).rank = (retainedForm i T).rank := by
  let p : (Matrix (Coord d n) (Coord d n) K)ˣ :=
    productUnit (fun j => g (i.succAbove j))
  have hp : p.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp p.isUnit).ne_zero
  have hp' : (productMatrix (fun j => g (i.succAbove j))).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hp
  have hi : (g i).val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (g i).isUnit).ne_zero
  rw [retainedForm_act, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hp',
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hi]

/-- Contragredient factor changes use the ordinary action with inverse-t
physical matrices. -/
def dualChanges (g : Changes K (d + 1) n) : Changes K (d + 1) n :=
  fun i => ⟨(g i).inv.transpose, (g i).val.transpose,
    by rw [← Matrix.transpose_mul, (g i).val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, (g i).inv_val, Matrix.transpose_one]⟩

theorem dual_product (g : Changes K (d + 1) n) :
    productMatrix (dualChanges g) = (productMatrix g⁻¹).transpose := by
  rfl

theorem retainedForm_rank_move (i : Fin (d + 1)) (g : Changes K (d + 1) n)
    (form : Coord (d + 1) n → K) :
    (retainedForm i (moveCutForm (productUnit g) form)).rank = (retainedForm i form).rank := by
  have h : moveCutForm (productUnit g) form = act (dualChanges g) form := by
    rw [act, dual_product]
    rfl
  rw [h]
  exact retainedForm_rank_act i _ form

theorem all_retained_fullRank_iff (g : Changes K (d + 1) n)
    (form : Coord (d + 1) n → K) :
    (∀ i, (retainedForm i (moveCutForm (productUnit g) form)).rank = n) ↔
      ∀ i, (retainedForm i form).rank = n := by
  simp only [retainedForm_rank_move]

#print axioms retainedForm_act
#print axioms retainedForm_rank_move
#print axioms all_retained_fullRank_iff

end EvenTI.Action
