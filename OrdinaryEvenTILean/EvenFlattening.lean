import EvenPhysicalAction
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped BigOperators

namespace EvenTI.Action

variable {K : Type*} [Field K] {l r n : Nat}

/-- The two halves of a prescribed cut retain all physical indices. -/
def cutEquiv : Coord l n × Coord r n ≃ Coord (l + r) n where
  toFun a := Fin.append a.1 a.2
  invFun a := (fun i => a (i.castAdd r), fun j => a (j.natAdd l))
  left_inv := by intro a; simp [Fin.append_left, Fin.append_right]
  right_inv := by intro a; exact Fin.append_castAdd_natAdd

def flatten (T : Tensor K (l + r) n) : Matrix (Coord l n) (Coord r n) K :=
  fun x y => T (cutEquiv (x, y))

def leftModes (g : Changes K (l + r) n) : Changes K l n := fun i => g (i.castAdd r)
def rightModes (g : Changes K (l + r) n) : Changes K r n := fun j => g (j.natAdd l)

theorem cut_productMatrix (g : Changes K (l + r) n)
    (x x' : Coord l n) (y y' : Coord r n) :
    productMatrix g (cutEquiv (x, y)) (cutEquiv (x', y')) =
      productMatrix (leftModes g) x x' * productMatrix (rightModes g) y y' := by
  unfold productMatrix cutEquiv leftModes rightModes
  simp [Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem flatten_action (g : Changes K (l + r) n) (T : Tensor K (l + r) n) :
    flatten (act g T) =
      productMatrix (leftModes g) * flatten T * (productMatrix (rightModes g)).transpose := by
  ext x y
  change (∑ a : Coord (l + r) n, productMatrix g (cutEquiv (x, y)) a * T a) = _
  rw [← cutEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [cut_productMatrix, Matrix.mul_apply, Matrix.transpose_apply, flatten,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem cut_side_card (n l : Nat) : Fintype.card (Coord l n) = n ^ l := by
  simp [Coord, Fintype.card_fun]

/-- The product of the physical units is an invertible cut-side matrix. -/
def productUnit (g : Changes K l n) : (Matrix (Coord l n) (Coord l n) K)ˣ where
  val := productMatrix g
  inv := productMatrix g⁻¹
  val_inv := by rw [← productMatrix_mul, mul_inv_cancel, productMatrix_one]
  inv_val := by rw [← productMatrix_mul, inv_mul_cancel, productMatrix_one]

/-- Split a cut side into a specified physical factor and all the others. -/
def retainedMode (i : Fin (l + 1)) : Fin n × Coord l n ≃ Coord (l + 1) n :=
  Fin.insertNthEquiv (fun _ => Fin n) i

theorem retained_productMatrix (g : Changes K (l + 1) n) (i : Fin (l + 1))
    (x y : Fin n) (u v : Coord l n) :
    productMatrix g (retainedMode i (x,u)) (retainedMode i (y,v)) =
      (g i).val x y * productMatrix (fun j => g (i.succAbove j)) u v := by
  simp only [productMatrix, retainedMode, Fin.insertNthEquiv_apply]
  rw [Fin.prod_univ_succAbove _ i]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

#print axioms retained_productMatrix
#print axioms flatten_action
#print axioms cut_side_card

end EvenTI.Action
