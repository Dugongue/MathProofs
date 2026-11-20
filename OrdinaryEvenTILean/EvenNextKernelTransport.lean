import EvenFlattening
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace EvenTI.Action
open Matrix

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

private theorem unit_mulVec_zero_iff (u : (Matrix I I K)ˣ) (x : I → K) :
    u.val.mulVec x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun y => u.inv.mulVec y) h
    rw [Matrix.mulVec_mulVec, u.inv_val, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hh
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- Coordinate map of the contragredient action on the cut forms. -/
def moveCutForm (u : (Matrix I I K)ˣ) (x : I → K) : I → K :=
  u.inv.transpose.mulVec x

theorem moveCutForm_injective (u : (Matrix I I K)ˣ) :
    Function.Injective (moveCutForm u) := by
  intro x y h
  have hprod : u.val.transpose * u.inv.transpose = 1 := by
    rw [← Matrix.transpose_mul, u.inv_val, Matrix.transpose_one]
  have hh := congrArg (fun z => u.val.transpose.mulVec z) h
  simpa only [moveCutForm, Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] using hh

theorem moveCutForm_ne_zero (u : (Matrix I I K)ˣ) {x : I → K} (hx : x ≠ 0) :
    moveCutForm u x ≠ 0 := by
  intro h
  apply hx
  exact moveCutForm_injective u (h.trans (by simp [moveCutForm]))

theorem right_form_transport (A : (Matrix I I K)ˣ) (B : (Matrix J J K)ˣ)
    (M : Matrix I J K) (x : J → K) :
    (A.val * M * B.val.transpose).mulVec (moveCutForm B x) = 0 ↔ M.mulVec x = 0 := by
  have hB : B.val.transpose * B.inv.transpose = 1 := by
    rw [← Matrix.transpose_mul, B.inv_val, Matrix.transpose_one]
  rw [moveCutForm, Matrix.mulVec_mulVec, Matrix.mul_assoc (A.val * M),
    hB, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact unit_mulVec_zero_iff A _

theorem left_form_transport (A : (Matrix I I K)ˣ) (B : (Matrix J J K)ˣ)
    (M : Matrix I J K) (x : I → K) :
    (A.val * M * B.val.transpose).transpose.mulVec (moveCutForm A x) = 0 ↔
      M.transpose.mulVec x = 0 := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
    right_form_transport B A M.transpose x

section PhysicalTensor

variable {l r n : Nat}

def rightCutKernel (T : Tensor K (l + r) n) : (Coord r n → K) →ₗ[K] (Coord l n → K) :=
  (flatten T).mulVecLin

def leftCutKernel (T : Tensor K (l + r) n) : (Coord l n → K) →ₗ[K] (Coord r n → K) :=
  (flatten T).transpose.mulVecLin

def moveRightForm (g : Changes K (l + r) n) (x : Coord r n → K) : Coord r n → K :=
  moveCutForm (productUnit (rightModes g)) x

def moveLeftForm (g : Changes K (l + r) n) (x : Coord l n → K) : Coord l n → K :=
  moveCutForm (productUnit (leftModes g)) x

theorem rightCutKernel_transport (g : Changes K (l + r) n) (T : Tensor K (l + r) n)
    (x : Coord r n → K) :
    rightCutKernel (act g T) (moveRightForm g x) = 0 ↔ rightCutKernel T x = 0 := by
  unfold rightCutKernel
  simp only [Matrix.mulVecLin_apply]
  rw [flatten_action]
  exact right_form_transport (productUnit (leftModes g)) (productUnit (rightModes g)) _ _

theorem leftCutKernel_transport (g : Changes K (l + r) n) (T : Tensor K (l + r) n)
    (x : Coord l n → K) :
    leftCutKernel (act g T) (moveLeftForm g x) = 0 ↔ leftCutKernel T x = 0 := by
  unfold leftCutKernel
  simp only [Matrix.mulVecLin_apply]
  rw [flatten_action]
  exact left_form_transport (productUnit (leftModes g)) (productUnit (rightModes g)) _ _

end PhysicalTensor

#print axioms moveCutForm_ne_zero
#print axioms rightCutKernel_transport
#print axioms leftCutKernel_transport

end EvenTI.Action
