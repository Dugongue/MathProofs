import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace SymmetricCircuitAdvances

open Matrix

theorem determinantOfSandwichPencil {R I : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] (L A W : Matrix I I R) (z : R) :
    Matrix.det (z • (L * W) - (L * A) * W) =
      Matrix.det (L * W) * Matrix.det (z • (1 : Matrix I I R) - A) := by
  have h : z • (L * W) - (L * A) * W =
      (L * (z • (1 : Matrix I I R) - A)) * W := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  ring

theorem determinantFromReciprocal {K I : Type*} [Field K]
    [Fintype I] [DecidableEq I] (L A W : Matrix I I K)
    (h : Matrix.det (L * W) ≠ 0) :
    Matrix.det ((L * A) * W) / Matrix.det (L * W) = Matrix.det A := by
  apply (div_eq_iff h).2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  ring

theorem diagonalBlockIndexBound (l : ℕ) (hl : 2 ≤ l) :
    2 ^ l ≤ 60 ^ (l - 1) := by
  calc
    2 ^ l ≤ 2 ^ (2 * (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ (l - 1) := by rw [pow_mul]; norm_num
    _ ≤ 60 ^ (l - 1) := Nat.pow_le_pow_left (by decide) _

theorem previousPaddingDoesNotEraseGap {K : Type*} [Field K]
    (h : (2 : K) ≠ 0) (v : ℕ) : (2 : K) ^ (4 * v + 1) ≠ 0 :=
  pow_ne_zero _ h

end SymmetricCircuitAdvances
