import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

namespace MixedGraphPC

variable {R i j k l : Type*} [CommRing R]
variable [Fintype i] [Fintype j] [Fintype k] [Fintype l]

theorem form_preparation [DecidableEq j]
    (X : Matrix k i R) (A : Matrix i j R) (Z : Matrix l j R)
    (Y : Matrix j l R) (B : Matrix k l R) :
    X * A - B * Y.transpose =
      (X * A * Z.transpose - B) * Y.transpose -
        X * A * (Y * Z - 1).transpose := by
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem reverse_preparation [DecidableEq i] [DecidableEq l]
    (X : Matrix k i R) (A : Matrix i j R) (Z : Matrix l j R)
    (Y : Matrix j l R) (B : Matrix k l R) (W : Matrix i k R) :
    A * Y - W * B =
      W * (X * A - B * Z) * Y +
        (1 - W * X) * A * Y +
        W * B * (Z * Y - 1) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

end MixedGraphPC
