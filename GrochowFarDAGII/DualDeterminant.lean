import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace GaloisMarks

/-- A map and its inverse dual together have determinant one. -/
theorem det_block_inverse_dual {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) (h : A * B = 1) :
    (Matrix.fromBlocks A 0 0 B.transpose).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, ← Matrix.det_mul, h, Matrix.det_one]

end GaloisMarks
