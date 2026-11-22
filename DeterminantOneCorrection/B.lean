import Mathlib

open Matrix
open scoped Kronecker

namespace DetCorrectionB

/-- A square-zero radical inner shear factors through the radical and
vanishes on it. Its determinant is one in the original coordinates. -/
theorem radical_shear_det_one {R u v : Type*} [CommRing R]
    [Fintype u] [DecidableEq u] [Fintype v] [DecidableEq v]
    (P : Matrix u v R) (Q : Matrix v u R) (h : Q * P = 0) :
    (1 + P * Q).det = 1 := by
  rw [Matrix.det_one_add_mul_comm, h, add_zero, Matrix.det_one]

/-- Acting on only the multiplicity index contributes one determinant
for each pair of natural matrix coordinates. -/
theorem radical_multiplicity_det {R u v w : Type*} [CommRing R]
    [Fintype u] [DecidableEq u] [Fintype v] [DecidableEq v]
    [Fintype w] [DecidableEq w] (H : Matrix w w R) :
    (((1 : Matrix u u R) ⊗ₖ (1 : Matrix v v R)) ⊗ₖ H).det =
      H.det ^ (Fintype.card u * Fintype.card v) := by
  simp [Matrix.det_kronecker, Fintype.card_prod]

/-- Paired permutations give an even permutation on the sum, independently
of the sign of the underlying label permutation. -/
theorem twin_permutation_det_one {R u : Type*} [CommRing R]
    [Fintype u] [DecidableEq u] (σ : Equiv.Perm u) :
    (Equiv.Perm.permMatrix R (Equiv.sumCongr σ σ)).det = 1 := by
  rw [Matrix.det_permutation, Equiv.Perm.sign_sumCongr, Int.units_mul_self]
  simp

end DetCorrectionB
