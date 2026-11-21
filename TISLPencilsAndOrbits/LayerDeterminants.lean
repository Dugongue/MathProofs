import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CentroidOrientation

/-- The product of determinants on a family of length-h chains. -/
theorem layer_determinants {K : Type*} [CommRing K] (h r : ℕ)
    (a : K) (M : Matrix (Fin r) (Fin r) K) :
    (∏ j ∈ Finset.range h, ((a ^ j) • M).det) =
      a ^ (∑ j ∈ Finset.range h, j * r) * M.det ^ h := by
  simp_rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp

end CentroidOrientation
