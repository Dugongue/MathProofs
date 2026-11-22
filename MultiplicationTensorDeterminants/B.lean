import Mathlib

namespace DetRatioB

/-- Scaling one variable on a rectangular truncated monomial basis gives
the power obtained by summing that variable's exponents. The second index
stands for all remaining monomial coordinates. -/
theorem monomial_coordinate_det {R β : Type*} [CommRing R] [Fintype β]
    [DecidableEq β] (m : ℕ) (t : R) :
    (Matrix.diagonal (fun b : Fin m × β => t ^ b.1.val)).det =
      t ^ (Fintype.card β * (m * (m - 1) / 2)) := by
  have he : (∏ i : Fin m, t ^ i.val) = t ^ (m * (m - 1) / 2) := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) m).trans (Finset.sum_range_id m)
  rw [Matrix.det_diagonal, Fintype.prod_prod_type_right]
  simp only [he, Finset.prod_const, Finset.card_univ, ← pow_mul]
  rw [Nat.mul_comm]

/-- A finite-field linear transformation of order prime to the scalar
multiplicative group has trivial determinant. -/
theorem prime_to_scalar_order_det {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (r : ℕ)
    (hr : r ≠ 0) (hc : Nat.Coprime r (Fintype.card K - 1)) (hM : M ^ r = 1) :
    M.det = 1 := by
  have hn := congrArg Matrix.det hM
  rw [Matrix.det_pow, Matrix.det_one] at hn
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, zero_pow hr] at hn
    exact zero_ne_one hn
  have hu := FiniteField.pow_card_sub_one_eq_one M.det hdet
  apply orderOf_eq_one_iff.1
  apply Nat.dvd_one.1
  rw [← hc.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hu)

/-- Twisting one side of a nondegenerate bilinear pairing has determinant
equal to the square of a simultaneous change of coordinates on that pairing. -/
theorem gram_twist_det_square {R ι : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [DecidableEq ι] (B X U : Matrix ι ι R)
    (hB : B.det ≠ 0) (h : X.transpose * B * X = U.transpose * B) :
    X.det ^ 2 = U.det := by
  have he := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_transpose] at he
  apply mul_right_cancel₀ hB
  calc
    X.det ^ 2 * B.det = X.det * B.det * X.det := by ring
    _ = U.det * B.det := he

end DetRatioB
