import Mathlib.Algebra.Polynomial.Coeff

namespace CoefficientWorlds

theorem cancel_formal_scalar {R : Type*} [Semiring R] (P Q : Polynomial R) (k : ℕ)
    (h : Polynomial.X ^ k * P = Polynomial.X ^ k * Q) : P = Q := by
  ext i
  rw [← Polynomial.coeff_X_pow_mul P k i, h, Polynomial.coeff_X_pow_mul Q k i]

theorem read_unit_coefficient {R : Type*} [CommSemiring R]
    (P : Polynomial R) (k : ℕ) (a b : R) (hP : P.coeff 0 = 1)
    (h : Polynomial.X ^ k * (Polynomial.C a * P) =
        Polynomial.X ^ k * (Polynomial.C b * P)) : a = b := by
  have same := cancel_formal_scalar _ _ k h
  have constant := congrArg (fun Q : Polynomial R => Q.coeff 0) same
  simpa [Polynomial.coeff_C_mul, hP] using constant

end CoefficientWorlds
