import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Polynomial.Coeff

namespace GrochowCatalogueFifth

/-- The two-state lift of a rectangular layer transition computes the
    product rule on its off-diagonal block. -/
theorem firstJet_recurrence {R m n p : Type*} [Semiring R] [Fintype n]
    (A dA : Matrix m n R) (B dB : Matrix n p R) :
    Matrix.fromBlocks A dA 0 A * Matrix.fromBlocks B dB 0 B =
      Matrix.fromBlocks (A * B) (A * dB + dA * B) 0 (A * B) := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The first jet of a product can also be evaluated by the scalar transfer
    rule, including when any factor has zero constant term. -/
theorem firstJet_product {R : Type*} [Semiring R] (P : List (Polynomial R)) :
    (P.prod.coeff 0, P.prod.coeff 1) =
      P.foldr (fun f j : _ =>
        (f.coeff 0 * j.1, f.coeff 0 * j.2 + f.coeff 1 * j.1)) (1, 0) := by
  induction P with
  | nil => simp [Polynomial.coeff_one]
  | cons f tail ih =>
      simp only [List.prod_cons, List.foldr_cons, Polynomial.mul_coeff_zero,
        Polynomial.mul_coeff_one]
      rw [← ih]

end GrochowCatalogueFifth

#print axioms GrochowCatalogueFifth.firstJet_recurrence
#print axioms GrochowCatalogueFifth.firstJet_product
