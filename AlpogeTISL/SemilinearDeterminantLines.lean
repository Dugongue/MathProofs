import Mathlib.FieldTheory.Finite.Trace

/-!
# Scalar lines for semilinear determinant attachments

The conjugate multiplication chain reads a base-field norm. The unique
quadratic subfield in even extension degree supplies the Frobenius sign:
the quadratic Frobenius acts by minus one on its trace-zero line.
-/

namespace SemilinearDeterminantLines

open scoped BigOperators

theorem conjugate_product_transport
    (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E]
    (tau : E ≃ₐ[F] E) (a : E) (x : ℕ → E) :
    (∏ j ∈ Finset.range (Module.finrank F E), a ^ (Nat.card F ^ j) * tau (x j)) =
      algebraMap F E (Algebra.norm F a) *
        tau (∏ j ∈ Finset.range (Module.finrank F E), x j) := by
  rw [Finset.prod_mul_distrib, ← FiniteField.algebraMap_norm_eq_prod_pow, map_prod]

theorem quadratic_frobenius_on_trace_zero
    (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E]
    (degree : Module.finrank F E = 2) (x : E) (hx : Algebra.trace F E x = 0) :
    x ^ Nat.card F = -x := by
  have h := FiniteField.algebraMap_trace_eq_sum_pow F E x
  rw [hx, map_zero, degree] at h
  have hsum : x + x ^ Nat.card F = 0 := by
    simpa [Finset.sum_range_succ] using h.symm
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum)

end SemilinearDeterminantLines
