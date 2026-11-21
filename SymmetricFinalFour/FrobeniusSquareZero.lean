import Mathlib.Algebra.CharP.Lemmas

namespace SymmetricFinalFour

theorem frobenius_ignores_square_zero {R : Type*} [CommRing R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (x y : R) (hy : y ^ 2 = 0) :
    (x + y) ^ p = x ^ p := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hz : y ^ p = 0 := by
    calc
      y ^ p = y ^ (p - 2 + 2) := by rw [Nat.sub_add_cancel hp]
      _ = 0 := by rw [pow_add, hy, mul_zero]
  rw [add_pow_char, hz, add_zero]

end SymmetricFinalFour
