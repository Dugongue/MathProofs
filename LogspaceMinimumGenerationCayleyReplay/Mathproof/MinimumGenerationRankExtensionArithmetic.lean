import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs

namespace Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic

open Module

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A] [Fintype ι]

/-- The multiplication table of a basis can be computed before any operand
queries. One output coordinate then uses a double sum over independently
queriable coefficients. -/
theorem repr_mul_eq (basis : Basis ι R A) (x y : A) (k : ι) :
    basis.repr (x * y) k =
      ∑ i, ∑ j, (basis.repr x i * basis.repr y j) * basis.repr (basis i * basis j) k := by
  have hxy : x * y =
      ∑ i, ∑ j, (basis.repr x i * basis.repr y j) • (basis i * basis j) := calc
    _ = (∑ i, basis.repr x i • basis i) * (∑ j, basis.repr y j • basis j) := by
      rw [basis.sum_repr, basis.sum_repr]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hxy]
  simp only [map_sum, Finsupp.finsetSum_apply, LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul]

variable {p : Nat} [NeZero p]

/-- Reduce an entire natural-number sum once, after the bitwise scan of the
unreduced products. This applies in particular to a polynomial basis. -/
theorem product_digit_of_coordinate_words [Algebra (ZMod p) A]
    (basis : Basis ι (ZMod p) A) (x y : A) (k : ι) :
    (basis.repr (x * y) k).val =
      (∑ i, ∑ j, (basis.repr x i).val * (basis.repr y j).val *
        (basis.repr (basis i * basis j) k).val) % p := by
  rw [repr_mul_eq]
  have hcast : ((↑(∑ i, ∑ j, (basis.repr x i).val * (basis.repr y j).val *
      (basis.repr (basis i * basis j) k).val) : ZMod p)) =
      ∑ i, ∑ j, (basis.repr x i * basis.repr y j) * basis.repr (basis i * basis j) k := by
    simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast]

end Mathproof.MinimumGeneration.RankBerkowitz.ExtensionArithmetic
