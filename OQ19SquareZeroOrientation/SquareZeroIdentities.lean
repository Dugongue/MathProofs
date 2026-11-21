import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel

namespace OQ19SquareZero

theorem unitary_correction {R : Type*} [Monoid R] [StarMul R] {v w : R}
    (hw : star w = w) (h : w * (star v * v) * w = 1) :
    star (v * w) * (v * w) = 1 := by
  rw [star_mul, hw]
  simpa only [mul_assoc] using h

theorem squareZero_midpoint_mul {F A : Type*} [CommRing F] [Ring A] [Algebra F A]
    (half : F) (a b dx dy : A) (h : dx * dy = 0) :
    (a + half • dx) * (b + half • dy) =
      a * b + half • (a * dy + dx * b) := by
  simp only [add_mul, mul_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, h,
    smul_zero, add_zero, smul_add]
  abel

theorem reverse_signed_swap {G : Type*} [Monoid G] (s t : G)
    (hs : s * s = 1) (ht : t * t = 1) (hcomm : s * t = t * s) :
    (s * t) * (s * t) = 1 := by
  calc
    (s * t) * (s * t) = s * (t * s) * t := by simp only [mul_assoc]
    _ = 1 := by rw [← hcomm, ← mul_assoc s s t, hs, one_mul, ht]

theorem even_power_of_involution {G : Type*} [Monoid G] (s : G)
    (hs : s * s = 1) (n : ℕ) : s ^ (2 * n) = 1 := by
  rw [pow_mul, pow_two, hs, one_pow]

end OQ19SquareZero
