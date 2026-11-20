import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

/-!
Square-zero correction for the adjoint-algebra norm equation.
This file checks the algebraic identities used in the radical lifting argument.
-/

namespace AlternatingTupleLifting

variable {R : Type*} [Ring R] [StarRing R]

/-- Congruence gives an affine transformation of a defect based at the identity. -/
theorem normDefect_affine (g z : R) :
    star g * (1 + z) * g - 1 =
      star g * z * g + (star g * g - 1) := by
  simp only [mul_add, mul_one, add_mul]
  abel

/-- The linear part of congruence preserves the trace image. -/
theorem normDefect_preservesTrace (g a : R) :
    star g * (a + star a) * g =
      star g * a * g + star (star g * a * g) := by
  simp only [mul_add, add_mul, star_mul, star_star, mul_assoc]

/-- At a square-zero grade the nonlinear terms vanish identically. -/
theorem squareZeroNormCorrection (I : AddSubgroup R)
    (starClosed : ∀ a ∈ I, star a ∈ I)
    (squareZero : ∀ a ∈ I, ∀ b ∈ I, a * b = 0)
    {x z : R} (hx : x ∈ I) (hz : z ∈ I) :
    star (1 + x) * (1 + z) * (1 + x) = 1 + (z + (x + star x)) := by
  have hsx := starClosed x hx
  have hsz := squareZero (star x) hsx z hz
  have hsxx := squareZero (star x) hsx x hx
  have hzx := squareZero z hz x hx
  simp only [star_add, star_one, add_mul, mul_add, one_mul, mul_one,
    hsz, hsxx, hzx, zero_add, add_zero]
  abel

/-- A representative over the identity lifts exactly when its defect lies in the trace image. -/
theorem squareZeroNormCorrectable (I : AddSubgroup R)
    (starClosed : ∀ a ∈ I, star a ∈ I)
    (squareZero : ∀ a ∈ I, ∀ b ∈ I, a * b = 0)
    {z : R} (hz : z ∈ I) :
    (∃ x ∈ I, star (1 + x) * (1 + z) * (1 + x) = 1) ↔
      ∃ x ∈ I, z + (x + star x) = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [squareZeroNormCorrection I starClosed squareZero hx hz] at h
    exact ⟨x, hx, add_left_cancel (h.trans (add_zero (1 : R)).symm)⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    rw [squareZeroNormCorrection I starClosed squareZero hx hz, h, add_zero]

#print axioms AlternatingTupleLifting.normDefect_affine
#print axioms AlternatingTupleLifting.normDefect_preservesTrace
#print axioms AlternatingTupleLifting.squareZeroNormCorrection
#print axioms AlternatingTupleLifting.squareZeroNormCorrectable

end AlternatingTupleLifting
