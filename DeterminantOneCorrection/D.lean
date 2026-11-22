import Mathlib

namespace DetCorrectionNext.LocalRing

/-- The labelled lines remain distinct over a ring with zero divisors. -/
theorem slope_rotation {R : Type*} [CommRing R] (a b x y : Rˣ) :
    (∃ c : Rˣ, ((x * a : Rˣ) : R) = ((c * b : Rˣ) : R) ∧
      (y : R) = (c : R)) ↔ x / y = b / a := by
  constructor
  · rintro ⟨c, hxy, hy⟩
    have hc : y = c := Units.ext hy
    subst c
    have hd : x * a = y * b := Units.ext hxy
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_left_inj (a * y)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hd
  · intro h
    refine ⟨y, ?_, rfl⟩
    change ((x * a : Rˣ) : R) = ((y * b : Rˣ) : R)
    have hh := congrArg (fun z : Rˣ => (a * y) * z) h
    rw [div_eq_mul_inv, div_eq_mul_inv] at hh
    have hd : x * a = y * b := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hh
    exact congrArg (fun z : Rˣ => (z : R)) hd

/-- Repeating a pairing on free arrows gives the scalar multiplier to the arrow rank. -/
theorem scaled_perfect_pair {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (P Q : Matrix n n R) (t : R) (h : P.transpose * Q = t • 1) :
    P.det * Q.det = t ^ Fintype.card n := by
  rw [← Matrix.det_transpose P, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]

end DetCorrectionNext.LocalRing
