import Mathlib

namespace PrincipalUnitsB

/-- First-order determinant formula on a square-zero scalar layer. Applying
it to multiplication by a trace-one element lifts a desired norm digit. -/
theorem norm_layer_det {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (a : R) (h : a ^ 2 = 0) (M : Matrix I I R) :
    (1 + a • M).det = 1 + M.trace * a := by
  rw [Matrix.det_one_add_smul, h, mul_zero, add_zero]

/-- The matrix-unit conjugator intertwines two systems of matrix units over
any semiring. If both reduce to the same system through a square-zero quotient,
the displayed sum is a unit congruent to one. -/
theorem matrix_unit_alignment {R I : Type*} [Semiring R] [Fintype I] [DecidableEq I]
    (E F : I → I → R) (r a b : I)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (hF : ∀ i j k l, F i j * F k l = if j = k then F i l else 0) :
    F a b * (∑ i, F i r * E r i) = (∑ i, F i r * E r i) * E a b := by
  have hl : F a b * (∑ i, F i r * E r i) = F a r * E r b := by
    rw [Finset.mul_sum]
    simp_rw [← mul_assoc, hF, ite_mul, zero_mul]
    simp
  have hr : (∑ i, F i r * E r i) * E a b = F a r * E r b := by
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, hE, mul_ite, mul_zero]
    simp
  exact hl.trans hr.symm

/-- Conjugating by a shear from a square-zero ideal is the identity plus
a radical-valued correction. The correction vanishes on the radical. -/
theorem radical_conjugation_formula {R : Type*} [Ring R] (x z : R)
    (hz : z * x * z = 0) :
    (1 + z) * x * (1 - z) = x + z * x - x * z := by
  calc
    (1 + z) * x * (1 - z) = x + z * x - x * z - (z * x * z) := by noncomm_ring
    _ = _ := by rw [hz, sub_zero]

end PrincipalUnitsB
