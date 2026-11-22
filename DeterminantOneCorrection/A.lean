import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

namespace DetCorrectionNext.CyclicMarker

open Matrix

/-- Opposite semilinear arrow maps cancel the inner conjugator's determinant. -/
theorem paired_arrow_determinants {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (X Y : Matrix n n K) (a b : K) (h : X * Y = 1) :
    (a • X).det * (b • Y).det = (a * b) ^ Fintype.card n := by
  have hd : X.det * Y.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [Matrix.det_smul, Matrix.det_smul, mul_pow]
  calc
    (a ^ Fintype.card n * X.det) * (b ^ Fintype.card n * Y.det)
      = (a ^ Fintype.card n * b ^ Fintype.card n) * (X.det * Y.det) := by ring
    _ = a ^ Fintype.card n * b ^ Fintype.card n := by rw [hd, mul_one]

/-- Marker multiplicity makes common scalar normalization an L-th power. -/
theorem balanced_marker_scaling {K : Type*} [Field K] (t : K) (r L : ℕ)
    (h : L ∣ 3 + r) : ∃ u : K, t ^ 2 * t * t ^ r = u ^ L := by
  obtain ⟨s, hs⟩ := h
  refine ⟨t ^ s, ?_⟩
  calc
    t ^ 2 * t * t ^ r = t ^ (3 + r) := by
      rw [pow_add, show t ^ 3 = t ^ 2 * t from pow_succ t 2]
    _ = t ^ (s * L) := by rw [hs, Nat.mul_comm L s]
    _ = (t ^ s) ^ L := pow_mul t s L

end DetCorrectionNext.CyclicMarker
