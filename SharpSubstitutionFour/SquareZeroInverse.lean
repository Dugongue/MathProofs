import Mathlib.Tactic.NoncommRing

namespace SharpSubstitutionFour

theorem square_zero_perturbation_inverse {R : Type*} [Ring R] (a b n : R)
    (hab : a * b = 1) (hba : b * a = 1) (hn : n * b * n = 0) :
    (a + n) * (b - b * n * b) = 1 ∧ (b - b * n * b) * (a + n) = 1 := by
  constructor
  · calc
      (a + n) * (b - b * n * b) =
          a * b - (a * b) * n * b + n * b - (n * b * n) * b := by noncomm_ring
      _ = 1 := by simp [hab, hn]
  · calc
      (b - b * n * b) * (a + n) =
          b * a + b * n - b * n * (b * a) - b * (n * b * n) := by noncomm_ring
      _ = 1 := by simp [hba, hn]

end SharpSubstitutionFour
