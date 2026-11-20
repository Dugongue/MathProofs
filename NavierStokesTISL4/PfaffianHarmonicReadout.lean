import Mathlib.Tactic.Ring

namespace PfaffianHarmonicReadout

/-- The nontrivial character weights in the finite ternary Pfaffian average. -/
theorem ternaryFourierWeights {R : Type*} [CommRing R] (ω : R)
    (h : 1 + ω + ω ^ 2 = 0) :
    ω + ω ^ 2 = -1 ∧
    ω ^ 2 - ω ^ 4 = -(ω - ω ^ 2) ∧
    ω ^ 2 + ω ^ 4 = -1 := by
  have hCube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (1 + ω + ω ^ 2) + 1 := by ring
      _ = 1 := by simp [h]
  have hFourth : ω ^ 4 = ω := by
    change ω ^ (3 + 1) = ω
    rw [pow_succ, hCube, one_mul]
  have hPair : ω + ω ^ 2 = -1 := by
    calc
      ω + ω ^ 2 = (1 + ω + ω ^ 2) - 1 := by ring
      _ = -1 := by rw [h, zero_sub]
  refine ⟨hPair, ?_, ?_⟩
  · rw [hFourth]
    ring
  · rw [hFourth, add_comm]
    exact hPair

end PfaffianHarmonicReadout

#print axioms PfaffianHarmonicReadout.ternaryFourierWeights
