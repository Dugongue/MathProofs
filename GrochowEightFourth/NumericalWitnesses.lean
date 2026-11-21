import Mathlib.Tactic

open scoped BigOperators

namespace NumericalWitnesses

/-- Exact on the audited operations. Values outside the rounding cell of 1
are only used when the exact result is already representable in binary64. -/
def roundAtOne (x : ℚ) : ℚ :=
  if 1 - 1 / (2 : ℚ)^54 < x ∧ x < 1 + 1 / (2 : ℚ)^53 then 1 else x

def binary64ResidualStep (r : ℚ × ℚ) : ℚ × ℚ :=
  let rnd := roundAtOne
  let ar₁ := rnd r.1
  let ar₂ := rnd (r.2 / (2 : ℚ)^60)
  let num := rnd (rnd (r.1 * r.1) + rnd (r.2 * r.2))
  let den := rnd (rnd (r.1 * ar₁) + rnd (r.2 * ar₂))
  let α := rnd (num / den)
  (rnd (r.1 - rnd (α * ar₁)), rnd (r.2 - rnd (α * ar₂)))

theorem binary64ResidualCycle :
    binary64ResidualStep (1, 1) = (-1, 1) ∧
      binary64ResidualStep (-1, 1) = (1, 1) := by
  norm_num [binary64ResidualStep, roundAtOne]

theorem finiteWeightedCentered {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∑ i, w i = 1) (c : ℝ) :
    (∑ i, w i * (x i - c)^2) =
      (∑ i, w i * (x i)^2) - (∑ i, w i * x i)^2 +
        ((∑ i, w i * x i) - c)^2 := by
  have expand (i : ι) : w i * (x i - c)^2 =
      w i * (x i)^2 - (w i * x i) * (2 * c) + w i * c^2 := by ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hw]
  ring

#print axioms binary64ResidualCycle
#print axioms finiteWeightedCentered

end NumericalWitnesses
