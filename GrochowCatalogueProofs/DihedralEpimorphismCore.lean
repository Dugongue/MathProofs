import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.FinCases

namespace DihedralEpimorphism

/-- The rank-one Boolean recovery at the heart of the reduction. -/
theorem rankOneBooleanRecovery {ι : Type*} (anchor : ι) (u v : ι → ZMod 2)
    (nonzero : ∃ i j, u i * v j ≠ 0)
    (symmetric : ∀ i j, u i * v j = u j * v i)
    (normalized : ∀ i, i ≠ anchor → u i * v i = u anchor * v i) :
    u = v ∧ u anchor = 1 := by
  have bit : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  obtain ⟨i, j, hij⟩ := nonzero
  have hui : u i = 1 := bit (u i) (by
    intro hz
    apply hij
    simp [hz])
  have hs : u j * v i ≠ 0 := by
    rwa [← symmetric i j]
  have hvi : v i = 1 := bit (v i) (by
    intro hz
    apply hs
    simp [hz])
  have heq : u = v := by
    funext k
    simpa only [hui, hvi, mul_one, one_mul] using symmetric k i
  refine ⟨heq, ?_⟩
  by_cases h : i = anchor
  · simpa only [h] using hui
  · have hn := normalized i h
    simp only [hui, hvi, mul_one] at hn
    exact hn.symm

/-- The rotation parity and reflection parity coordinates of the central quotient. -/
def centreQuotientCoordinates : DihedralGroup 4 → ZMod 2 × ZMod 2
  | .r i => ((i.val : ZMod 2), 0)
  | .sr i => ((i.val : ZMod 2), 1)

/-- The alternating determinant pairing on the two quotient coordinates. -/
def commutatorBit (a b : DihedralGroup 4) : ZMod 2 :=
  let (x₁, x₂) := centreQuotientCoordinates a
  let (y₁, y₂) := centreQuotientCoordinates b
  x₁ * y₂ - x₂ * y₁

/-- The bit is the exponent of the central rotation in the actual group commutator. -/
theorem dihedralCommutatorFormula (a b : DihedralGroup 4) :
    a * b * a⁻¹ * b⁻¹ = DihedralGroup.r (2 * ((commutatorBit a b).val : ZMod 4)) := by
  cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;> decide

end DihedralEpimorphism

#print axioms DihedralEpimorphism.rankOneBooleanRecovery
#print axioms DihedralEpimorphism.dihedralCommutatorFormula
