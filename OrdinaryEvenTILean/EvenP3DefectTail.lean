import EvenP3SelectedForms

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical
open EvenTI.Primary

noncomputable section

/-- A chosen form of high defect has small raw-source probability,
with no weighting by the number of forms in its exact cut kernel. -/
theorem selected_defect_tail {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (right : Bool) (b : ℕ) (hb : 0 < b) :
    event (fun T : Four K n => ∃ v, selectCutForm right T = some v ∧ b ≤ formDefect v)
      ≤ 4 / (b : ℝ)^2 := by
  have hpos : 0 < (b : ℝ)^2 := by positivity
  apply (le_div_iff₀' hpos).mpr
  refine le_trans ?_ (mean_selected_square_defect (K := K) (n := n) right)
  rw [event, ← mean_mul]
  apply mean_mono
  intro T
  by_cases he : ∃ v, selectCutForm right T = some v ∧ b ≤ formDefect v
  · rw [if_pos he, mul_one]
    obtain ⟨v, hv, hvb⟩ := he
    rw [hv, Option.elim_some]
    exact_mod_cast Nat.pow_le_pow_left hvb 2
  · simp only [if_neg he, mul_zero]
    cases selectCutForm right T <;> simp

#print axioms selected_defect_tail

end
end Mathproof.EvenTI.OrderFour
