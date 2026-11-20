import EvenP3DefectTail

namespace Mathproof.EvenTI.OrderFour

open scoped Classical
open Module Matrix EvenTI.Primary EvenTI.Action
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenTI.Singular.Coverage

noncomputable section

private theorem event_or_le {A : Type*} [Fintype A] (p q : A → Prop) :
    event (fun x => p x ∨ q x) ≤ event p + event q := by
  let f (a : A) : ℝ := if p a then 1 else 0
  let g (a : A) : ℝ := if q a then 1 else 0
  have h (x : A) :
      (@ite ℝ (p x ∨ q x) (Classical.propDecidable _) 1 0) ≤ f x + g x := by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [f,g,hp,hq]
  change mean (fun x => @ite ℝ (p x ∨ q x) (Classical.propDecidable _) 1 0) ≤ _
  refine (mean_mono h).trans_eq ?_
  simp only [event, mean, f, g, Finset.sum_add_distrib, add_div]

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

def lowRankSelectedForm (right : Bool) (T : Four K n) (b : ℕ) : Prop :=
  ∃ v, selectCutForm right T = some v ∧ b ≤ formDefect v

def singularPreliminaryException (T : Four K n) (b : ℕ) : Prop :=
  n < Fintype.card K ^ finrank K (rightCutKernel T).ker ∨
    lowRankSelectedForm false T b ∨ lowRankSelectedForm true T b

/-- The high cut-corank and high selected-form-defect exceptions are
both measured on the original uniform dense source. -/
theorem singular_preliminary_exception_bound (hn : 0 < n) (b : ℕ) (hb : 0 < b) :
    event (fun T : Four K n => singularPreliminaryException T b) ≤
      2 / (n : ℝ) + 8 / (b : ℝ)^2 := by
  let h (T : Four K n) := n < Fintype.card K ^ finrank K (rightCutKernel T).ker
  have h₁ : event h ≤ 2 / (n : ℝ) := square_cut_large_corank hn
  have h₂ := selected_defect_tail (K := K) (n := n) false b hb
  have h₃ := selected_defect_tail (K := K) (n := n) true b hb
  exact (event_or_le h _).trans <| (add_le_add h₁ ((event_or_le _ _).trans
    (add_le_add h₂ h₃))).trans_eq (by ring)

#print axioms singular_preliminary_exception_bound

end
end Mathproof.EvenTI.OrderFour
