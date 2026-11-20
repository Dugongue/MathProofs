import EvenP3FormMoment

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical Matrix
open Matrix Module EvenTI.Primary EvenTI.Action
open Mathproof.EvenTI.Singular.Coverage Mathproof.EvenTI.Singular.Forms
open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)

noncomputable section

/-- Any choice of a nonzero killed form has no more expected nonnegative cost
than a uniformly sampled form, provided each specified form is killed at
most with the inverse ambient cardinality. Missing choices cost zero. -/
theorem mean_option_selection_le_uniform {Ω V : Type*} [Fintype Ω] [Fintype V]
    (choose : Ω → Option V) (cost : V → ℝ) (hc : ∀ v, 0 ≤ cost v)
    (h : ∀ v, weight choose (some v) ≤ (Fintype.card V : ℝ)⁻¹) :
    mean (fun x => (choose x).elim 0 cost) ≤ mean cost := by
  let C (v : Option V) := v.elim 0 cost
  change mean (C ∘ choose) ≤ _
  rw [mean_comp_eq_weight, Fintype.sum_option]
  simp only [C, Option.elim_none, zero_mul, zero_add, Option.elim_some]
  calc
    _ ≤ ∑ v, cost v * (Fintype.card V : ℝ)⁻¹ :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h v) (hc v)
    _ = _ := by unfold mean; simp only [← Finset.sum_mul, div_eq_mul_inv]

def chooseNonzero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) : Option V :=
  if h : ∃ v, v ≠ 0 ∧ v ∈ U then some (Classical.choose h) else none

theorem chooseNonzero_spec {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U : Submodule K V} {v : V} (h : chooseNonzero U = some v) :
    v ≠ 0 ∧ v ∈ U := by
  unfold chooseNonzero at h
  split at h
  · rename_i h'
    cases Option.some.inj h
    exact Classical.choose_spec h'
  · contradiction

theorem chooseNonzero_some {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (h : ∃ v, v ≠ 0 ∧ v ∈ U) :
    ∃ v, chooseNonzero U = some v := by
  exact ⟨Classical.choose h, dif_pos h⟩

variable {K : Type*} [Field K] {n : ℕ}

abbrev Four (K : Type*) [Field K] (n : ℕ) := Tensor K ((1+1)+(1+1)) n
abbrev Forms (K : Type*) (n : ℕ) := Coord (1+1) n → K

def fourCutMap (right : Bool) (T : Four K n) : Forms K n →ₗ[K] Forms K n :=
  if right then rightCutKernel T else leftCutKernel T

def selectCutForm (right : Bool) (T : Four K n) : Option (Forms K n) :=
  chooseNonzero (fourCutMap right T).ker

theorem selectCutForm_of_singular (right : Bool) (T : Four K n)
    (h : (flatten T).det = 0) : ∃ v, selectCutForm right T = some v := by
  apply chooseNonzero_some
  cases right
  · obtain ⟨v, hv, hz⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (flatten T)ᵀ)).mpr
      (by rwa [Matrix.det_transpose])
    exact ⟨v, hv, hz⟩
  · obtain ⟨v, hv, hz⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := flatten T)).mpr h
    exact ⟨v, hv, hz⟩

theorem mean_selectCutForm_le_uniform [Fintype K] (right : Bool)
    (cost : Forms K n → ℝ) (hc : ∀ v, 0 ≤ cost v) :
    mean (fun T => (selectCutForm right T).elim 0 cost) ≤ mean cost := by
  apply mean_option_selection_le_uniform _ cost hc
  intro v
  rw [weight, event_as_fraction]
  by_cases hv : v = 0
  · have he : (fun T : Four K n => selectCutForm right T = some v) = fun _ => False := by
      funext T
      exact propext ⟨fun h => (chooseNonzero_spec h).1 hv, False.elim⟩
    rw [he]
    simp [uniformFraction]
  · have h := uniformFraction_le_of_imp
      (fun (T : Four K n) (h : selectCutForm right T = some v) => (chooseNonzero_spec h).2)
    refine h.trans_eq ?_
    change uniformFraction (Four K n) (fun T => fourCutMap right T v = 0) = _
    cases right
    · rw [show (fun T : Four K n => fourCutMap false T v = 0) =
          (fun T => leftCutKernel T v = 0) from rfl, leftCutKernel_zero_fraction v hv]
      rw [Fintype.card_fun, cut_side_card, Nat.cast_pow, one_div]
    · rw [show (fun T : Four K n => fourCutMap true T v = 0) =
          (fun T => rightCutKernel T v = 0) from rfl, rightCutKernel_zero_fraction v hv]
      rw [Fintype.card_fun, cut_side_card, Nat.cast_pow, one_div]

theorem mean_selected_square_defect [Fintype K] (right : Bool) :
    mean (fun T : Four K n => (selectCutForm right T).elim (0 : ℝ)
      (fun v => ((formDefect v)^2 : ℕ))) ≤ 4 :=
  (mean_selectCutForm_le_uniform right _ (fun _ => by positivity)).trans mean_square_form_defect

#print axioms mean_selectCutForm_le_uniform
#print axioms mean_selected_square_defect
#print axioms selectCutForm_of_singular

end
end Mathproof.EvenTI.OrderFour
