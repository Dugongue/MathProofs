import EvenP3SingularExceptions
import EvenP3FiberAssembly
import EvenP3SingularPack
import EvenP2Source

namespace Mathproof.EvenTI.OrderFour

open scoped BigOperators Classical Matrix
open Matrix Module EvenTI.Primary EvenTI.Action
open Mathproof.EvenOrdinaryTISingular Mathproof.EvenOrdinaryTISingular.EnlargedCut
open Mathproof.EvenTI.Singular.Coverage Mathproof.Problem17RepeatedBudget

noncomputable section

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

private def trialForm (U : Submodule K (Forms K n)) : Forms K n :=
  (chooseNonzero U).getD 0

private def leftForm (k : KernelPair K 1 n) := trialForm k.2
private def rightForm (k : KernelPair K 1 n) := trialForm k.1

private def goodTrial (k : KernelPair K 1 n) : Prop :=
  leftForm k ≠ 0 ∧ rightForm k ≠ 0 ∧ Fintype.card K ^ finrank K k.1 ≤ n ∧
  n ≤ 3 * min (formWidth (leftForm k)) (formWidth (rightForm k))

private theorem trialForm_mem (U : Submodule K (Forms K n)) : trialForm U ∈ U := by
  unfold trialForm
  cases h : chooseNonzero U with
  | none => exact U.zero_mem
  | some v => exact (chooseNonzero_spec h).2

private def formFor (k : KernelPair K 1 n) (i : Bool) :=
  if i then rightForm k else leftForm k

private def trialCost (k : KernelPair K 1 n) (i : Bool) (T : Four K n) : ℕ :=
  repeatedBudget (if i then rawEnlargedRightPoly (leftForm k) (rightForm k) T
    else rawEnlargedLeftPoly (leftForm k) (rightForm k) T)

private def activeCost (i : Bool) (T : Four K n) : ℕ :=
  if goodTrial (exactKernels T) then trialCost (exactKernels T) i T else 0

private theorem mean_equiv' {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (f ∘ e) = mean f := by
  unfold mean
  change (∑ x, f (e x)) / Fintype.card A = (∑ x, f x) / Fintype.card B
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private theorem formFor_eq (i : Bool) (T : Four K n) :
    formFor (exactKernels T) i = (selectCutForm i T).getD 0 := by
  cases i <;> rfl

private theorem mean_trial_form_defect (i : Bool) :
    mean (fun T : Four K n => ((formDefect (formFor (exactKernels T) i) ^ 2 : ℕ) : ℝ) *
      (if goodTrial (exactKernels T) then 1 else 0)) ≤ 4 := by
  refine (mean_mono (Y := fun T : Four K n => (selectCutForm i T).elim (0 : ℝ)
    (fun v => ((formDefect v ^ 2 : ℕ) : ℝ))) ?_).trans (mean_selected_square_defect i)
  intro T
  by_cases h : goodTrial (exactKernels T)
  · have hnz : formFor (exactKernels T) i ≠ 0 := by
      cases i
      · exact h.1
      · exact h.2.1
    rw [formFor_eq] at hnz ⊢
    cases hz : selectCutForm i T with
    | none => exact False.elim (hnz (by simp [hz]))
    | some v => simp [hz, h]
  · simp only [if_neg h, mul_zero]
    cases selectCutForm i T <;> simp

set_option maxHeartbeats 1200000 in
private theorem mean_active_cost_le (hn : 1024 ≤ n) (i : Bool) :
    mean (fun T : Four K n => (activeCost i T : ℝ)) ≤
      8 * (budgetConstant K + 1) + 34 := by
  let key : Four K n → KernelPair K 1 n := exactKernels
  haveI : Finite (Submodule K (CutSide K 1 n)) :=
    Finite.of_injective (fun U : Submodule K (CutSide K 1 n) => (U : Set (CutSide K 1 n)))
      SetLike.coe_injective
  letI : Fintype (KernelPair K 1 n) := Fintype.ofFinite _
  let C : ℝ := 8 * (budgetConstant K + 1) + 2
  have hC : 0 ≤ C := by dsimp [C]; linarith [budgetConstant_nonneg (K := K)]
  let d (T : Four K n) : ℝ := ((formDefect (formFor (key T) i) ^ 2 : ℕ) : ℝ) *
    (if goodTrial (key T) then 1 else 0)
  let centered (T : Four K n) : ℝ := (activeCost i T : ℝ) - 8*d T
  have hμ : mean centered ≤ C := by
    apply mean_le_of_exact_fibers key centered C hC
    intro k
    by_cases hg : goodTrial k
    · by_cases hx : Nonempty (DenseKernelFiber k.1 k.2)
      · let A₀ := Classical.choice hx
        letI : Nonempty (DenseKernelFiber k.1 k.2) := hx
        letI : Fintype (DenseKernelFiber k.1 k.2) := Fintype.ofFinite _
        let e : DenseKernelFiber k.1 k.2 ≃ {a : Four K n // key a = k} := exactKernelsEquiv k
        let f (x : {a : Four K n // key a = k}) := centered x.val
        have hShift (F : Fintype {a : Four K n // key a = k}) :
            @mean _ F f = mean (f ∘ e) := (@mean_equiv' _ _ inferInstance F e f).symm
        refine (hShift _).trans_le ?_
        have hc := raw_enlarged_fiber_primary_means A₀ (trialForm_mem k.2) (trialForm_mem k.1)
          hn hg.2.2.1 hg.2.2.2
        have he (A : DenseKernelFiber k.1 k.2) : key (e A).val = k := (e A).property
        have hs (u : DenseKernelFiber k.1 k.2 → ℝ) (v : ℝ) :
            mean (fun A => u A - v) = mean u - v := by
          have hcard : (Fintype.card (DenseKernelFiber k.1 k.2) : ℝ) ≠ 0 := by positivity
          simp [mean, Finset.sum_sub_distrib, sub_div, mul_comm v, hcard]
        have hCenter : f ∘ e =
            fun A => (trialCost k i A.val : ℝ) - 8 * (↑(formDefect (formFor k i) ^ 2) : ℝ) := by
          funext A
          simp only [Function.comp_apply, f, centered, activeCost, ← show key = exactKernels from rfl,
            he, if_pos hg, d, mul_one] <;> rfl
        rw [hCenter, hs]
        cases i
        · simp only [trialCost, formFor, Bool.false_eq_true, if_false]
          apply sub_le_iff_le_add.mpr
          simpa only [leftForm, rightForm, C] using hc.1
        · simp only [trialCost, formFor, if_true]
          apply sub_le_iff_le_add.mpr
          simpa only [leftForm, rightForm, C] using hc.2
      · letI : IsEmpty {a : Four K n // key a = k} :=
          ⟨fun x => hx ⟨(exactKernelsEquiv k).symm x⟩⟩
        simp [mean, hC]
    · have hzero (T : {a : Four K n // key a = k}) : centered T.val = 0 := by
        simp [centered, activeCost, ← show key = exactKernels from rfl, d, T.property, hg]
      simp [hzero, mean, hC]
  have hAdd : (fun T : Four K n => (activeCost i T : ℝ)) = fun T => centered T + 8*d T := by
    funext T
    dsimp [centered]
    ring
  rw [hAdd]
  simp only [mean, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
  change mean centered + 8 * mean d ≤ _
  have hd : mean d ≤ 4 := mean_trial_form_defect i
  dsimp [C] at hμ
  linarith only [hμ, hd]

/-- One actual enlarged singular trial passes the original `q^D ≤ n`
gate when it has admissible cut corank and bounded joint primary budget. -/
def singularOrderFourAccepted (T : Four K n) : Prop :=
  ∃ (ell rho : Forms K n), ell ≠ 0 ∧ rho ≠ 0 ∧
    ell ∈ (exactKernels T).2 ∧ rho ∈ (exactKernels T).1 ∧
    Fintype.card K ^ finrank K (exactKernels T).1 ≤ n ∧
    Fintype.card K ^ (repeatedBudget (rawEnlargedLeftPoly ell rho T) +
      repeatedBudget (rawEnlargedRightPoly ell rho T)) ≤ n

private theorem good_of_singular_nonexception (hn : 2 ≤ n) (T : Four K n)
    (hT : (flatten T).det = 0) (he : ¬ singularPreliminaryException T (n / 2)) :
    goodTrial (exactKernels T) := by
  obtain ⟨ell, hL⟩ := selectCutForm_of_singular false T hT
  obtain ⟨rho, hR⟩ := selectCutForm_of_singular true T hT
  have hL' : leftForm (exactKernels T) = ell := by
    simpa only [formFor, Bool.false_eq_true, if_false, hL, Option.getD_some] using formFor_eq false T
  have hR' : rightForm (exactKernels T) = rho := by
    simpa only [formFor, if_true, hR, Option.getD_some] using formFor_eq true T
  refine ⟨hL'.symm ▸ (chooseNonzero_spec hL).1, hR'.symm ▸ (chooseNonzero_spec hR).1,
    Nat.le_of_not_gt (fun h => he (Or.inl h)), ?_⟩
  rw [hL', hR']
  have hcL : ¬ n/2 ≤ formDefect ell := fun h => he (Or.inr (Or.inl ⟨ell, hL, h⟩))
  have hcR : ¬ n/2 ≤ formDefect rho := fun h => he (Or.inr (Or.inr ⟨rho, hR, h⟩))
  change ¬ n/2 ≤ n - formWidth ell at hcL
  change ¬ n/2 ≤ n - formWidth rho at hcR
  omega

private theorem event_or_le' {A : Type*} [Fintype A] (p q : A → Prop) :
    event (fun x => p x ∨ q x) ≤ event p + event q := by
  unfold event mean
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [hp,hq])) (by positivity)

set_option maxHeartbeats 1200000 in
/-- Singular coverage of the specified cut of a dense ordinary four-tensor.
The accepted trial uses the same enlarged polynomials as the comparison. -/
theorem orderFour_singular_coverage (hn : 1024 ≤ n) :
    event (fun T : Four K n => (flatten T).det = 0 ∧ ¬ singularOrderFourAccepted T) ≤
      2 / (n : ℝ) + 8 / (↑(n/2) : ℝ)^2 +
      2 * (8 * (budgetConstant K + 1) + 34) * Real.log (Fintype.card K) / Real.log n := by
  let e (T : Four K n) := singularPreliminaryException T (n/2)
  let g (T : Four K n) := n < Fintype.card K ^ (activeCost false T + activeCost true T)
  have hm : event (fun T : Four K n => (flatten T).det = 0 ∧ ¬ singularOrderFourAccepted T) ≤
      event (fun T => e T ∨ g T) := by
    apply mean_mono
    intro T
    by_cases ht : (flatten T).det = 0 ∧ ¬ singularOrderFourAccepted T
    · have h : e T ∨ g T := by
        by_cases he : e T
        · exact Or.inl he
        · right
          have hh := good_of_singular_nonexception (by omega) T ht.1 he
          refine lt_of_not_ge (fun hg => ht.2 ⟨leftForm (exactKernels T), rightForm (exactKernels T),
            hh.1, hh.2.1, trialForm_mem _, trialForm_mem _, hh.2.2.1, ?_⟩)
          simpa [activeCost, trialCost, hh] using hg
      simp [ht,h]
    · rw [if_neg ht]
      split <;> norm_num
  let C : ℝ := 8 * (budgetConstant K + 1) + 34
  have hq := Real.log_pos (by exact_mod_cast Fintype.one_lt_card (α := K) : 1 < (Fintype.card K : ℝ))
  have hn' := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : 1 < (n : ℝ))
  have hGate : event g ≤ 2 * C * Real.log (Fintype.card K) / Real.log n := by
    let t := Real.log (n : ℝ) / (2 * Real.log (Fintype.card K))
    have ht : 0 < t := div_pos hn' (by positivity)
    have h := event_sum_budget_le (fun i (T : Four K n) => (activeCost i T : ℝ))
      (fun _ _ => by positivity) C t ht (mean_active_cost_le hn)
    have hEq (T : Four K n) : g T ↔ (Fintype.card Bool : ℝ)*t < ∑ i, (activeCost i T : ℝ) := by
      have hr : g T ↔ (n : ℝ) < (Fintype.card K : ℝ) ^ (activeCost false T + activeCost true T) := by
        unfold g
        exact_mod_cast Iff.rfl
      rw [hr, ← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow,
        Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat, Nat.cast_add]
      rw [show (2 : ℝ) * t = Real.log n / Real.log (Fintype.card K) by
        dsimp [t]; field_simp]
      rw [div_lt_iff₀ hq]
      <;> simp only [add_comm]
    simp only [← hEq] at h
    exact h.trans_eq (by dsimp [t]; rw [div_div_eq_mul_div]; ring)
  exact (hm.trans (event_or_le' e g)).trans
    (add_le_add (singular_preliminary_exception_bound (by omega) (n/2) (by omega)) hGate)

#print axioms orderFour_singular_coverage

end
end Mathproof.EvenTI.OrderFour
