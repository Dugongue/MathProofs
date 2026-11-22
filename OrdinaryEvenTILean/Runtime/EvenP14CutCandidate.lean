import EvenP14CutCoeffInstall
import EvenP14CutRecombine
import EvenP14CutChoiceCap
import EvenNextBankPairs

set_option autoImplicit false
set_option maxHeartbeats 1250000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dL dO dT dU dZ dI)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def cutCandidateProgram (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (loadCutCoefficients D F) (cutRecombineProgram F)

noncomputable def cutCandidateCost (F : FieldPresentation K) (c m : ℕ) : ℕ :=
  loadCutCoefficientsCost F c + cutRecombineCost F c m

/-- A cap-admitted numeric code is translated to the exact linear combination
used by `bankForms`. The allocated result bank is the only new field payload. -/
theorem cutCandidateProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn a b o c m z t u : ℕ} {σ : Env} (v : Fin (Fintype.card K^c))
    (h : CutRecombineInput (B := B) (Sn := Sn) F σ a b o c m z t u)
    (hField : Fintype.card K < B)
    (hPow : Fintype.card K^c < B)
    (hcBank : c ≤ (σ.arrs coefficientBank).length)
    (hLive : σ.vars cutChoiceIndex = v.val)
    (hLen : σ.vars coeffLength = c)
    (hLoadBase : σ.vars loadBase = a) (hLoadLen : σ.vars loadLength = c) :
    ∃ τ, Run B (cutCandidateProgram D F) σ τ (cutCandidateCost F c m) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ j : Fin m, val F canonical qN.WS τ (o+j.val) =
        ∑ i : Fin c, coefficients D c v i * val F canonical qN.WS σ (b+(i.val*m+j.val))) ∧
      (∀ i < c, (τ.arrs coefficientBank).getD i 0 = coefficientLabel (Fintype.card K) v.val i) ∧
      (τ.arrs coefficientBank).length = (σ.arrs coefficientBank).length ∧
      (∀ s < Sn, (s < a ∨ a+c ≤ s) → (s < o ∨ o+m ≤ s) → s ≠ t → s ≠ u →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, r ∉ regNames canonical → ¬loadChanges r → r ≠ coeffIndex → r ≠ coeffPower →
        r ≠ coeffNumber → r ≠ dI → r ≠ dO → r ≠ cutEntry → τ.vars r = σ.vars r) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  have hAB := h.layout.coefficient_before
  have hBO := h.layout.output_before
  have hBZ := h.layout.basis_before
  have hZT := h.layout.zero_before
  have hTU := h.layout.scratch_order
  have hSn := h.layout.fit
  have hCB := h.count_word
  obtain ⟨μ,hLoad,hS,hCoeffs,hDigits,hBankLen,hKeep,hRegs,hIn,hOut⟩ :=
    loadCutCoefficients_run D F v h.slots hField (by omega) hPow (by omega) hcBank (by omega)
      hLive hLen hLoadBase hLoadLen
  have hm : CutRecombineInput (B := B) (Sn := Sn) F μ a b o c m z t u :=
    ⟨hS,h.layout,hCB,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.coeff_start,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.basis_start,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.form_start,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.side,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.count,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.zero,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.scratch₁,
      (hRegs _ (by decide) (by decide) (by decide) (by decide)).trans h.scratch₂,
      (hKeep _ (Or.inr (by omega))).trans h.zero_value⟩
  obtain ⟨τ,hRun,hSlots,hResults,hMem,hVars,hArr,hin,hout⟩ := cutRecombineProgram_run F hm
  have hb := hArr coefficientBank (by decide) (by decide)
  refine ⟨τ,hLoad.seq hRun,hSlots,?_,?_,(congrArg List.length hb).trans hBankLen,?_,?_,hin.trans hIn,hout.trans hOut⟩
  · intro j
    rw [hResults j.val j.isLt]
    unfold cutFormEntry
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hCoeffs i,hKeep _ (Or.inr (by omega))]
  · intro i hi
    rw [hb]
    exact hDigits i hi
  · intro s hs hsC hsO ht hu
    exact (hMem s hs hsO ht hu).trans (hKeep s hsC)
  · intro r hR hL hI hP hN hDI hDO hE
    exact (hVars r hR hDI hDO hE).trans (hRegs r hL hI hP hN)

/-- The capped scan covers exactly the coefficient codes used by
`linearChoices`, including the empty branch when the cap is exceeded. -/
theorem cappedCutChoiceCount_eq (D : FieldEncoding K) (c budget : ℕ) :
    cappedCutChoiceCount (Fintype.card K) c budget = (coefficientChoices D c budget).length := by
  rw [coefficientChoices_length]
  rfl

#print axioms cutCandidateProgram_run
#print axioms cappedCutChoiceCount_eq
end EvenTI.P12ComparePrep
