import EvenP17TrialBlockScan
import EvenP16TrialFormInit
import EvenP14CutRawSetup

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU dI dO)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure FormScanReady (σ : Env) (d n o : ℕ) : Prop where
  modes : σ.vars emitFormModes = d
  base : σ.vars reverseDigitBase = n
  start : σ.vars fieldVectorStart = o
  length : σ.vars fieldVectorLength = n^d

private def formRegs : List String := [emitFormModes,reverseDigitBase,fieldVectorStart,fieldVectorLength]

private theorem FormScanReady.frame {σ τ : Env} {d n o : ℕ} (h : FormScanReady σ d n o)
    (hf : ∀ r ∈ formRegs, τ.vars r=σ.vars r) : FormScanReady τ d n o :=
  ⟨(hf _ (by decide)).trans h.modes,(hf _ (by decide)).trans h.base,
    (hf _ (by decide)).trans h.start,(hf _ (by decide)).trans h.length⟩

noncomputable def encodeOneForm (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (cutCandidateProgram D F) (emitHigherForm D F)

noncomputable def encodeOneFormCost (F : FieldPresentation K) (c d m : ℕ) : ℕ :=
  cutCandidateCost F c m + emitHigherFormCost F d m

private def formVisitRegs : List String :=
  [cutCoeffStart,cutBasisStart,cutFormStart,shapePower.out,dL,dZ,dT,dU,
    coeffLength,loadBase,loadLength,cutChoiceIndex,cutChoiceLength] ++ formRegs

private abbrev CandidateFresh (r : String) : Prop :=
  r ∉ regNames canonical ∧ ¬loadChanges r ∧ r≠coeffIndex ∧ r≠coeffPower ∧ r≠coeffNumber ∧
  r≠dI ∧ r≠dO ∧ r≠cutEntry

private theorem candidateFormFresh : ∀ r ∈ formVisitRegs, CandidateFresh r := by decide
private theorem outputFormFresh : ∀ r ∈ formVisitRegs, r ∉ formClobbered := by decide
private theorem frameFormFresh : ∀ r ∈ regNames canonical, r ∉ formClobbered := by decide

/-- Reconstruct and serialize one indexed form while preserving the shared
basis, cap and native field layout for the next visit. -/
theorem encodeOneForm_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn a b o c d n z t u : ℕ} {σ : Env} (v : Fin (Fintype.card K^c))
    (hn : 0 < n) (hNB : n < B) (hD : d < B)
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c (n^d) z t u)
    (hForm : FormScanReady σ d n o) (hQ : Fintype.card K < B)
    (hPow : Fintype.card K^c < B) (hIdx : σ.vars cutChoiceIndex = v.val) :
    let x : Coord d n → K := fun j =>
      ∑ i : Fin c, coefficients D c v i *
        val F canonical qN.WS σ (b+(i.val*(n^d)+(inputCoordOrder n d j).val))
    ∃ τ, Run B (encodeOneForm D F) σ τ (encodeOneFormCost F c d (n^d)) ∧
      CutVisitInput (B := B) (Sn := Sn) F τ a b o c (n^d) z t u ∧
      FormScanReady τ d n o ∧ τ.vars cutChoiceIndex = v.val ∧
      τ.vars cutChoiceLength = σ.vars cutChoiceLength ∧
      (∀ s < z, b ≤ s → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out++cutFormWords D x := by
  dsimp only
  let m := n^d
  have h₀ := h.frame.layout.coefficient_before
  have h₁ := h.frame.layout.output_before
  have h₂ := h.frame.layout.basis_before
  have h₃ := h.frame.layout.zero_before
  have h₄ := h.frame.layout.scratch_order
  have h₅ := h.frame.layout.fit
  have hB := h.frame.slots.slots_word
  have hfit : o+m ≤ Sn := by omega
  have hMB : m < B := by omega
  have hLarge : 1 < B := by omega
  obtain ⟨α,hRebuild,hS,hRead,_,hBankLen,hMem,hVars,hIn,hOut⟩ :=
    cutCandidateProgram_run D F v h.frame hQ hPow h.coefficient_bank hIdx
      h.coefficient_count h.load_base h.load_count
  have keep (r : String) (hr : r ∈ formVisitRegs) : α.vars r=σ.vars r := by
    obtain ⟨hR,hL,hI,hP,hN,hDI,hDO,hE⟩ := candidateFormFresh r hr
    exact hVars r hR hL hI hP hN hDI hDO hE
  have hFormα : FormScanReady α d n o := hForm.frame
    (fun r hr => keep r (List.mem_append.mpr (Or.inr hr)))
  let x : Coord d n → K := fun j =>
    ∑ i : Fin c, coefficients D c v i *
      val F canonical qN.WS σ (b+(i.val*m+(inputCoordOrder n d j).val))
  have hX (j : Coord d n) : val F canonical qN.WS α (o+(inputCoordOrder n d j).val)=x j :=
    hRead (inputCoordOrder n d j)
  have hP : F.p < B := by
    have hp := Nat.le_mul_of_pos_right (F.p+1) (by omega : 0 < F.p+1)
    have hm := hS.base.arithmetic_word
    rw [pow_two] at hm
    omega
  obtain ⟨τ,hEmit,hEmitOut,hArr,hEmitIn,hEmitVars⟩ :=
    emitHigherForm_run D F x hn hNB hD hMB hS hQ.le hP hLarge hfit
      hFormα.start hFormα.length hFormα.base hFormα.modes hX
  have keep₁ (r : String) (hr : r ∈ formVisitRegs) : τ.vars r=σ.vars r :=
    (hEmitVars r (outputFormFresh r hr)).trans (keep r hr)
  have hWS : τ.vars qN.WS=α.vars qN.WS := hEmitVars _ (by decide)
  have hSτ := slots_frame F hS (congrFun hArr _) (congrFun hArr _)
    (fun r hr => hEmitVars r (frameFormFresh r hr)) hWS
  have emitVal (s : ℕ) : val F canonical qN.WS τ s=val F canonical qN.WS α s :=
    cutSlot_value_frame F (congrFun hArr _) hWS s
  have hKeep (s : ℕ) (hs : s ≤ z) (hb : b ≤ s) :
      val F canonical qN.WS τ s=val F canonical qN.WS σ s :=
    (emitVal s).trans (hMem s (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega))
  refine ⟨τ,hRebuild.seq hEmit,?_,hForm.frame (fun r hr => keep₁ r (List.mem_append.mpr (Or.inr hr))),
    (keep₁ _ (by decide)).trans hIdx,keep₁ _ (by decide),fun s hs hb => hKeep s hs.le hb,
    hEmitIn.trans hIn,hEmitOut.trans ?_⟩
  · refine ⟨⟨hSτ,h.frame.layout,h.frame.count_word,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · exact (keep₁ _ (by decide)).trans h.frame.coeff_start
    · exact (keep₁ _ (by decide)).trans h.frame.basis_start
    · exact (keep₁ _ (by decide)).trans h.frame.form_start
    · exact (keep₁ _ (by decide)).trans h.frame.side
    · exact (keep₁ _ (by decide)).trans h.frame.count
    · exact (keep₁ _ (by decide)).trans h.frame.zero
    · exact (keep₁ _ (by decide)).trans h.frame.scratch₁
    · exact (keep₁ _ (by decide)).trans h.frame.scratch₂
    · exact (hKeep z (le_refl _) (by omega)).trans h.frame.zero_value
    · rw [hArr,hBankLen]
      exact h.coefficient_bank
    · exact (keep₁ _ (by decide)).trans h.coefficient_count
    · exact (keep₁ _ (by decide)).trans h.load_base
    · exact (keep₁ _ (by decide)).trans h.load_count
  · rw [hOut]

#print axioms encodeOneForm_run
end EvenTI.P17Trial
