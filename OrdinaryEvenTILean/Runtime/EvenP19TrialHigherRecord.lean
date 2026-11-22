import EvenP19TrialModeVisit
import EvenP19TrialHigherFormsTail
import EvenP19TrialHigherHeader
import EvenP19TrialHigherOrder

set_option autoImplicit false
set_option maxHeartbeats 1450000
set_option maxRecDepth 24000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment EvenTI.P10Scan
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P17Trial EvenTI.P17Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15RecogIMPGrid20261007 (gRows)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def produceHigherTrial (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq higherHeader <|
    .seq (reciprocalTwoSweeps (higherModeVisit D F false) (higherModeVisit D F true)) <|
      .seq (emitInstalledHigherFormPair D F) restoreHigherTraceArgs

noncomputable def produceHigherTrialCost (F : FieldPresentation K) (l n : ℕ) : ℕ :=
  20+(((higherModeVisitCost F false l n+12)*(l+1)+8+
      ((higherModeVisitCost F true l n+12)*(l+1)+8))+
      (2*emitInstalledHigherFormCost F (l+1) (n^(l+1))+6))

private theorem finalFormKeepsControls :
    ∀ r∈higherRegisterNames, r≠fieldVectorStart → r≠fieldVectorLength →
      r∉higherFormTargets ∧ r∉formClobbered := by decide

/-- Starting with the original dense tensor and a native installed form
pair, emit one exact higher singular trial. The output includes both
lengths, all anchors in reference order, and the two form vectors. The
same source banks and workspace controls are ready for the next pair. -/
theorem produceHigherTrial_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S l n : ℕ} {s : Env} (b : HigherBanks)
    (T : Tensor K ((l+1)+(l+1)) n) (ell rho : Coord (l+1) n → K)
    (hLayout : HigherLayout b (n^(l+1)) n S)
    (hFrame : HigherFrame F b B S (n^(l+1)) n s s)
    (hInput : HigherInputValues F b T ell rho s)
    (hn : 2≤n) (hWide : 2*n<B) (hNn : n*n+2<B) (hM : n^(l+1)+1<B)
    (hHeader : 1+((l+1)+(l+1))*(n*n+2)<B)
    (hL : l+1<B) (hPower : n^l<B)
    (hQ : Fintype.card K≤B) (hP : F.p<B)
    (hPowLive : s.vars crossA=n^l) (hLimit : s.vars reciprocalSweepLimit=l+1) :
    ∃ t, Run B (produceHigherTrial D F) s t (produceHigherTrialCost F l n) ∧
      HigherFrame F b B S (n^(l+1)) n s t ∧
      t.vars crossA=n^l ∧ t.vars reciprocalSweepLimit=l+1 ∧ t.inp=s.inp ∧
      t.out=s.out++preparedTrialWords D (PreparedTrial.higher (ell,rho) (rawHigherSingularAnchors ell rho T)) := by
  let C (ρ : Env) := HigherFrame F b B S (n^(l+1)) n s ρ ∧
    ρ.vars crossA=n^l ∧ ρ.vars reciprocalSweepLimit=l+1
  let σ := higherHeaderState s l n
  let H (i : Fin (l+1) × Bool) := blockW (numberedAnchorWords D (numeric (rawHigherSingularAnchors ell rho T i)))
  have hSlotB := hFrame.slots.slots_word
  have hTraceBound : b.trace < S := by
    have h₁ := hLayout.traceBeforeLeft
    have h₂ := hLayout.leftBeforeRight
    have h₃ := hLayout.rightBeforeTemp
    have h₄ := hLayout.tempBeforeProduct
    have h₅ := hLayout.productBeforeCross
    have h₆ := hLayout.crossBeforeSquare
    have h₇ := hLayout.squareBeforeHighT
    have h₈ := hLayout.highTFit
    omega
  have hFitL := hLayout.formLeftBeforeTrace
  have hFitR := hLayout.formRightBeforeTrace
  have ht := hLayout.ttBefore
  have hu := hLayout.uuBefore
  have hn' : 0<n := by omega
  have hnB : n<B := by omega
  have hWidth : s.vars crossN=n := hFrame.registers (crossN,n) (by simp [higherRegisters])
  have r₀ := higherHeader_run hWidth hLimit hNn hHeader
  have hF₁ := hFrame.setVar reciprocalCountWord ((l+1)+(l+1)) (by decide) (by decide) (by decide)
  have hF₂ := hF₁.setVar gRows (n*n) (by decide) (by decide) (by decide)
  have hSlots₀ : Slots F canonical qN.WS S B σ :=
    slots_frame F hF₂.slots rfl rfl (fun _ _ => rfl) rfl
  have hC₀ : C σ :=
    ⟨⟨hSlots₀,hF₂.registers,hF₂.preserved⟩,hPowLive,hLimit⟩
  have doVisit (side : Bool) (ρ : Env) (i : Fin (l+1)) (hρ : C ρ)
      (hI : ρ.vars reciprocalSweepIndex=i.val) (hS : ρ.vars crossStride=n^(l-i.val))
      (_hN : ρ.vars crossN=n) :
      ∃ t, Run B (higherModeVisit D F side) ρ t (higherModeVisitCost F side l n) ∧ C t ∧
        t.vars reciprocalSweepIndex=i.val ∧ t.vars crossStride=n^(l-i.val) ∧
        t.vars crossN=ρ.vars crossN ∧ t.vars crossA=ρ.vars crossA ∧
        t.vars reciprocalSweepLimit=ρ.vars reciprocalSweepLimit ∧ t.inp=ρ.inp ∧ t.out=ρ.out++H (i,side) := by
    obtain ⟨t,r,hF,hKeep,hi,ho⟩ := higherModeVisit_run D F side b T ell rho i hLayout hρ.1
      hInput hn' hWide (by omega) hM hQ hP hS
    refine ⟨t,r,⟨hF,(hKeep _ (by decide)).trans hρ.2.1,(hKeep _ (by decide)).trans hρ.2.2⟩,
      (hKeep _ (by decide)).trans hI,(hKeep _ (by decide)).trans hS,
      hKeep _ (by decide),hKeep _ (by decide),hKeep _ (by decide),hi,ho⟩
  obtain ⟨γ,r₁,hγ,hIγ,hOγ⟩ := higherTwoSweeps_run
    (higherModeVisit D F) (fun side => higherModeVisitCost F side l n) C H
    hn hnB hPower hL
    (fun ρ i h => ⟨h.1.setVar _ i (by decide) (by decide) (by decide),h.2.1,h.2.2⟩)
    (fun ρ i h => ⟨h.1.setVar _ i (by decide) (by decide) (by decide),h.2.1,h.2.2⟩)
    doVisit hC₀ (hC₀.1.registers (crossN,n) (by simp [higherRegisters])) hC₀.2.1 hC₀.2.2
  have hReadL (x : Coord (l+1) n) :
      val F canonical qN.WS γ (b.formLeft+(inputCoordOrder n (l+1) x).val)=ell x := by
    have hx := (inputCoordOrder n (l+1) x).isLt
    exact (hγ.1.preserved _ (by omega) (by omega) (by omega)).trans (by
      simpa using hInput.left (inputCoordOrder n (l+1) x))
  have hReadR (x : Coord (l+1) n) :
      val F canonical qN.WS γ (b.formRight+(inputCoordOrder n (l+1) x).val)=rho x := by
    have hx := (inputCoordOrder n (l+1) x).isLt
    exact (hγ.1.preserved _ (by omega) (by omega) (by omega)).trans (by
      simpa using hInput.right (inputCoordOrder n (l+1) x))
  have rg {r : String} {v : ℕ} (h : (r,v)∈higherRegisters b (n^(l+1)) n) : γ.vars r=v :=
    hγ.1.registers _ h
  obtain ⟨η,r₂,hη,hMem,hVars,hIe,hOe⟩ := emitInstalledHigherFormPair_run D F (ls := b.formLeft) (rs := b.formRight) ell rho
    hγ.1.slots hn' hnB hL (by omega) (by omega) (by omega) (by omega) hQ hP
    (rg (by simp [higherRegisters])) hγ.2.2 (rg (by simp [higherRegisters]))
    (rg (by simp [higherRegisters])) (rg (by simp [higherRegisters])) hReadL hReadR
  let τ := restoredTraceState η b.trace n
  have r₃ : Run B restoreHigherTraceArgs η τ 6 := restoreHigherTraceArgs_run (o := b.trace) (n := n)
    ((hVars _ (by decide) (by decide)).trans (rg (by simp [higherRegisters])))
    ((hVars _ (by decide) (by decide)).trans (rg (by simp [higherRegisters])))
    (by omega) (by omega)
  have hT₁ := Slots.setVar F canonical hη (by decide : fieldVectorStart∉regNames canonical)
    (by decide : fieldVectorStart≠qN.WS) b.trace
  have hT₂ := Slots.setVar F canonical hT₁ (by decide : fieldVectorLength∉regNames canonical)
    (by decide : fieldVectorLength≠qN.WS) (n*n)
  have restored (r : String) (hr : r∈higherRegisterNames) : τ.vars r=γ.vars r := by
    by_cases hs : r=fieldVectorStart
    · subst r
      exact (show τ.vars fieldVectorStart=b.trace from rfl).trans (rg (by simp [higherRegisters])).symm
    by_cases hl : r=fieldVectorLength
    · subst r
      exact (show τ.vars fieldVectorLength=n*n from rfl).trans (rg (by simp [higherRegisters])).symm
    have hf := finalFormKeepsControls r hr hs hl
    simpa only [τ,restoredTraceState,vars_setVar,if_neg hs,if_neg hl] using hVars r hf.1 hf.2
  have hP₁ : τ.vars crossA=n^l := (hVars _ (by decide) (by decide)).trans hγ.2.1
  have hP₂ : τ.vars reciprocalSweepLimit=l+1 := (hVars _ (by decide) (by decide)).trans hγ.2.2
  have hBase (k : ℕ) : val F canonical qN.WS τ k=val F canonical qN.WS η k :=
    (val_setVar F canonical (by decide : fieldVectorLength≠qN.WS) _ _ k).trans
      (val_setVar F canonical (by decide : fieldVectorStart≠qN.WS) _ _ k)
  refine ⟨τ,r₀.seq (r₁.seq (r₂.seq r₃)),
    ⟨hT₂,fun p hp => (restored p.1 (higherRegister_name hp)).trans (hγ.1.registers p hp),
      fun k hk ht' hu' => (hBase k).trans ((hMem k).trans (hγ.1.preserved k hk ht' hu'))⟩,
    hP₁,hP₂,hIe.trans hIγ,?_⟩
  change η.out=_
  rw [hOe,hOγ,show σ.out=s.out++[2,1+((l+1)+(l+1))*(n*n+2),(l+1)+(l+1)] from rfl,
    higherTrialWords_exact]
  simp only [List.append_assoc,H]

#print axioms produceHigherTrial_run
end EvenTI.P19Trial
