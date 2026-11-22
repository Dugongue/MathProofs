import EvenP19TrialModeFrame
import EvenP19TrialHigherAnchorTail

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 27000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.P10Scan EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16TrialNative EvenTI.P16Execution EvenTI.P17Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (out_lt)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private noncomputable def testField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem scratchControls : ∀ r ∈ higherVisitControls, r≠dT ∧ r≠dU := by decide

private theorem projectionControls (F : FieldPresentation K) :
    ∀ r ∈ higherVisitControls, r ∉ scalarWrites (nativeProjectionPair F) := by
  change ∀ r ∈ higherVisitControls, r ∉ scalarWrites (nativeProjectionPair testField)
  decide

private theorem tailControls (F : FieldPresentation K) :
    ∀ r ∈ higherVisitControls, r ∉ scalarWrites (higherContraction F) ∧ SideTraceStable F r := by
  change ∀ r ∈ higherVisitControls, r ∉ scalarWrites (higherContraction testField) ∧ SideTraceStable testField r
  unfold SideTraceStable
  decide

noncomputable def higherModeVisit (D : FieldEncoding K) (F : FieldPresentation K) (side : Bool) : Com :=
  .seq highScratch (.seq (nativeProjectionPair F) (.seq lowScratch (higherAnchorTail D F side)))

noncomputable def higherModeVisitCost (F : FieldPresentation K) (side : Bool) (l n : ℕ) : ℕ :=
  4+(2*(17+nativeProjectionGridCost F n (n^l) 1)+(4+higherAnchorTailCost F side (n^(l+1)) n))

structure HigherInputValues (F : FieldPresentation K) (b : HigherBanks) {l n : ℕ}
    (T : Tensor K ((l+1)+(l+1)) n) (ell rho : Coord (l+1) n → K) (s : Env) : Prop where
  tensor : ∀ x y : Fin (n^(l+1)), val F canonical qN.WS s (b.tensor+(x.val*n^(l+1)+y.val)) =
    flatten T ((inputCoordOrder n (l+1)).symm x) ((inputCoordOrder n (l+1)).symm y)
  left : ∀ x : Fin (n^(l+1)), val F canonical qN.WS s (b.formLeft+x.val)=ell ((inputCoordOrder n (l+1)).symm x)
  right : ∀ x : Fin (n^(l+1)), val F canonical qN.WS s (b.formRight+x.val)=rho ((inputCoordOrder n (l+1)).symm x)
  zero : val F canonical qN.WS s b.zero=0
  one : val F canonical qN.WS s b.one=1

/-- Install the physical projection coefficients for this mode, restore the
low scratch addresses, contract the original tensor and emit the chosen
partial trace. Source banks and mode-sweep control words survive. -/
theorem higherModeVisit_run (D : FieldEncoding K) (F : FieldPresentation K) (side : Bool)
    {B S l n : ℕ} {base s : Env} (b : HigherBanks)
    (T : Tensor K ((l+1)+(l+1)) n) (ell rho : Coord (l+1) n → K) (i : Fin (l+1))
    (hLayout : HigherLayout b (n^(l+1)) n S)
    (hFrame : HigherFrame F b B S (n^(l+1)) n base s)
    (hRead : HigherInputValues F b T ell rho base) (hn : 0 < n) (hWide : 2*n < B)
    (hNn : n*n+1 < B) (hM : n^(l+1)+1 < B) (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hStride : s.vars crossStride=n^(l-i.val)) :
    ∃ t, Run B (higherModeVisit D F side) s t (higherModeVisitCost F side l n) ∧
      HigherFrame F b B S (n^(l+1)) n base t ∧
      (∀ r ∈ higherVisitControls, t.vars r=s.vars r) ∧ t.inp=s.inp ∧
      t.out=s.out++blockW (numberedAnchorWords D (numeric (rawHigherSingularAnchors ell rho T (i,side)))) := by
  have hSlotB := hFrame.slots.slots_word
  have h₀ := hLayout.tensorBeforeTrace
  have h₁ := hLayout.formLeftBeforeTrace
  have h₂ := hLayout.formRightBeforeTrace
  have h₃ := hLayout.traceBeforeLeft
  have h₄ := hLayout.leftBeforeRight
  have h₅ := hLayout.rightBeforeTemp
  have h₆ := hLayout.tempBeforeProduct
  have h₇ := hLayout.productBeforeCross
  have h₈ := hLayout.crossBeforeSquare
  have h₉ := hLayout.squareBeforeHighT
  have h₁₀ := hLayout.squareBeforeHighU
  have h₁₁ := hLayout.highTFit
  have h₁₂ := hLayout.highUFit
  have hLowT := hLayout.ttBefore
  have hLowU := hLayout.uuBefore
  have hOneLow := hLayout.oneBefore
  have hOneNext := hLayout.oneNext
  have hZeroLT : b.zero < b.trace := by omega
  have reg {r : String} {v : ℕ} (h : (r,v) ∈ higherRegisters b (n^(l+1)) n) : s.vars r=v :=
    hFrame.registers _ h
  have own {r : String} {v : ℕ} (h : (r,v) ∈ higherRegisters b (n^(l+1)) n) : r ∈ higherVisitControls :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (higherRegister_name h))))
  obtain ⟨α,payHigh,hA,hAT,hAU,hAR,hAM,hAI,hAO⟩ := highScratch_run F (t := b.highT) (u := b.highU) hFrame.slots
    (reg (by simp [higherRegisters])) (reg (by simp [higherRegisters])) (by omega) (by omega)
  have keepA (r : String) (hr : r ∈ higherVisitControls) : α.vars r=s.vars r :=
    hAR r (scratchControls r hr).1 (scratchControls r hr).2
  have getA {r : String} {v : ℕ} (hr : (r,v) ∈ higherRegisters b (n^(l+1)) n) : α.vars r=v :=
    (keepA r (own hr)).trans (reg hr)
  have readA (k : ℕ) (hk : k < b.trace) (ht : k≠b.tt) (hu : k≠b.uu) :
      val F canonical qN.WS α k=val F canonical qN.WS base k :=
    (hAM k).trans (hFrame.preserved k hk ht hu)
  have zeroA : val F canonical qN.WS α b.zero=0 :=
    (readA _ hZeroLT hLayout.zeroApart.1 hLayout.zeroApart.2).trans hRead.zero
  have oneA : val F canonical qN.WS α (b.zero+1)=1 := by
    rw [←hOneNext]
    exact (readA _ hOneLow hLayout.oneApart.1 hLayout.oneApart.2).trans hRead.one
  have leftA (x : Fin (n^(l+1))) :
      val F canonical qN.WS α (b.formLeft+x.val)=ell ((inputCoordOrder n (l+1)).symm x) := by
    have hx := x.isLt
    exact (readA _ (by omega) (by omega) (by omega)).trans (hRead.left x)
  have rightA (x : Fin (n^(l+1))) :
      val F canonical qN.WS α (b.formRight+x.val)=rho ((inputCoordOrder n (l+1)).symm x) := by
    have hx := x.isLt
    exact (readA _ (by omega) (by omega) (by omega)).trans (hRead.right x)
  obtain ⟨β,payProjection,hB,hProjL,hProjR,hPM,hPI,hPO⟩ :=
    nativeProjectionPair_run F (a := b.left) (b := b.right) (ls := b.formLeft) (rs := b.formRight)
      i ell rho hn hWide hNn hM (by omega) (by omega) h₄
      (by omega) (by omega) h₁₁ h₁₂ hLayout.highDistinct (by omega)
      hA zeroA oneA hAT hAU (getA (by simp [higherRegisters]))
      (getA (by simp [higherRegisters])) ((keepA _ (by decide)).trans hStride)
      (getA (by simp [higherRegisters])) (getA (by simp [higherRegisters]))
      (getA (by simp [higherRegisters])) (getA (by simp [higherRegisters]))
      (getA (by simp [higherRegisters])) leftA rightA
  rw [nativeProjectionGridCost_fixed F i] at payProjection
  have keepB (r : String) (hr : r ∈ higherVisitControls) : β.vars r=s.vars r :=
    ((Frame.of_run payProjection).vars r (projectionControls F r hr)).trans (keepA r hr)
  have getB {r : String} {v : ℕ} (hr : (r,v) ∈ higherRegisters b (n^(l+1)) n) : β.vars r=v :=
    (keepB r (own hr)).trans (reg hr)
  obtain ⟨γ,payLow,hC,hCT,hCU,hCR,hCM,hCI,hCO⟩ := lowScratch_run F (t := b.tt) (u := b.uu) hB
    (getB (by simp [higherRegisters])) (getB (by simp [higherRegisters])) (by omega) (by omega)
  have keepC (r : String) (hr : r ∈ higherVisitControls) : γ.vars r=s.vars r :=
    (hCR r (scratchControls r hr).1 (scratchControls r hr).2).trans (keepB r hr)
  have getC {r : String} {v : ℕ} (hr : (r,v) ∈ higherRegisters b (n^(l+1)) n) : γ.vars r=v :=
    (keepC r (own hr)).trans (reg hr)
  have lowC (k : ℕ) (hk : k < b.trace) (ht : k≠b.tt) (hu : k≠b.uu) :
      val F canonical qN.WS γ k=val F canonical qN.WS base k :=
    (hCM k).trans ((hPM k (by omega)).trans (readA k hk ht hu))
  have hCon : ContractionRegisters γ (n^(l+1)) n b.toContractionOffsets := by
    constructor <;> first | exact hCT | exact hCU | exact getC (by simp [higherRegisters])
  have hTrace : TraceRegisterBank γ n b.square b.trace b.one := by
    constructor <;> exact getC (by simp [higherRegisters])
  have tensorC (x y : Fin (n^(l+1))) :
      val F canonical qN.WS γ (b.tensor+(x.val*n^(l+1)+y.val)) =
        flatten T ((inputCoordOrder n (l+1)).symm x) ((inputCoordOrder n (l+1)).symm y) := by
    have hx := out_lt (o0:=b.tensor) x.isLt y.isLt
    exact (lowC _ (by omega) (by omega) (by omega)).trans (hRead.tensor x y)
  obtain ⟨τ,payTail,hT,hTM,hTR,hTI,hTO⟩ := higherAnchorTail_run D F side b.toContractionOffsets b.square b.trace
    T ell rho i hC hn (by omega) hM hNn hCon hTrace hQ hP
    (by omega) (by omega) h₅ h₆ h₇ h₈ (by omega) (by omega) (by omega)
    ⟨hLowT.1,by omega,by omega,by omega⟩ ⟨hLowU.1,by omega,by omega,by omega⟩ hLayout.lowDistinct
    ⟨hZeroLT,hLayout.zeroApart⟩ ⟨hOneLow,hLayout.oneApart⟩
    ((lowC _ hZeroLT hLayout.zeroApart.1 hLayout.zeroApart.2).trans hRead.zero)
    ((lowC _ hOneLow hLayout.oneApart.1 hLayout.oneApart.2).trans hRead.one)
    tensorC (fun u x => (hCM _).trans (hProjL u x)) (fun u x => (hCM _).trans (hProjR u x))
  have keepT (r : String) (hr : r ∈ higherVisitControls) : τ.vars r=s.vars r :=
    (hTR r (tailControls F r hr).1 (tailControls F r hr).2).trans (keepC r hr)
  refine ⟨τ,payHigh.seq (payProjection.seq (payLow.seq payTail)),?_,keepT,
    hTI.trans (hCI.trans (hPI.trans hAI)),?_⟩
  · exact ⟨hT,fun p hp => (keepT p.1 (own hp)).trans (reg hp),
      fun k hk ht hu => (hTM k hk ht hu).trans (lowC k hk ht hu)⟩
  · rw [hTO,hCO,hPO,hAO]

#print axioms higherModeVisit_run
end EvenTI.P19Trial
