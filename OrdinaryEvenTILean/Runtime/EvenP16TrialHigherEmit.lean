import EvenP16TrialReverseDigits
import EvenP15TrialFieldVector

set_option autoImplicit false
set_option maxHeartbeats 2100000

namespace EvenTI.P16Trial

open EvenTI.Contract EvenTI.Action EvenTI.P15Trial EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames val_setVar)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def emitFormModes : String := "even.trial.emit.form-modes"

private def formAddress : Expr := .add (.var qN.WS)
  (.mul (.add (.var fieldVectorStart) (.var reverseDigitResult)) (.var canonical.e))

private noncomputable def emitFormStep (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.assign reverseDigitRemain (.var emitFormModes)) <|
    .seq (.assign reverseDigitQuotient (.var fieldVectorIndex)) <|
      .seq reverseDigits <|
        .seq (.assign labelAddress formAddress) <|
          .seq (emitFieldLabel D F)
            (.assign fieldVectorIndex (.add (.var fieldVectorIndex) (.lit 1)))

noncomputable def emitHigherForm (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.assign fieldVectorIndex (.lit 0)) (.while fieldVectorGuard (emitFormStep D F))

noncomputable def emitHigherFormCost (F : FieldPresentation K) (d m : ℕ) : ℕ :=
  (24*d+26+emitFieldLabelCost F)*m+6

def formClobbered : List String :=
  [fieldVectorIndex,reverseDigitRemain,reverseDigitQuotient,reverseDigitResult,labelAddress]

private structure EmitFormInvariant (F : FieldPresentation K) (σ τ : Env)
    (Sn B n d : ℕ) (digits : ℕ → ℕ) : Prop where
  slots : Slots F canonical qN.WS Sn B τ
  index_bound : τ.vars fieldVectorIndex ≤ n^d
  arrays : τ.arrs=σ.arrs
  input : τ.inp=σ.inp
  output : τ.out=σ.out++(List.range (τ.vars fieldVectorIndex)).map digits
  frame : ∀ x, x ∉ formClobbered → τ.vars x=σ.vars x

private theorem coreReverseSafe : ∀ r∈regNames canonical,
    r ≠ reverseDigitRemain ∧ r ≠ reverseDigitQuotient ∧ r ≠ reverseDigitResult := by decide

/-- Serialize an installed kernel form of any cut order in the exact
public encoding, computing each address with the paid digit reversal. -/
theorem emitHigherForm_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn n d src : ℕ} {σ : Env} (form : Coord d n → K)
    (hn : 0 < n) (hNB : n < B) (hD : d < B) (hM : n^d < B)
    (hSlots : Slots F canonical qN.WS Sn B σ)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hLarge : 1 < B)
    (hFit : src+n^d ≤ Sn)
    (hSrc : σ.vars fieldVectorStart=src) (hLen : σ.vars fieldVectorLength=n^d)
    (hBase : σ.vars reverseDigitBase=n) (hMode : σ.vars emitFormModes=d)
    (hRead : ∀ x : Coord d n,
      val F canonical qN.WS σ (src+(inputCoordOrder n d x).val)=form x) :
    ∃ τ, Run B (emitHigherForm D F) σ τ (emitHigherFormCost F d (n^d)) ∧
      τ.out=σ.out++cutFormWords D form ∧ τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧
      ∀ x, x ∉ formClobbered → τ.vars x=σ.vars x := by
  let m := n^d
  let digits := fun i : ℕ => (D (val F canonical qN.WS σ (src+reverseModeNumber n d i))).val
  let I := fun τ => EmitFormInvariant F σ τ Sn B n d digits
  let V := fun τ : Env => m-τ.vars fieldVectorIndex
  have hSn := hSlots.slots_word
  let σ₀ := σ.setVar fieldVectorIndex 0
  have r₀ : Run B (.assign fieldVectorIndex (.lit 0)) σ σ₀ 2 := Run.assign (evalB_lit (by omega))
  have h₀ : I σ₀ := by
    refine ⟨Slots.setVar F canonical hSlots (by decide) (by decide) _,by simp [σ₀],
      rfl,rfl,by simp [σ₀],?_⟩
    intro x hx
    have hh : x≠fieldVectorIndex := fun h => hx (by simp [h,formClobbered])
    simp [σ₀,hh]
  have hGuard (τ : Env) (h : I τ) :
      fieldVectorGuard.evalB B τ=some (decide (τ.vars fieldVectorIndex < m)) := by
    have hLen' := (h.frame _ (by decide)).trans hLen
    exact evalB_condLt (evalB_var (h.index_bound.trans_lt hM)) (ev_var hLen' hM)
  have hStep (τ : Env) (h : I τ) (hg : fieldVectorGuard.evalB B τ=some true) :
      ∃ v, Run B (emitFormStep D F) τ v (24*d+22+emitFieldLabelCost F) ∧ I v ∧ V v < V τ := by
    rw [hGuard τ h] at hg
    let i := τ.vars fieldVectorIndex
    have hi : i < m := of_decide_eq_true (Option.some.inj hg)
    have hRevSlot : reverseModeNumber n d i < m := by
      rw [←reverseModeNumber_eq hn d (⟨i,hi⟩ : Fin m)]
      exact (inputCoordOrder n d ((cutOrder d n).symm ⟨i,hi⟩)).isLt
    let ρ := τ.setVar reverseDigitRemain d
    let η := ρ.setVar reverseDigitQuotient i
    have r₁ : Run B (.assign reverseDigitRemain (.var emitFormModes)) τ ρ 2 :=
      Run.assign (ev_var ((h.frame _ (by decide)).trans hMode) hD)
    have r₂ : Run B (.assign reverseDigitQuotient (.var fieldVectorIndex)) ρ η 2 :=
      Run.assign (ev_var (show ρ.vars fieldVectorIndex=i from rfl) (hi.trans hM))
    obtain ⟨α,r₃,hRev,hArr,hIn,hOut,hKeep⟩ := reverseDigits_run hn hNB hD hM hi
      (show η.vars reverseDigitBase=n from (h.frame _ (by decide)).trans hBase) rfl rfl
    have hα (x : String) (hx₁ : x ≠ reverseDigitRemain) (hx₂ : x ≠ reverseDigitQuotient)
        (hx₃ : x ≠ reverseDigitResult) : α.vars x=τ.vars x := by
      rw [hKeep x hx₁ hx₂ hx₃]
      simp [η,ρ,hx₁,hx₂]
    have hSA : Slots F canonical qN.WS Sn B α := slots_frame F h.slots
      (congrFun hArr _) (congrFun hArr _)
      (fun x hx => hα x (coreReverseSafe x hx).1 (coreReverseSafe x hx).2.1 (coreReverseSafe x hx).2.2)
      (hα _ (by decide) (by decide) (by decide))
    have hSrc' : α.vars fieldVectorStart=src :=
      (hα _ (by decide) (by decide) (by decide)).trans ((h.frame _ (by decide)).trans hSrc)
    let p := src+reverseModeNumber n d i
    have hp : p < Sn := by omega
    let dst := α.vars qN.WS+p*F.e
    have hMem := hSA.base.memory_word
    have hFitMem := hSA.fit
    have hAddr : dst < B := by
      have hd := Nat.mul_le_mul_right F.e (show p ≤ Sn from hp.le)
      dsimp [dst]
      omega
    have he : F.e < B := by
      have hE := Nat.le_mul_of_pos_left F.e (show 0 < Sn by omega)
      omega
    have ep : (Expr.add (.var fieldVectorStart) (.var reverseDigitResult)).evalB B α=some p :=
      ev_add (ev_var hSrc' (by omega)) (ev_var hRev (hRevSlot.trans hM)) (hp.trans hSn)
    have eAddr : formAddress.evalB B α=some dst :=
      ev_add (ev_var rfl (by dsimp [dst] at hAddr; omega))
        (ev_mul ep (ev_var hSA.base.degree he) (by dsimp [dst] at hAddr; omega)) hAddr
    let β := α.setVar labelAddress dst
    have r₄ : Run B (.assign labelAddress formAddress) α β 8 := Run.assign eAddr
    have hSB : Slots F canonical qN.WS Sn B β :=
      Slots.setVar F canonical hSA (by decide) (by decide) _
    have hVal : val F canonical qN.WS β p=val F canonical qN.WS σ p := by
      change val F canonical qN.WS (α.setVar labelAddress dst) p=_
      rw [val_setVar F canonical (by decide)]
      unfold val slice
      rw [hArr,show η.arrs=τ.arrs from rfl,h.arrays,hα _ (by decide) (by decide) (by decide),
        h.frame _ (by decide)]
    let γ := {β with out := β.out++[digits i]}
    have r₅ : Run B (emitFieldLabel D F) β γ (emitFieldLabelCost F) := by
      have he' : β.vars labelAddress=β.vars qN.WS+p*F.e := rfl
      simpa only [hVal,γ,digits,p] using emitFieldLabel_run D F hSB hp hQ hP he'
    have hIdx : γ.vars fieldVectorIndex=i := hα _ (by decide) (by decide) (by decide)
    let δ := γ.setVar fieldVectorIndex (i+1)
    have eInc : (Expr.add (.var fieldVectorIndex) (.lit 1)).evalB B γ=some (i+1) :=
      ev_add (ev_var hIdx (hi.trans hM)) (evalB_lit hLarge) (by omega)
    have r₆ : Run B (.assign fieldVectorIndex (.add (.var fieldVectorIndex) (.lit 1))) γ δ 4 :=
      Run.assign eInc
    have hSC : Slots F canonical qN.WS Sn B γ := slots_frame F hSB rfl rfl (fun _ _ => rfl) rfl
    refine ⟨δ,(r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))).mono ?_,?_,?_⟩
    · omega
    · refine ⟨Slots.setVar F canonical hSC (by decide) (by decide) _,?_,hArr.trans h.arrays,
        hIn.trans h.input,?_,?_⟩
      · change i+1 ≤ m
        omega
      · change α.out++[digits i]=σ.out++(List.range (i+1)).map digits
        rw [hOut,show η.out=τ.out from rfl,h.output,show τ.vars fieldVectorIndex=i from rfl,
          List.range_succ,List.map_append]
        simp [List.append_assoc]
      · intro x hx
        have hf : x≠fieldVectorIndex := fun hh => hx (by simp [hh,formClobbered])
        have hg : x≠labelAddress := fun hh => hx (by simp [hh,formClobbered])
        have hr : x≠reverseDigitRemain := fun hh => hx (by simp [hh,formClobbered])
        have hq : x≠reverseDigitQuotient := fun hh => hx (by simp [hh,formClobbered])
        have ho : x≠reverseDigitResult := fun hh => hx (by simp [hh,formClobbered])
        simpa [δ,γ,β,hf,hg] using (hα x hr hq ho).trans (h.frame x hx)
    · change m-(i+1) < m-i
      omega
  obtain ⟨τ,rτ,hτ,hStop⟩ := Run.while_count I V (24*d+22+emitFieldLabelCost F)
    (fun τ h => ⟨_,hGuard τ h⟩) hStep h₀
  rw [hGuard τ hτ] at hStop
  have hStop' := of_decide_eq_false (Option.some.inj hStop)
  have hEnd : τ.vars fieldVectorIndex=m := by have := hτ.index_bound; omega
  have h0 : V σ₀=m := by simp [V,σ₀]
  have hW : (List.range m).map digits=cutFormWords D form := by
    rw [cutFormWords_as_gather hn D form (fun j => val F canonical qN.WS σ (src+j)) hRead]
    apply List.ext_getElem
    · simp [m]
    · intro j h₁ h₂
      simp [digits]
  refine ⟨τ,?_,?_,hτ.arrays,hτ.input,hτ.frame⟩
  · rw [h0] at rτ
    exact (r₀.seq rτ).mono (by
      unfold emitHigherFormCost
      change 2+((1+3+(24*d+22+emitFieldLabelCost F))*m+1+3) ≤
        (24*d+26+emitFieldLabelCost F)*m+6
      have hh : 1+3+(24*d+22+emitFieldLabelCost F)=24*d+26+emitFieldLabelCost F := by omega
      rw [hh]
      omega)
  · rw [hτ.output,hEnd,hW]

#print axioms emitHigherForm_run
end EvenTI.P16Trial