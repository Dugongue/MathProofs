import EvenP12ComparePrepCoeffDigits
import EvenP12CompareBankLoad
import Mathproof.Meta.P15GEInit20261007

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.Contract EvenTI.P12Compare
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarNames)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18IMPFieldAddition20261001 (writeValues writeValues_length)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutChoiceIndex : String := "even_compare_choice_index"

noncomputable def loadCutCoefficients (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (coefficientDigitProgram (Fintype.card K) cutChoiceIndex)
    (encodedBankLoad D F coefficientBank (.var loadIndex))

def loadCutCoefficientsCost (F : FieldPresentation K) (c : ℕ) : ℕ :=
  (34*c+8) + encodedBankLoadCost F (.var loadIndex) c

theorem cutSlot_value_frame (F : FieldPresentation K) {σ τ : Env}
    (hMem : τ.arrs canonical.mem = σ.arrs canonical.mem)
    (hWS : τ.vars qN.WS = σ.vars qN.WS) (s : ℕ) :
    val F canonical qN.WS τ s = val F canonical qN.WS σ s := by
  unfold val
  rw [hWS]
  apply congrArg (Mathproof.Problem18IMPFieldPresentation20261001.decode F)
  funext i
  change (τ.arrs canonical.mem).getD (σ.vars qN.WS+s*F.e+i.val) 0 =
    (σ.arrs canonical.mem).getD (σ.vars qN.WS+s*F.e+i.val) 0
  rw [hMem]

private theorem coeffState_register (q v c : ℕ) (σ : Env) (r : String)
    (hi : r ≠ coeffIndex) (hp : r ≠ coeffPower) (hn : r ≠ coeffNumber) :
    (coefficientDigitState σ q v c).vars r = σ.vars r := by
  unfold coefficientDigitState
  split <;> simp [vars_setVar,hi,hp,hn]

private theorem coeffState_array (q v c : ℕ) (σ : Env) (a : String)
    (ha : a ≠ coefficientBank) : (coefficientDigitState σ q v c).arrs a = σ.arrs a := by
  simp [coefficientDigitState,ha]

private theorem coeffState_fresh (r : String) (hr : r ∈ regNames canonical) :
    r ≠ coeffIndex ∧ r ≠ coeffPower ∧ r ≠ coeffNumber := by
  have hno : ∀ x ∈ [coeffIndex,coeffPower,coeffNumber], x ∉ regNames canonical := by decide
  exact ⟨fun h => hno _ (by simp) (h ▸ hr),fun h => hno _ (by simp) (h ▸ hr),
    fun h => hno _ (by simp) (h ▸ hr)⟩

/-- The word decoder reads the live candidate code, installs its exact
coefficient vector in canonical field slots, and frames the basis banks. -/
theorem loadCutCoefficients_run (D : FieldEncoding K) (F : FieldPresentation K)
    {c base Sn B : ℕ} {σ : Env} (v : Fin (Fintype.card K^c))
    (hS : Slots F canonical qN.WS Sn B σ) (hQ : Fintype.card K < B)
    (hB : 1 < B) (hPow : Fintype.card K^c < B)
    (hc : c < B) (hArr : c ≤ (σ.arrs coefficientBank).length)
    (hFit : base+c ≤ Sn) (hCode : σ.vars cutChoiceIndex = v.val)
    (hC : σ.vars coeffLength = c) (hBase : σ.vars loadBase = base)
    (hLen : σ.vars loadLength = c) :
    ∃ τ, Run B (loadCutCoefficients D F) σ τ (loadCutCoefficientsCost F c) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ j : Fin c, val F canonical qN.WS τ (base+j.val) = coefficients D c v j) ∧
      (∀ i < c, (τ.arrs coefficientBank).getD i 0 = coefficientLabel (Fintype.card K) v.val i) ∧
      (τ.arrs coefficientBank).length = (σ.arrs coefficientBank).length ∧
      (∀ s, s < base ∨ base+c ≤ s → val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, ¬loadChanges r → r ≠ coeffIndex → r ≠ coeffPower → r ≠ coeffNumber → τ.vars r = σ.vars r) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let q := Fintype.card K
  let ρ := coefficientDigitState σ q v.val c
  have hq : 0 < q := Fintype.card_pos
  obtain ⟨hRun,hDigits,hIn,hOut⟩ := coefficientDigitProgram_run q v.val c B cutChoiceIndex σ
    hq hQ hB (v.isLt.trans hPow) hc hPow hArr hC hCode (by decide)
  have hsR (r : String) (hi : r ≠ coeffIndex) (hp : r ≠ coeffPower) (hn : r ≠ coeffNumber) :
      ρ.vars r = σ.vars r := coeffState_register q v.val c σ r hi hp hn
  have haR (a : String) (ha : a ≠ coefficientBank) : ρ.arrs a = σ.arrs a :=
    coeffState_array q v.val c σ a ha
  have hw := hsR qN.WS (by decide) (by decide) (by decide)
  have hSlots := slots_frame F hS (haR _ (by decide)) (haR _ (by decide))
    (fun r hr => let hx := coeffState_fresh r hr; hsR r hx.1 hx.2.1 hx.2.2) hw
  let data (k : ℕ) : K := D.symm ⟨coefficientLabel q v.val k, Nat.mod_lt _ hq⟩
  have hLength : (ρ.arrs coefficientBank).length = (σ.arrs coefficientBank).length := by
    simp [ρ,coefficientDigitState,writeValues_length]
  have hData (k : ℕ) (hk : k < c) : (ρ.arrs coefficientBank)[k]? = some (D (data k)).val := by
    have hka : k < (ρ.arrs coefficientBank).length := by omega
    have hd := hDigits k hk
    change (ρ.arrs coefficientBank).getD k 0 = coefficientLabel q v.val k at hd
    rw [List.getElem?_eq_getElem hka, ← List.getD_eq_getElem _ _ hka, hd]
    simp [data]
  obtain ⟨τ,hLoad,hSlots',hValues,hKeep,hRegs,hArrKeep,hIn',hOut'⟩ :=
    encodedBankLoad_run D F coefficientBank (.var loadIndex) id data (by decide) hSlots hQ.le hB hc
      ((hsR _ (by decide) (by decide) (by decide)).trans hBase)
      ((hsR _ (by decide) (by decide) (by decide)).trans hLen) hFit
      (fun _ k hk _ hkc => evalB_var_iff.mpr ⟨hk.symm,hk ▸ hkc.trans hc⟩) hData
  have hArr' := hArrKeep coefficientBank (by decide)
  refine ⟨τ,hRun.seq hLoad,hSlots',?_,?_,congrArg List.length hArr' |>.trans hLength,?_,?_,hIn'.trans hIn,hOut'.trans hOut⟩
  · intro i
    rw [hValues i.val i.isLt]
    unfold data
    apply D.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (coefficientLabel_eq D v i)
  · intro i hi
    rw [hArr']
    exact hDigits i hi
  · intro s hs
    rw [hKeep s hs]
    exact cutSlot_value_frame F (haR canonical.mem (by decide)) hw s
  · intro r hr hI hP hN
    exact (hRegs r hr).trans (hsR r hI hP hN)

#print axioms loadCutCoefficients_run
end EvenTI.P12ComparePrep
