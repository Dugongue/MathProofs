import EvenP12ComparePrepKernelLayout

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (install installed_arrays installed_scalar installed_slots)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs KBLay kAM kOUT)
open Mathproof.P15FactorIMP20261007 (rCv rTd)
open Mathproof.P15RecogIMPDot20261007 (dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15GEDigitLoad20261007 (destination)
set_option autoImplicit false

structure CutRegisters (τ : Env) (target : Bool) (idx : Fin 4) (m : Nat) : Prop where
  hRows : τ.vars originalRows = m
  hCols : τ.vars originalColumns = m
  hNR : τ.vars tNR = m
  hD : τ.vars tD = m
  hBase : τ.vars loadBase = rawMatrixBase.value m
  hRB : τ.vars tRB = rawMatrixBase.value m
  hLength : τ.vars loadLength = m*m
  hAM : τ.vars kAM = augmentedMatrixBase.value m
  hOUT : τ.vars kOUT = (outputBase idx).value m
  hInpBase : τ.vars inputBase = tensorOffset (m*m) target
  hZ : τ.vars dZ = constantsBase.value m
  hO : τ.vars rOs = constantsBase.value m+1
  hT : τ.vars dT = constantsBase.value m+2
  hU : τ.vars dU = constantsBase.value m+3

theorem kernelState_registers (σ : Env) (target : Bool) (idx : Fin 4) (m : Nat) :
    CutRegisters (kernelState target idx m σ) target idx m := by
  cases target <;> constructor <;> rfl

theorem kernelState_frame (σ : Env) (target : Bool) (idx : Fin 4) (m : Nat) :
    (kernelState target idx m σ).arrs = σ.arrs ∧
      (kernelState target idx m σ).inp = σ.inp ∧ (kernelState target idx m σ).out = σ.out :=
  installed_arrays _ _

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem kernelState_slots (F : FieldPresentation K) (target : Bool) (idx : Fin 4)
    (m : Nat) {Sn B : Nat} {σ : Env}
    (hS : Slots F canonical qN.WS Sn B σ)
    (hWS : σ.vars qN.WS = F.e+1) :
    let τ := kernelState target idx m σ
    Slots F canonical qN.WS Sn B τ ∧ τ.vars qN.WS = F.e+1 ∧
      ∀ j, val F canonical qN.WS τ j = val F canonical qN.WS σ j := by
  let xs := (kernelBindings target idx).map fun p => (p.1,p.2.value m)
  have hNames (p : String × Nat) (hp : p ∈ xs) :
      canonical.e ≠ p.1 ∧ canonical.p ≠ p.1 ∧ canonical.modBase ≠ p.1 ∧
        canonical.exp ≠ p.1 ∧ qN.WS ≠ p.1 := by
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    simp only [kernelBindings,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> simp only [Prod.fst] <;> decide
  have hw : (install xs σ).vars qN.WS = σ.vars qN.WS :=
    installed_scalar _ _ _ (fun p hp => (hNames p hp).2.2.2.2)
  refine ⟨installed_slots F xs σ hS hNames,hw.trans hWS,?_⟩
  intro j
  unfold val
  rw [show (kernelState target idx m σ).vars qN.WS = σ.vars qN.WS from hw]
  have hmem := (kernelState_frame σ target idx m).1
  change Mathproof.Problem18IMPFieldPresentation20261001.decode F
    (fun i => ((kernelState target idx m σ).arrs canonical.mem).getD
      (σ.vars qN.WS+j*F.e+i.val) 0) = _
  rw [hmem]
  rfl

/-- Setup for one of the four cuts. The same paid assignment code works for
both source/target banks and both orientations. -/
noncomputable def oneCutSetup (D : FieldEncoding K) (F : FieldPresentation K) (target : Bool) (idx : Fin 4) : Com :=
  .seq (kernelAssignment target idx)
    (.seq (.assign inputLabel (.lit (D 1).val))
      (.seq (.assign destination (.var rOs)) (installEncodedDigit D F)))

theorem oneCutSetup_run (D : FieldEncoding K) (F : FieldPresentation K)
    (target : Bool) (idx : Fin 4) (m : Nat) {Sn B : Nat} {σ : Env}
    (hm : σ.vars shapePower.out = m) (hPos : 0 < m)
    (hS : Slots F canonical qN.WS Sn B σ) (hWS : σ.vars qN.WS = F.e+1)
    (hFits : ∀ v ∈ kernelBindings target idx, v.2.value m < B)
    (hCard : Fintype.card K ≤ B) (hO : constantsBase.value m+1 < Sn)
    (hz : val F canonical qN.WS σ (constantsBase.value m) = 0) :
    ∃ τ, Run B (oneCutSetup D F target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+installEncodedDigitCost F) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars qN.WS = F.e+1 ∧
      CutRegisters τ target idx m ∧
      val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      val F canonical qN.WS τ (constantsBase.value m+1) = 1 ∧
      (∀ a, a ≠ canonical.mem → τ.arrs a = σ.arrs a) ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  let r := kernelState target idx m σ
  have hr := kernelAssignment_run target idx m hm hPos hFits
  have hRegs := kernelState_registers σ target idx m
  obtain ⟨hS',hWS',hFrame⟩ := kernelState_slots F target idx m hS hWS
  let x := r.setVar inputLabel (D 1).val
  let y := x.setVar destination (constantsBase.value m+1)
  have r₁ : Run B (.assign inputLabel (.lit (D 1).val)) r x 2 :=
    Run.assign (evalB_lit ((D 1).isLt.trans_le hCard))
  have hOx : x.vars rOs = constantsBase.value m+1 := by
    rw [show x.vars rOs = r.vars rOs by rfl]
    exact hRegs.hO
  have r₂ : Run B (.assign destination (.var rOs)) x y 2 := by
    apply Run.assign
    rw [evalB_var_iff,hOx]
    exact ⟨rfl,hO.trans hS.slots_word⟩
  have hSy : Slots F canonical qN.WS Sn B y :=
    Slots.setVar F canonical (Slots.setVar F canonical hS' (by decide) (by decide) _)
      (by decide) (by decide) _
  obtain ⟨τ,r₃,hSτ,hOne,hOutside,hVars,hArrays,hInp,hOut⟩ :=
    installEncodedDigit_run D F (σ := y) 1 hSy hCard (by simp [y,x,show inputLabel ≠ destination by decide])
      (by simp [y]) hO
  have hKeep (v : String) (h₁ : v ≠ rCv) (h₂ : v ≠ rTd)
      (h₃ : v ≠ inputLabel) (h₄ : v ≠ destination) : τ.vars v = r.vars v := by
    rw [hVars v h₁ h₂]
    simp [y,x,h₃,h₄]
  have hFrameArr := kernelState_frame σ target idx m
  have hRun : Run B (oneCutSetup D F target idx) σ τ
      ((((kernelBindings target idx).map fun v => v.2.expr.size+1).sum)+5+installEncodedDigitCost F) :=
    (hr.seq (r₁.seq (r₂.seq r₃))).mono (by omega)
  refine ⟨τ,hRun,hSτ,(hKeep _ (by decide) (by decide) (by decide) (by decide)).trans hWS',
    ?_,?_,hOne,?_,?_,?_⟩
  · exact ⟨(hKeep originalRows (by decide) (by decide) (by decide) (by decide)).trans hRegs.hRows,
      (hKeep originalColumns (by decide) (by decide) (by decide) (by decide)).trans hRegs.hCols,
      (hKeep tNR (by decide) (by decide) (by decide) (by decide)).trans hRegs.hNR,
      (hKeep tD (by decide) (by decide) (by decide) (by decide)).trans hRegs.hD,
      (hKeep loadBase (by decide) (by decide) (by decide) (by decide)).trans hRegs.hBase,
      (hKeep tRB (by decide) (by decide) (by decide) (by decide)).trans hRegs.hRB,
      (hKeep loadLength (by decide) (by decide) (by decide) (by decide)).trans hRegs.hLength,
      (hKeep kAM (by decide) (by decide) (by decide) (by decide)).trans hRegs.hAM,
      (hKeep kOUT (by decide) (by decide) (by decide) (by decide)).trans hRegs.hOUT,
      (hKeep inputBase (by decide) (by decide) (by decide) (by decide)).trans hRegs.hInpBase,
      (hKeep dZ (by decide) (by decide) (by decide) (by decide)).trans hRegs.hZ,
      (hKeep rOs (by decide) (by decide) (by decide) (by decide)).trans hRegs.hO,
      (hKeep dT (by decide) (by decide) (by decide) (by decide)).trans hRegs.hT,
      (hKeep dU (by decide) (by decide) (by decide) (by decide)).trans hRegs.hU⟩
  · rw [hOutside _ (by omega),show y = x.setVar destination _ from rfl,
      val_setVar F canonical (by decide),show x = r.setVar inputLabel _ from rfl,
      val_setVar F canonical (by decide)]
    exact (hFrame _).trans hz
  · intro a ha
    rw [hArrays a ha]
    exact congrFun hFrameArr.1 a
  · exact hInp.trans hFrameArr.2.1
  · exact hOut.trans hFrameArr.2.2

#print axioms kernelState_slots
#print axioms oneCutSetup_run
end EvenTI.P12ComparePrep
