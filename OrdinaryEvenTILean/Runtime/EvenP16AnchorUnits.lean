import EvenP14CutRankOne
import EvenP16AnchorSquareTrace

set_option autoImplicit false

namespace EvenTI.P16Execution

open EvenTI.Contract EvenTI.P12ComparePrep EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dZ)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def loadAnchorConstant (D : FieldEncoding K) (F : FieldPresentation K)
    (slot : String) (x : K) : Com :=
  .seq (.assign inputLabel (.lit (D x).val))
    (.seq (.assign destination (.var slot)) (installEncodedDigit D F))

theorem loadAnchorConstant_run (D : FieldEncoding K) (F : FieldPresentation K) (x : K)
    {B S z : ℕ} {s : Env} (slot : String) (hFresh : slot≠inputLabel)
    (h : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B)
    (hz : z < S) (hs : s.vars slot=z) :
    ∃ t, Run B (loadAnchorConstant D F slot x) s t (4+installEncodedDigitCost F) ∧
      Slots F canonical qN.WS S B t ∧ val F canonical qN.WS t z=x ∧
      (∀ i, i≠z → val F canonical qN.WS t i=val F canonical qN.WS s i) ∧
      (∀ r, r≠inputLabel → r≠destination → r≠rCv → r≠rTd → t.vars r=s.vars r) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let u := s.setVar inputLabel (D x).val
  let v := u.setVar destination z
  have r₁ : Run B (.assign inputLabel (.lit (D x).val)) s u 2 :=
    Run.assign (evalB_lit ((D x).isLt.trans_le hQ))
  have r₂ : Run B (.assign destination (.var slot)) u v 2 :=
    Run.assign (evalB_var_iff.mpr ⟨by simp [u,hFresh,hs],by simp [u,hFresh,hs,hz.trans h.slots_word]⟩)
  have hV : Slots F canonical qN.WS S B v := Slots.setVar F canonical
    (Slots.setVar F canonical h (by decide : inputLabel ∉ Mathproof.Problem18ClaudeIMPSlots20261001.regNames canonical)
      (by decide : inputLabel≠qN.WS) (D x).val)
    (by decide : destination ∉ Mathproof.Problem18ClaudeIMPSlots20261001.regNames canonical)
    (by decide : destination≠qN.WS) z
  obtain ⟨t,r,hS,hx,hM,hVars,_,hi,ho⟩ := installEncodedDigit_run D F (σ:=v) x hV hQ
    (by simp [v,u,show inputLabel≠destination by decide]) (by simp [v]) hz
  refine ⟨t,(r₁.seq (r₂.seq r)).mono (by omega),hS,hx,?_,?_,hi,ho⟩
  · intro i hne
    rw [hM i hne]
    exact (val_setVar F canonical (by decide : destination≠qN.WS) u z i).trans
      (val_setVar F canonical (by decide : inputLabel≠qN.WS) s _ i)
  · intro a ha hb hc hd
    rw [hVars a hc hd]
    simp [v,u,ha,hb]

/-- Establish the zero and one slots after a prior matrix calculation. No
assumption about their previous contents survives this actual execution. -/
noncomputable def initializeAnchorUnits (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (loadAnchorConstant D F dZ 0) (loadAnchorConstant D F anchorUnitWord 1)

theorem initializeAnchorUnits_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S z one : ℕ} {s : Env} (h : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B)
    (hz : z < S) (ho : one < S) (hne : z≠one) (hZ : s.vars dZ=z) (hO : s.vars anchorUnitWord=one) :
    ∃ t, Run B (initializeAnchorUnits D F) s t (2*(4+installEncodedDigitCost F)) ∧
      Slots F canonical qN.WS S B t ∧ val F canonical qN.WS t z=0 ∧ val F canonical qN.WS t one=1 ∧
      (∀ i, i≠z → i≠one → val F canonical qN.WS t i=val F canonical qN.WS s i) ∧
      (∀ r, r≠inputLabel → r≠destination → r≠rCv → r≠rTd → t.vars r=s.vars r) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨u,ru,hu,hZero,hMU,hVU,hIU,hOU⟩ := loadAnchorConstant_run D F 0 dZ (by decide) h hQ hz hZ
  have hO' : u.vars anchorUnitWord=one :=
    (hVU anchorUnitWord (by decide) (by decide) (by decide) (by decide)).trans hO
  obtain ⟨t,rt,ht,hOne,hMT,hVT,hIT,hOT⟩ := loadAnchorConstant_run D F 1 anchorUnitWord (by decide) hu hQ ho hO'
  refine ⟨t,(ru.seq rt).mono (by omega),ht,(hMT _ hne).trans hZero,hOne,?_,?_,hIT.trans hIU,hOT.trans hOU⟩
  · intro i h₁ h₂
    exact (hMT i h₂).trans (hMU i h₁)
  · intro r h₁ h₂ h₃ h₄
    exact (hVT r h₁ h₂ h₃ h₄).trans (hVU r h₁ h₂ h₃ h₄)

#print axioms initializeAnchorUnits_run
end EvenTI.P16Execution