import EvenP14CutRankConfigure
import EvenP14CutRankSweep
import EvenP12ComparePrepFourBudget

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P10Scan
open Lax51.BinaryWordEncoding (bitSize)
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dL)
open Mathproof.P15GEDigitLoad20261007 (destination)
open Mathproof.P15FactorIMP20261007 (rCv rTd)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def cutRankMakeOne (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.assign inputLabel (.lit (D 1).val)) <|
  .seq (.assign destination (Address.add constantsBase (.litSucc 0)).expr) <|
    installEncodedDigit D F

def cutRankMakeOneCost (F : FieldPresentation K) : ℕ :=
  2+((Address.add constantsBase (.litSucc 0)).expr.size+1)+installEncodedDigitCost F

theorem cutRankMakeOne_run (D : FieldEncoding K) (F : FieldPresentation K)
    {m Sn B : ℕ} {σ : Env} (hm : σ.vars shapePower.out=m) (hPos : 0 < m)
    (hSlot : Slots F canonical qN.WS Sn B σ)
    (hFit : constantsBase.value m+1<Sn) (hQ : Fintype.card K≤B) :
    ∃ τ, Run B (cutRankMakeOne D F) σ τ
        (cutRankMakeOneCost F) ∧ Slots F canonical qN.WS Sn B τ ∧
      val F canonical qN.WS τ (constantsBase.value m+1)=1 ∧
      (∀ s, s≠constantsBase.value m+1 → val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      (∀ r, r≠inputLabel → r≠destination → r≠rCv → r≠rTd → τ.vars r=σ.vars r) ∧
      (∀ a, a≠canonical.mem → τ.arrs a=σ.arrs a) ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  let j := constantsBase.value m+1
  let μ := σ.setVar inputLabel (D 1).val
  let ν := μ.setVar destination j
  let addr := Address.add constantsBase (.litSucc 0)
  have hm' : μ.vars shapePower.out=m := hm
  have hJ : j<B := hFit.trans hSlot.slots_word
  have ev : addr.expr.evalB B μ = some j :=
    Address.eval hm' hPos addr hJ
  have r₁ : Run B (.assign inputLabel (.lit (D 1).val)) σ μ 2 :=
    Run.assign (evalB_lit ((D 1).isLt.trans_le hQ))
  have r₂ : Run B (.assign destination addr.expr) μ ν (addr.expr.size+1) :=
    Run.assign ev
  have hν : Slots F canonical qN.WS Sn B ν :=
    Slots.setVar F canonical (Slots.setVar F canonical hSlot (by decide) (by decide) _)
      (by decide) (by decide) _
  obtain ⟨τ,r₃,hτ,hOne,hMem,hVars,hArr,hIn,hOut⟩ := installEncodedDigit_run D F (σ := ν) 1
    hν hQ (by simp [ν,μ,show inputLabel≠destination by decide]) (by simp [ν,j]) hFit
  have hRun : Run B (cutRankMakeOne D F) σ τ
      (2+(addr.expr.size+1)+installEncodedDigitCost F) := by
    refine (r₁.seq (r₂.seq r₃)).mono ?_
    omega
  refine ⟨τ,hRun,hτ,hOne,?_,?_,hArr,hIn,hOut⟩
  · intro s hs
    rw [hMem s hs]
    exact (val_setVar F canonical (by decide : destination≠qN.WS) μ j s).trans
      (val_setVar F canonical (by decide : inputLabel≠qN.WS) σ _ s)
  · intro x hx hx' hcv htd
    rw [hVars x hcv htd]
    simp [ν,μ,hx,hx']

#print axioms cutRankMakeOne_run
end EvenTI.P12ComparePrep
