import EvenP14CutVisit

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def cappedNonzeroCutScan (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  cappedCutScanWith (Fintype.card K) (visitCutCandidate D F) j

/-- Exact nonzero specialization, with the literal decoder and strided
field reconstruction paid inside every accepted-range visit. -/
theorem cappedNonzeroCutScan_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn a b o c m z t u budget : ℕ} {σ : Env} (j : Fin 4)
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c m z t u)
    (hLive : σ.vars (nullityAt j) = c) (hb : σ.vars cutChoiceBudget = budget)
    (hbM : budget ≤ m) (hWord : (m+Fintype.card K+1)*(m+Fintype.card K+1) < B) :
    let q := Fintype.card K
    let count := cappedCutChoiceCount q c budget
    ∃ τ, Run B (cappedNonzeroCutScan D F j) σ τ
      (30*(m+q)+42 + ((visitCutCandidateCost F c m+8)*count+6)) ∧
      CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u ∧
      (∀ s < z, o+m ≤ s → val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ++ (List.range count).filter (cutCodeGood q c (D 0).val) := by
  apply cappedCutScanWith_run F (visitCutCandidate D F) (visitCutCandidateCost F c m)
    (cutCodeGood (Fintype.card K) c (D 0).val) (fun _ => True) (o+m) j h hLive hb hbM hWord
    (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  intro ρ v _ hW _ hq hPow hIdx
  obtain ⟨τ,hr,hWork,hCode,hCount,_,hFr,hIn,hOut⟩ := visitCutCandidate_run D F v hW hq hPow hIdx
  have hA := hW.frame.layout.coefficient_before
  have hZ := hW.frame.layout.zero_before
  have hT := hW.frame.layout.scratch_order
  have hU := hW.frame.layout.fit
  exact ⟨τ,hr,hWork,True.intro,hCode,hCount,fun s hs ho =>
    hFr s (by omega) (Or.inr (by omega)) (Or.inr ho) (by omega) (by omega),hIn,hOut⟩

#print axioms cappedNonzeroCutScan_run
end EvenTI.P12ComparePrep
