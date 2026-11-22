import EvenP14CutScanEngine
import EvenP14CutNonzero

set_option autoImplicit false
set_option maxHeartbeats 1350000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dI dO dL dT dU dZ)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Store a stable candidate identifier. The original basis banks and the paid
one-candidate reconstruction remain available when the identifier is consumed. -/
def emitCutCandidate : Com :=
  .ite (.eq (.var cutNonzero) (.lit 1)) (.write (.var cutChoiceIndex)) .skip

noncomputable def visitCutCandidate (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (cutCandidateProgram D F) (.seq (cutNonzeroProgram (D 0).val) emitCutCandidate)

def cutCodeGood (q c zero v : ℕ) : Bool :=
  (List.range c).any (fun j => decide (coefficientLabel q v j ≠ zero))

theorem cutCodeGood_spec {q c zero v : ℕ} : cutCodeGood q c zero v = true ↔
    ∃ j < c, coefficientLabel q v j ≠ zero := by
  simp [cutCodeGood,List.any_eq_true]

noncomputable def visitCutCandidateCost (F : FieldPresentation K) (c m : ℕ) : ℕ :=
  cutCandidateCost F c m + (24*c+8+10)

/-- One complete visit, including actual reconstruction and a field-encoding
independent nonzero filter. This is the exact order-four form filter. -/
theorem visitCutCandidate_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B Sn a b o c m z t u : ℕ} {σ : Env} (v : Fin (Fintype.card K ^ c))
    (h : CutVisitInput (B := B) (Sn := Sn) F σ a b o c m z t u)
    (hQ : Fintype.card K < B) (hPow : Fintype.card K^c < B)
    (hIdx : σ.vars cutChoiceIndex = v.val) :
    ∃ τ, Run B (visitCutCandidate D F) σ τ (visitCutCandidateCost F c m) ∧
      CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u ∧
      τ.vars cutChoiceIndex = v.val ∧ τ.vars cutChoiceLength = σ.vars cutChoiceLength ∧
      (∀ j : Fin m, val F canonical qN.WS τ (o+j.val) =
        ∑ i : Fin c, coefficients D c v i * val F canonical qN.WS σ (b+(i.val*m+j.val))) ∧
      (∀ s < Sn, (s < a ∨ a+c ≤ s) → (s < o ∨ o+m ≤ s) → s ≠ t → s ≠ u →
        val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ++
        (if cutCodeGood (Fintype.card K) c (D 0).val v.val then [v.val] else []) := by
  let q := Fintype.card K
  let zero := (D 0).val
  have ht := h.frame.count_word
  have hOne : 1 < B := by omega
  have hcWord : c < B := by omega
  have hz := (D 0).isLt.trans hQ
  have hab := h.frame.layout.coefficient_before
  have hbo := h.frame.layout.output_before
  have hbz := h.frame.layout.basis_before
  have hzt := h.frame.layout.zero_before
  have htu := h.frame.layout.scratch_order
  have h3 := h.frame.layout.fit
  obtain ⟨α,ha,hSlots,hValues,hDigits,hLen,hMem,hVars,hIn,hOut⟩ :=
    cutCandidateProgram_run D F v h.frame hQ hPow h.coefficient_bank hIdx h.coefficient_count h.load_base h.load_count
  have hcLive : α.vars coeffLength = c :=
    (hVars _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.coefficient_count
  have hBound (i : ℕ) (hi : i < c) : (α.arrs coefficientBank).getD i 0 < B := by
    rw [hDigits i hi]
    exact (Nat.mod_lt _ (Fintype.card_pos (α := K))).trans hQ
  obtain ⟨β,hb,hBit,hGood,hNoRegs,hNoArr,hNoIn,hNoOut⟩ := cutNonzeroProgram_run zero c B α
    hOne hcWord hz hcLive (by rw [hLen]; exact h.coefficient_bank) hBound
  have hGood' : β.vars cutNonzero = 1 ↔ cutCodeGood q c zero v.val = true := by
    rw [hGood,cutCodeGood_spec]
    constructor
    · rintro ⟨i,hi,hn⟩
      exact ⟨i,hi,(hDigits i hi) ▸ hn⟩
    · rintro ⟨i,hi,hn⟩
      exact ⟨i,hi,(hDigits i hi).symm ▸ hn⟩
  have hExt (r : String) (hR : r ∉ regNames canonical) (hL : ¬loadChanges r)
      (hI : r ≠ coeffIndex) (hP : r ≠ coeffPower) (hN : r ≠ coeffNumber)
      (hDI : r ≠ dI) (hDO : r ≠ dO) (hE : r ≠ cutEntry)
      (hZ : r ≠ cutZeroCursor) (hNZ : r ≠ cutNonzero) : β.vars r = σ.vars r :=
    (hNoRegs r hZ hNZ).trans (hVars r hR hL hI hP hN hDI hDO hE)
  have hLive := (hExt cutChoiceIndex (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hIdx
  have er : (Expr.var cutChoiceIndex).evalB B β = some v.val :=
    evalB_var_iff.mpr ⟨hLive.symm,hLive ▸ v.isLt.trans hPow⟩
  let out := if cutCodeGood q c zero v.val then [v.val] else []
  let τ := {β with out := β.out ++ out}
  have eb := evalB_condEq (evalB_var (σ := β) (x := cutNonzero) (hBit.trans_lt hOne))
    (evalB_lit hOne)
  have hEmit : Run B emitCutCandidate β τ 10 := by
    by_cases hyes : β.vars cutNonzero = 1
    · have e : (Cond.eq (.var cutNonzero) (.lit 1)).evalB B β = some true := by simpa [hyes] using eb
      have h := Run.ite_true (d := .skip) e (Run.write er)
      simpa [emitCutCandidate,τ,out,(hGood'.mp hyes)] using h.mono (by decide : _ ≤ 10)
    · have e : (Cond.eq (.var cutNonzero) (.lit 1)).evalB B β = some false := by simpa [hyes] using eb
      have h := Run.ite_false (c := .write (.var cutChoiceIndex)) e Run.skip
      have ht : cutCodeGood q c zero v.val = false := Bool.eq_false_iff.mpr (fun ht => hyes (hGood'.mpr ht))
      simpa [emitCutCandidate,τ,out,ht] using h.mono (by decide : _ ≤ 10)
  have hKeep (r : String) (hR : r ∈ regNames canonical) : τ.vars r = α.vars r := by
    have hNo : ∀ x ∈ [cutZeroCursor,cutNonzero], x ∉ regNames canonical := by decide
    exact hNoRegs r (fun he => hNo _ (by simp) (he ▸ hR)) (fun he => hNo _ (by simp) (he ▸ hR))
  have hWS : τ.vars qN.WS = α.vars qN.WS := hNoRegs _ (by decide) (by decide)
  have hArr : τ.arrs = α.arrs := hNoArr
  have newSlots := slots_frame F hSlots (congrFun hArr canonical.mem) (congrFun hArr canonical.scratch) hKeep hWS
  have hValue (s : ℕ) : val F canonical qN.WS τ s = val F canonical qN.WS α s := by
    exact cutSlot_value_frame F (congrFun hArr canonical.mem) hWS s
  have hNew : CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z t u := by
    refine ⟨⟨newSlots,h.frame.layout,h.frame.count_word,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.coeff_start
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.basis_start
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.form_start
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.side
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.count
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.zero
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.scratch₁
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.frame.scratch₂
    · exact (hValue z).trans ((hMem z (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)).trans h.frame.zero_value)
    · rw [hArr,hLen]
      exact h.coefficient_bank
    · exact (hNoRegs _ (by decide) (by decide)).trans hcLive
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.load_base
    · exact (hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.load_count
  refine ⟨τ,?_,hNew,hLive,?_,?_,?_,hNoIn.trans hIn,?_⟩
  · simpa [visitCutCandidate,visitCutCandidateCost,zero,Nat.add_assoc] using ha.seq (hb.seq hEmit)
  · exact hExt _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro j
    exact (hValue _).trans (hValues j)
  · intro s hs hC' hO ht' hu
    exact (hValue s).trans (hMem s hs hC' hO ht' hu)
  · change β.out++out = _
    rw [hNoOut,hOut]

#print axioms visitCutCandidate_run
end EvenTI.P12ComparePrep
