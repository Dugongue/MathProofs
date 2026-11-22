import EvenP14CutRankOne
import EvenP14CutScanRank

set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def cutRankInit (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (cutRankMakeOne D F) cutRankConfigure

def cutRankInitCost (F : FieldPresentation K) : ℕ := cutRankMakeOneCost F + cutRankConfigCost

/-- Install the retained-rank ABI once, before visiting the enumerated
forms. This preserves the live cut configuration and all four bases. -/
theorem cutRankInit_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n B c budget : ℕ} {σ : Env} (j : Fin 4) (tail : List ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1))+n^(d+1)+n^(d+1)+10<B)
    (hQ : Fintype.card K ≤ B)
    (hh : σ.arrs rawPairIO.array=((d+1)+(d+1))::n::tail) (hABI : σ.vars qN.WS=F.e+1)
    (hN : σ.vars (nullityAt j)=c) (hBudget : σ.vars cutChoiceBudget=budget)
    (hW : let m := n^(d+1); let z := constantsBase.value m
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) F σ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3)) :
    let m := n^(d+1)
    let z := constantsBase.value m
    ∃ τ, Run B (cutRankInit D F) σ τ (cutRankInitCost F) ∧
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) F τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      CutRankStable (d := d) (n := n) F τ ∧
      τ.vars (nullityAt j)=c ∧ τ.vars cutChoiceBudget=budget ∧
      (∀ s ≤ z, val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  let m := n^(d+1)
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let a := augmentedMatrixBase.value m
  let b := (outputBase j).value m
  let o := placedRankSource m
  have hPos : 0 < m := pow_pos (by omega) _
  have hCap : z+1<Sn := by simp [z,Sn,pairCutSlotCount,Address.value]
  obtain ⟨ρ,hOne,hSlot,hOneVal,hMem,hRegs,hArr,hIn,hOut⟩ :=
    cutRankMakeOne_run D F hW.frame.side hPos hW.frame.slots hCap hQ
  let x : Coord (d+1) n → K := fun u => val F canonical qN.WS ρ (o+(inputCoordOrder n (d+1) u).val)
  obtain ⟨τ,hInit,hRank,hVal,hFrame,hArr',hi,ho⟩ :=
    cutRankConfigure_run F x tail hd hn hB hSlot
      ((hArr _ (by decide)).trans hh)
      ((hRegs _ (by decide) (by decide) (by decide) (by decide)).trans hW.frame.side)
      ((hRegs _ (by decide) (by decide) (by decide) (by decide)).trans hABI)
      (fun _ => rfl) ((hMem z (Nat.ne_of_lt (Nat.lt_succ_self z))).trans hW.frame.zero_value) hOneVal
  have hKept : ∀ s ≤ z, val F canonical qN.WS τ s=val F canonical qN.WS σ s :=
    fun s hs => (hVal s).trans (hMem s (Nat.ne_of_lt (lt_of_le_of_lt hs (Nat.lt_succ_self z))))
  have hSame (r : String) (h0 : r ∉ cutRankConfigNames)
      (h1 : r≠cutRankRawOrder) (h2 : r≠cutRankRawWidth) (h3 : r≠inputLabel)
      (h4 : r≠Mathproof.P15GEDigitLoad20261007.destination)
      (h5 : r≠Mathproof.P15FactorIMP20261007.rCv) (h6 : r≠Mathproof.P15FactorIMP20261007.rTd) :
      τ.vars r=σ.vars r :=
    (hFrame r h0 h1 h2).trans (hRegs r h3 h4 h5 h6)
  have hCount (r : String) (hr : r ∈ [dL,coeffLength,loadLength,loadBase,cutCoeffStart,
      cutBasisStart,cutFormStart,shapePower.out,cutChoiceBudget]) : τ.vars r=σ.vars r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e|e|e|e|e|e|e|e|e <;> subst r <;>
      exact hSame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hRankZ : τ.vars dZ = z := hRank.regs (dZ,z) (by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hRankT : τ.vars dT = z+2 := hRank.regs (dT,z+2) (by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hRankU : τ.vars dU = z+3 := hRank.regs (dU,z+3) (by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hPrepared : CutVisitInput (B := B) (Sn := Sn) F τ a b o c m z (z+2) (z+3) := by
    refine ⟨⟨hRank.slots,hW.frame.layout,hW.frame.count_word,
      (hCount _ (by simp)).trans hW.frame.coeff_start,
      (hCount _ (by simp)).trans hW.frame.basis_start,
      (hCount _ (by simp)).trans hW.frame.form_start,
      (hCount _ (by simp)).trans hW.frame.side,
      (hCount _ (by simp)).trans hW.frame.count,
      hRankZ,hRankT,hRankU,hRank.zero⟩,?_,
      (hCount _ (by simp)).trans hW.coefficient_count,
      (hCount _ (by simp)).trans hW.load_base,
      (hCount _ (by simp)).trans hW.load_count⟩
    rw [hArr',hArr _ (by decide)]
    exact hW.coefficient_bank
  refine ⟨τ,hOne.seq hInit,hPrepared,⟨hRank.regs,hRank.one⟩,?_,
    (hCount _ (by simp)).trans hBudget,hKept,hi.trans hIn,ho.trans hOut⟩
  exact (hSame _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)).trans hN

#print axioms cutRankInit_run
end EvenTI.P12ComparePrep
