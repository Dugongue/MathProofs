import EvenP14CutScanEngine
import EvenP14CutRankSweep
import EvenP14CutRankLayout

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dI dO dL dZ dT dU)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def emitRankedCutCandidate : Com :=
  .ite (.eq (.var cutRankAccept) (.lit 1)) (.write (.var cutChoiceIndex)) .skip

noncomputable def rankedCutVisit (D : FieldEncoding K) (FP : FieldPresentation K) : Com :=
  .seq (cutCandidateProgram D FP) (.seq cutRankSweepPreservingCount emitRankedCutCandidate)

noncomputable def cappedRankedCutScan (D : FieldEncoding K) (FP : FieldPresentation K) (j : Fin 4) : Com :=
  cappedCutScanWith (Fintype.card K) (rankedCutVisit D FP) j

structure CutRankStable {d n : ℕ} (FP : FieldPresentation K) (σ : Env) : Prop where
  regs : ∀ p ∈ cutRankArgs d n (placedRankSource (n^(d+1))) (placedRankRows (n^(d+1)))
      (placedRankAugmented (n^(d+1))) (placedRankOutput (n^(d+1)))
      (constantsBase.value (n^(d+1))) FP.e, σ.vars p.1 = p.2
  one : val FP canonical qN.WS σ (constantsBase.value (n^(d+1))+1) = 1

noncomputable def cutIndexedForm (D : FieldEncoding K) (FP : FieldPresentation K)
    {d n c : ℕ} (σ : Env) (j : Fin 4) (v : Fin (Fintype.card K^c)) : Coord (d+1) n → K :=
  fun x => ∑ i : Fin c, coefficients D c v i * val FP canonical qN.WS σ
    ((outputBase j).value (n^(d+1))+(i.val*n^(d+1)+(inputCoordOrder n (d+1) x).val))

noncomputable def cutRankCodeGood (D : FieldEncoding K) (FP : FieldPresentation K)
    (d n c : ℕ) (σ : Env) (j : Fin 4) (v : ℕ) : Bool :=
  if h : v < Fintype.card K^c then rawRetainedFullRank (cutIndexedForm D FP (d := d) (n := n) σ j ⟨v,h⟩)
  else false

private theorem cutRankArg_in {d n src R A O Z e : ℕ} {p : String × ℕ}
    (h : p ∈ cutRankArgs d n src R A O Z e) : p.1 ∈ cutRankArgNames := by
  change p.1 ∈ (cutRankArgs d n src R A O Z e).map Prod.fst
  exact List.mem_map.mpr ⟨p,h,rfl⟩

private abbrev CandidateFresh (r : String) : Prop :=
  r ∉ regNames canonical ∧ ¬loadChanges r ∧ r ≠ coeffIndex ∧ r ≠ coeffPower ∧ r ≠ coeffNumber ∧
    r ≠ dI ∧ r ≠ dO ∧ r ≠ cutEntry

private theorem candidate_rank_regs : ∀ r ∈ cutRankArgNames, CandidateFresh r := by decide
private theorem cap_rank_regs : ∀ r ∈ cutRankArgNames,
    r ∉ ["left","d","n","i","r",cutChoiceLength] := by decide
private theorem rank_index_fresh : cutChoiceIndex ∉ cutRankArgNames := by decide

/-- Higher folds use the actual retained-rank sweep. The candidate is rebuilt
from the same live basis bank as the order-four specialization. -/
theorem cappedRankedCutScan_run (D : FieldEncoding K) (FP : FieldPresentation K)
    {B d n c budget : ℕ} {σ : Env} (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1)) + n^(d+1) + n^(d+1) + 10 < B)
    (hChoice : (n^(d+1)+Fintype.card K+1)*(n^(d+1)+Fintype.card K+1) < B)
    (hLive : σ.vars (nullityAt j) = c) (hBudget : σ.vars cutChoiceBudget = budget)
    (hBudgetSide : budget ≤ n^(d+1)) (hStable : CutRankStable (d := d) (n := n) FP σ)
    (hW : let m := n^(d+1); let z := constantsBase.value m
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) FP σ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3)) :
    let q := Fintype.card K; let m := n^(d+1); let z := constantsBase.value m
    let N := cappedCutChoiceCount q c budget
    let cost := cutCandidateCost FP c m + ((cutRankModeCost FP m+24)*(d+1)+14+10)
    ∃ τ, Run B (cappedRankedCutScan D FP j) σ τ (30*(m+q)+42 + ((cost+8)*N+6)) ∧
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) FP τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      (∀ s < z, firstOutputBase.value m ≤ s → val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ++ (List.range N).filter (cutRankCodeGood D FP d n c σ j) := by
  let m := n^(d+1)
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let a := augmentedMatrixBase.value m
  let b := (outputBase j).value m
  let o := placedRankSource m
  let rb := placedRankRows m
  let am := placedRankAugmented m
  let dest := placedRankOutput m
  let pivot := firstOutputBase.value m
  let stable := CutRankStable (d := d) (n := n) FP
  let good := cutRankCodeGood D FP d n c σ j
  let cost := cutCandidateCost FP c m + ((cutRankModeCost FP m+24)*(d+1)+14+10)
  have layout := placedRankFits_of_cut hd hn hB
  have hm : n^d*n = m := (pow_succ n d).symm
  have hFour : 4 ≤ m := by
    have h₄ : 4 ≤ n^2 := by nlinarith
    exact h₄.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hCut : o+m ≤ pivot := by
    have hmm : m ≤ m*m := Nat.le_mul_of_pos_right _ (by omega)
    simp only [o,pivot,placedRankSource,firstOutputBase,Address.value,cutArea_value]
    omega
  have hb : pivot ≤ b := by rw [show b = _ from outputBase_value m j]; omega
  have hCutM : b+m*m ≤ z := outputBank_point_upper m j
  have hkS : z+4 ≤ Sn := by simp [Sn,z,pairCutSlotCount,Address.value]
  have hword : Sn+m+m+10 < B := hB
  have hRword : d+1 < B := by
    have hD := (Nat.lt_two_pow_self (n := d+1)).le.trans (Nat.pow_le_pow_left hn (d+1))
    omega
  have hDoCut (s : ℕ) (hs : s < z) (hp : pivot ≤ s) :
      CutRankSlotFixed d n rb dest z Sn s := by
    have h1 : (n+1)*XBs (n^d) n ≤ a := layout.scratch_below
    have h2 : dest+n*n ≤ pivot := layout.output_before_bases
    exact ⟨by omega,by
      have hh : a ≤ pivot := by simp [a,pivot,firstOutputBase,Address.value]
      omega,Or.inr (by omega),by omega,by omega⟩
  apply cappedCutScanWith_run FP (rankedCutVisit D FP) cost good stable pivot j hW hLive hBudget hBudgetSide hChoice
  · intro ρ ha hr
    refine ⟨fun p hp => (hr p.1 (cap_rank_regs _ (cutRankArg_in hp))).trans (hStable.regs p hp),?_⟩
    have hw := hr qN.WS (by decide)
    exact (cutSlot_value_frame FP (congrFun ha canonical.mem) hw _).trans hStable.one
  · intro ρ k hs
    refine ⟨fun p hp => ?_,(val_setVar FP canonical (by decide : cutChoiceIndex ≠ qN.WS) ρ k _).trans hs.one⟩
    have hn : p.1 ≠ cutChoiceIndex := fun eq => rank_index_fresh (eq ▸ cutRankArg_in hp)
    simpa only [vars_setVar,if_neg hn] using hs.regs p hp
  · intro ρ v hStableρ hWρ hBank hQ hPow hIdx
    change CutVisitInput (B := B) (Sn := Sn) FP ρ a b o c m z (z+2) (z+3) at hWρ
    have hFR : a+c ≤ o := hWρ.frame.layout.coefficient_before
    have hCB : c+1 < B := hWρ.frame.count_word
    have hGeom (s : ℕ) (hl : o+m ≤ s) (hu : s ≤ z+1) :
        s < Sn ∧ (s < a ∨ a+c ≤ s) ∧ (s < o ∨ o+m ≤ s) ∧ s ≠ z+2 ∧ s ≠ z+3 :=
      ⟨by omega,Or.inr (by omega),Or.inr hl,by omega,by omega⟩
    obtain ⟨α,hRebuild,hSlots,hValues,_,hSize,hMem,hVars,hIn,hOut⟩ :=
      cutCandidateProgram_run D FP v hWρ.frame hQ hPow hWρ.coefficient_bank hIdx
        hWρ.coefficient_count hWρ.load_base hWρ.load_count
    have hCVar (r : String) (hr : CandidateFresh r) : α.vars r = ρ.vars r :=
      hVars r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1
        hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2
    have hIdxα := (hCVar cutChoiceIndex (by decide)).trans hIdx
    have hDraw : α.vars dL = c :=
      (hCVar dL (by decide)).trans hWρ.frame.count
    have hFrozen (s : ℕ) (hl : o+m ≤ s) (hu : s ≤ z+1) :
        val FP canonical qN.WS α s = val FP canonical qN.WS ρ s := by
      obtain ⟨hs,hca,hco,ht,hu'⟩ := hGeom s hl hu
      exact hMem s hs hca hco ht hu'
    have hzAhead : o+m ≤ z := by omega
    have hStableα : stable α := by
      refine ⟨fun p hp => (hCVar _ (candidate_rank_regs _ (cutRankArg_in hp))).trans (hStableρ.regs p hp),?_⟩
      exact (hFrozen (z+1) (by omega) (le_refl _)).trans hStableρ.one
    let x := cutIndexedForm D FP (d := d) (n := n) σ j v
    have hX (u : Coord (d+1) n) : val FP canonical qN.WS α (o+(inputCoordOrder n (d+1) u).val) = x u := by
      rw [hValues (inputCoordOrder n (d+1) u)]
      unfold x cutIndexedForm
      apply Finset.sum_congr rfl
      intro i _
      have hj := (inputCoordOrder n (d+1) u).isLt
      have hi := i.isLt
      have hc := hWρ.frame.layout.nullity
      have ha : i.val*m+(inputCoordOrder n (d+1) u).val < m*m := by
        have h := Nat.mul_le_mul_right m (show i.val+1 ≤ m from hi.trans_le hc)
        rw [Nat.succ_mul] at h
        omega
      let jj := (inputCoordOrder n (d+1) u).val
      have hbb : b+(i.val*m+jj) < z := by
        have hk : i.val*m+jj < m*m := ha
        omega
      have hbp : pivot ≤ b+(i.val*m+jj) := hb.trans (Nat.le_add_right _ _)
      exact congrArg (fun x => coefficients D c v i*x) (hBank _ hbb hbp)
    have hRBank : CutRankBank FP x o rb am dest z Sn B α :=
      ⟨hSlots,hStableα.regs,hX,
        (hFrozen z hzAhead (by omega)).trans hWρ.frame.zero_value,
        hStableα.one⟩
    obtain ⟨β,hRank,hRB,hDL,hBool,hTest,hFrame,hRVars,hRIn,hROut⟩ :=
      cutRankSweepPreservingCount_run D FP x hd hn (le_refl _) hRword layout.layout
        (layout.scratch_below.trans (Nat.le_add_right _ _)) layout.source_before_rows
        layout.rows_before_augmented hRBank (by rw [hDraw]; omega)
    have hAgree : β.vars cutRankAccept = 1 ↔ good v.val = true := by
      simpa only [good,cutRankCodeGood,dif_pos v.isLt] using hTest
    have hIdxβ : β.vars cutChoiceIndex = v.val :=
      (hRVars _ (by decide) (by decide)).trans hIdxα
    have hEval : (Expr.var cutChoiceIndex).evalB B β = some v.val :=
      evalB_var_iff.mpr ⟨hIdxβ.symm,hIdxβ ▸ v.isLt.trans hPow⟩
    let τ := {β with out := β.out ++ (if good v.val then [v.val] else [])}
    have hOne : 1 < B := by omega
    have e := evalB_condEq (evalB_var (σ := β) (x := cutRankAccept) (hBool.trans_lt hOne)) (evalB_lit hOne)
    have hEmit : Run B emitRankedCutCandidate β τ 10 := by
      by_cases hYes : β.vars cutRankAccept=1
      · have ee : (Cond.eq (.var cutRankAccept) (.lit 1)).evalB B β = some true := by simpa [hYes] using e
        have h := (Run.ite_true (d := .skip) ee (Run.write hEval)).mono (by decide : _ ≤ 10)
        simpa [emitRankedCutCandidate,τ,hAgree.mp hYes] using h
      · have ee : (Cond.eq (.var cutRankAccept) (.lit 1)).evalB B β = some false := by simpa [hYes] using e
        have h := (Run.ite_false (c := .write (.var cutChoiceIndex)) ee Run.skip).mono (by decide : _ ≤ 10)
        have hg : good v.val = false := Bool.eq_false_iff.mpr (fun he => hYes (hAgree.mpr he))
        simpa [emitRankedCutCandidate,τ,hg] using h
    have hFresh (r : String) (hC : CandidateFresh r) (hR : CutRankScalarFixed r)
        (hN : r ≠ cutRankSavedCount) : τ.vars r = ρ.vars r :=
      (hRVars r hR hN).trans (hCVar r hC)
    have hRead : (τ.arrs coefficientBank).length = (ρ.arrs coefficientBank).length := by
      change (β.arrs coefficientBank).length = _
      rw [cutRankSweepPreservingCount_arrays hRank _ (by decide) (by decide),hSize]
    have hSlotτ : Slots FP canonical qN.WS Sn B τ :=
      slots_frame FP hRB.slots rfl rfl (fun _ _ => rfl) rfl
    have hPacked : CutVisitInput (B := B) (Sn := Sn) FP τ a b o c m z (z+2) (z+3) := by
      refine ⟨⟨hSlotτ,hWρ.frame.layout,hCB,?_,?_,?_,?_,?_,?_,?_,?_,hRB.zero⟩,
        by simpa only [hRead] using hWρ.coefficient_bank,?_,?_,?_⟩
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.coeff_start
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.basis_start
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.form_start
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.side
      · exact hDL.trans hDraw
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.zero
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.scratch₁
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.frame.scratch₂
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.coefficient_count
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.load_base
      · exact (hFresh _ (by decide) (by decide) (by decide)).trans hWρ.load_count
    refine ⟨τ,?_,hPacked,⟨hRB.regs,hRB.one⟩,hIdxβ,hFresh _ (by decide) (by decide) (by decide),?_,hRIn.trans hIn,?_⟩
    · simpa only [rankedCutVisit,cost,Nat.add_assoc] using hRebuild.seq (hRank.seq hEmit)
    · intro s hs hp
      exact (hFrame s (hDoCut s hs hp)).trans
        (hFrozen s (hCut.trans hp) (Nat.le_trans (show s < z from hs).le (Nat.le_succ z)))
    · change β.out++_ = _
      rw [hROut,hOut]

#print axioms cappedRankedCutScan_run
end EvenTI.P12ComparePrep
