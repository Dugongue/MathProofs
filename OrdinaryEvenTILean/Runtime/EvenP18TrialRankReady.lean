import EvenP17TrialFormVisit
import EvenP14CutScanRank

set_option autoImplicit false
set_option maxHeartbeats 2900000
set_option maxRecDepth 12000

namespace EvenTI.P18Trial

open EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.LiveSpectral
open EvenTI.P15Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dI dO dL dZ dT dU)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem cutRankArg_in {d n src R A O Z e : ℕ} {p : String × ℕ}
    (h : p ∈ cutRankArgs d n src R A O Z e) : p.1 ∈ cutRankArgNames := by
  change p.1 ∈ (cutRankArgs d n src R A O Z e).map Prod.fst
  exact List.mem_map.mpr ⟨p,h,rfl⟩

abbrev IndexedFormFresh (r : String) : Prop :=
  r ∉ regNames canonical ∧ ¬loadChanges r ∧ r ≠ coeffIndex ∧ r ≠ coeffPower ∧ r ≠ coeffNumber ∧
    r ≠ dI ∧ r ≠ dO ∧ r ≠ cutEntry

private theorem candidate_rank_regs : ∀ r ∈ cutRankArgNames, IndexedFormFresh r := by decide

noncomputable def rankReadyVisit (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (cutCandidateProgram D F) cutRankSweepPreservingCount

noncomputable def rankReadyVisitCost (F : FieldPresentation K) (d m c : ℕ) : ℕ :=
  cutCandidateCost F c m+((cutRankModeCost F m+24)*(d+1)+14)

abbrev RankedRegisterFixed (r : String) : Prop :=
  IndexedFormFresh r ∧ CutRankScalarFixed r ∧ r ≠ cutRankSavedCount

/-- Restore the indexed cut scan state after deciding the current
retained-rank predicate, with the full reconstructed form still live.
This exposes the accepted branch to any independently checked renderer. -/
theorem rankReadyVisit_run (D : FieldEncoding K) (FP : FieldPresentation K)
    {B d n c : ℕ} {σ : Env} (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1)) + n^(d+1) + n^(d+1) + 10 < B)
    (hStable : CutRankStable (d := d) (n := n) FP σ)
    (hW : let m := n^(d+1); let z := constantsBase.value m
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) FP σ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3))
    (v : Fin (Fintype.card K^c)) (hIdx : σ.vars cutChoiceIndex=v.val)
    (hQ : Fintype.card K < B) (hPow : Fintype.card K^c < B) :
    let m := n^(d+1)
    let z := constantsBase.value m
    let x := cutIndexedForm D FP (d := d) (n := n) σ j v
    ∃ τ, Run B (rankReadyVisit D FP) σ τ (rankReadyVisitCost FP d m c) ∧
      CutVisitInput (B := B) (Sn := pairCutSlotCount.value m) FP τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      CutRankStable (d := d) (n := n) FP τ ∧
      (∀ u : Coord (d+1) n, val FP canonical qN.WS τ
        (placedRankSource m+(inputCoordOrder n (d+1) u).val) = x u) ∧
      τ.vars cutRankAccept ≤ 1 ∧ (τ.vars cutRankAccept=1 ↔ rawRetainedFullRank x=true) ∧
      (∀ s < z, firstOutputBase.value m ≤ s →
        val FP canonical qN.WS τ s = val FP canonical qN.WS σ s) ∧
      (∀ r, RankedRegisterFixed r → τ.vars r=σ.vars r) ∧
      τ.inp=σ.inp ∧ τ.out=σ.out := by
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
  have layout := placedRankFits_of_cut hd hn hB
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
  change CutVisitInput (B := B) (Sn := Sn) FP σ a b o c m z (z+2) (z+3) at hW
  have hFR : a+c ≤ o := hW.frame.layout.coefficient_before
  have hCB : c+1 < B := hW.frame.count_word
  have hGeom (s : ℕ) (hl : o+m ≤ s) (hu : s ≤ z+1) :
      s < Sn ∧ (s < a ∨ a+c ≤ s) ∧ (s < o ∨ o+m ≤ s) ∧ s ≠ z+2 ∧ s ≠ z+3 :=
    ⟨by omega,Or.inr (by omega),Or.inr hl,by omega,by omega⟩
  obtain ⟨α,hRebuild,hSlots,hValues,_,hSize,hMem,hVars,hIn,hOut⟩ :=
    cutCandidateProgram_run D FP v hW.frame hQ hPow hW.coefficient_bank hIdx
      hW.coefficient_count hW.load_base hW.load_count
  have hCVar (r : String) (hr : IndexedFormFresh r) : α.vars r = σ.vars r :=
    hVars r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1
      hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2
  have hDraw : α.vars dL = c :=
    (hCVar dL (by decide)).trans hW.frame.count
  have hFrozen (s : ℕ) (hl : o+m ≤ s) (hu : s ≤ z+1) :
      val FP canonical qN.WS α s = val FP canonical qN.WS σ s := by
    obtain ⟨hs,hca,hco,ht,hu'⟩ := hGeom s hl hu
    exact hMem s hs hca hco ht hu'
  have hzAhead : o+m ≤ z := by omega
  have hStableα : CutRankStable (d := d) (n := n) FP α := by
    refine ⟨fun p hp => (hCVar _ (candidate_rank_regs _ (cutRankArg_in hp))).trans (hStable.regs p hp),?_⟩
    exact (hFrozen (z+1) (by omega) (le_refl _)).trans hStable.one
  let x := cutIndexedForm D FP (d := d) (n := n) σ j v
  have hX (u : Coord (d+1) n) : val FP canonical qN.WS α (o+(inputCoordOrder n (d+1) u).val) = x u :=
    hValues (inputCoordOrder n (d+1) u)
  have hRBank : CutRankBank FP x o rb am dest z Sn B α :=
    ⟨hSlots,hStableα.regs,hX,
      (hFrozen z hzAhead (by omega)).trans hW.frame.zero_value,
      hStableα.one⟩
  obtain ⟨τ,hRank,hRB,hDL,hBool,hTest,hFrame,hRVars,hRIn,hROut⟩ :=
    cutRankSweepPreservingCount_run D FP x hd hn (le_refl _) hRword layout.layout
      (layout.scratch_below.trans (Nat.le_add_right _ _)) layout.source_before_rows
      layout.rows_before_augmented hRBank (by rw [hDraw]; omega)
  have hFresh (r : String) (hr : RankedRegisterFixed r) : τ.vars r = σ.vars r :=
    (hRVars r hr.2.1 hr.2.2).trans (hCVar r hr.1)
  have hRead : (τ.arrs coefficientBank).length = (σ.arrs coefficientBank).length := by
    rw [cutRankSweepPreservingCount_arrays hRank _ (by decide) (by decide),hSize]
  have hPacked : CutVisitInput (B := B) (Sn := Sn) FP τ a b o c m z (z+2) (z+3) := by
    refine ⟨⟨hRB.slots,hW.frame.layout,hCB,?_,?_,?_,?_,?_,?_,?_,?_,hRB.zero⟩,
      by simpa only [hRead] using hW.coefficient_bank,?_,?_,?_⟩
    · exact (hFresh _ (by decide)).trans hW.frame.coeff_start
    · exact (hFresh _ (by decide)).trans hW.frame.basis_start
    · exact (hFresh _ (by decide)).trans hW.frame.form_start
    · exact (hFresh _ (by decide)).trans hW.frame.side
    · exact hDL.trans hDraw
    · exact (hFresh _ (by decide)).trans hW.frame.zero
    · exact (hFresh _ (by decide)).trans hW.frame.scratch₁
    · exact (hFresh _ (by decide)).trans hW.frame.scratch₂
    · exact (hFresh _ (by decide)).trans hW.coefficient_count
    · exact (hFresh _ (by decide)).trans hW.load_base
    · exact (hFresh _ (by decide)).trans hW.load_count
  refine ⟨τ,hRebuild.seq hRank,hPacked,⟨hRB.regs,hRB.one⟩,hRB.source,hBool,hTest,?_,hFresh,
    hRIn.trans hIn,hROut.trans hOut⟩
  intro s hs hp
  exact (hFrame s (hDoCut s hs hp)).trans
    (hFrozen s (hCut.trans hp) (Nat.le_trans (show s < z from hs).le (Nat.le_succ z)))

#print axioms rankReadyVisit_run
end EvenTI.P18Trial
