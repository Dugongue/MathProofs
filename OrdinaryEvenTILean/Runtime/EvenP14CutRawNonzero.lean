import EvenP14CutRawSetup
import EvenP14CutScan

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawNonzeroCutProgram (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j) (cappedNonzeroCutScan D F j)

theorem cappedCutChoiceCount_le (q c budget : ℕ) : cappedCutChoiceCount q c budget ≤ budget := by
  unfold cappedCutChoiceCount
  split <;> omega

/-- One cap-admitted cut in the order-four comparison. Starting with the
original encoded pair, the program computes the actual four kernels,
initializes its selected coefficient bank, and outputs exact accepted codes. -/
theorem rawNonzeroCutProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n : ℕ} (T S : Tensor K (2+2) n) (j : Fin 4) (hn : 2 ≤ n) :
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (cutWordPoly F).eval L
    let m := n^2
    let Sn := pairCutSlotCount.value m
    let z := constantsBase.value m
    let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
    let count := cappedCutChoiceCount (Fintype.card K) c n
    let C := rawCutSetupBitCost F L j + (30*(m+Fintype.card K)+42 + ((visitCutCandidateCost F c m+8)*count+6))
    ∃ τ, Run B (rawNonzeroCutProgram D F j) (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L))
        (w.length::w)) τ C ∧
      CutVisitInput (B := B) (Sn := Sn) F τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      (∃ xs : Fin c → Coord 2 n → K, LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = selectedKernel (leftOf j) (if targetOf j then S else T) ∧
        ∀ i x, val F canonical qN.WS τ ((outputBase j).value m+(i.val*m+(inputCoordOrder n 2 x).val))=xs i x) ∧
      τ.inp=[] ∧ τ.out=(List.range count).filter (cutCodeGood (Fintype.card K) c (D 0).val) := by
  dsimp only
  obtain ⟨ρ,hρ,hW,hCuts,hLive,hBudget,_,_,hi,ho,_,hCap⟩ :=
    rawCutSetupProgram_run D F T S j (by decide : 2 ≤ 2) hn
  have hN := (cutInput_side_bounds D T S (by decide : 1 ≤ 2) hn).1
  obtain ⟨τ,hτ,hW',hKeep,hi',ho'⟩ := cappedNonzeroCutScan_run D F j hW hLive hBudget hN hCap
  refine ⟨τ,hρ.seq hτ,hW',?_,hi'.trans hi,by simpa only [ho,List.nil_append] using ho'⟩
  have hBasis := (hCuts j).basis
  rw [hLive] at hBasis
  obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
  refine ⟨xs,hInd,hSpan,?_⟩
  intro i x
  let m := n^2
  let b := (outputBase j).value m
  let s := b+(i.val*m+(inputCoordOrder n 2 x).val)
  have hP : i.val*m+(inputCoordOrder n 2 x).val < m*m :=
    outputPoint_lt hW.frame.layout.nullity i (inputCoordOrder n 2 x)
  have hTop : b+m*m ≤ constantsBase.value m := outputBank_point_upper m j
  have hs : s<constantsBase.value m := (Nat.add_lt_add_left hP b).trans_le hTop
  have hb : placedRankSource m+m ≤ b := hW.frame.layout.output_before
  exact (hKeep s hs (hb.trans (Nat.le_add_right _ _))).trans (hAt i x)

#print axioms rawNonzeroCutProgram_run
end EvenTI.P12ComparePrep
