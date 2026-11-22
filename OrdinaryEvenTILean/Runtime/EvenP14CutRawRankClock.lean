import EvenP14CutRawClock
import EvenP14CutRawRank

set_option autoImplicit false
set_option maxHeartbeats 1650000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawRankedBitPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawSetupBitPoly F j+(C (cutRankInitCost F)+cutRankedPaidPoly F (Fintype.card K))

theorem rawRankedCutBit_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (cutWordPoly F).eval L
    let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
    let count := cappedCutChoiceCount (Fintype.card K) c n
    ∃ τ, Run B (rawRankedCutProgram D F j)
      (initEnv (comparisonInitExt F (pairCutSlotCount.value (n^(d+1))) w.length (cutChoiceExt L))
        (w.length::w)) τ ((rawRankedBitPoly F j).eval L) ∧
      τ.out=(List.range count).filter (cutRankCodeGood D F d n c τ j) := by
  dsimp only
  obtain ⟨τ,hR,hW,_,_,hOut⟩ := rawRankedCutProgram_run D F T S j hd hn
  obtain ⟨hN,hM,hD⟩ := cutInput_side_bounds D T S (by omega : 1 ≤ d+1) hn
  refine ⟨τ,hR.mono ?_,hOut⟩
  simp only [rawRankedBitPoly,eval_add,eval_C,rawSetupBitPoly_eval]
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (rankedCutScanCost_le F hD (hW.frame.layout.nullity.trans hM) hM (hN.trans hM)) _) _

#print axioms rawRankedCutBit_run
end EvenTI.P12ComparePrep
