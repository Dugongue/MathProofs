import EvenP14CutScanBudget
import EvenP14CutRawNonzero

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def oneCutBitPoly (F : FieldPresentation K) : Polynomial ℕ :=
  C (78+installEncodedDigitCost F)*X+
  C (34500*macroBudget F)*(C 4*X+C 2)^5+C (4096+installEncodedDigitCost F)

theorem oneCutBitPoly_eval (F : FieldPresentation K) (L : ℕ) :
    (oneCutBitPoly F).eval L = oneCutCostBound F L := by
  simp [oneCutBitPoly,oneCutCostBound,Nat.add_assoc,Nat.mul_assoc]

noncomputable def rawSetupBitPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  C 40*(X+C 1)+C (3*F.e+26)+C 4*oneCutBitPoly F+C (cutSetupCost j)

theorem rawSetupBitPoly_eval (F : FieldPresentation K) (j : Fin 4) (L : ℕ) :
    (rawSetupBitPoly F j).eval L=rawCutSetupBitCost F L j := by
  simp [rawSetupBitPoly,rawCutSetupBitCost,oneCutBitPoly_eval,Nat.add_assoc]

noncomputable def rawNonzeroBitPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawSetupBitPoly F j+cutNonzeroPaidPoly F (Fintype.card K)

theorem rawNonzeroCutBit_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n : ℕ} (T S : Tensor K (2+2) n) (j : Fin 4) (hn : 2 ≤ n) :
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (cutWordPoly F).eval L
    let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
    let count := cappedCutChoiceCount (Fintype.card K) c n
    ∃ τ, Run B (rawNonzeroCutProgram D F j)
        (initEnv (comparisonInitExt F (pairCutSlotCount.value (n^2)) w.length (cutChoiceExt L))
          (w.length::w)) τ ((rawNonzeroBitPoly F j).eval L) ∧
      τ.out=(List.range count).filter (cutCodeGood (Fintype.card K) c (D 0).val) := by
  dsimp only
  obtain ⟨τ,hR,hW,_,_,hOut⟩ := rawNonzeroCutProgram_run D F T S j hn
  obtain ⟨hN,hM,_⟩ := cutInput_side_bounds D T S (by decide : 1≤2) hn
  refine ⟨τ,hR.mono ?_,hOut⟩
  simp only [rawNonzeroBitPoly,eval_add,rawSetupBitPoly_eval]
  exact Nat.add_le_add_left
    (nonzeroCutScanCost_le F (hW.frame.layout.nullity.trans hM) hM (hN.trans hM)) _

#print axioms rawNonzeroCutBit_run
end EvenTI.P12ComparePrep
