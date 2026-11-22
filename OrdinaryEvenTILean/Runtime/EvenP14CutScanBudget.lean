import EvenP14CutScan
import EvenP14CutRankControl

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P12ComparePrep

open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.P15RecogIMPDot20261007 (dotCost dotStep)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open EvenTI.P12Compare
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem countCutCodes_le (q c budget : ℕ) : cappedCutChoiceCount q c budget ≤ budget := by
  unfold cappedCutChoiceCount
  split <;> omega

theorem cutCandidateCost_mono (F : FieldPresentation K) {c m L : ℕ}
    (hc : c ≤ L) (hm : m ≤ L) : cutCandidateCost F c m ≤ cutCandidateCost F L L := by
  simp only [cutCandidateCost,loadCutCoefficientsCost,encodedBankLoadCost,cutRecombineCost,cutDotCost,dotCost]
  gcongr

private noncomputable def cutCandidatePoly (F : FieldPresentation K) : Polynomial ℕ :=
  let M := fieldMacros F
  C 34 * X + C 8 +
    (C (encodedBankLoadStepCost F (.var loadIndex)+4)*X+C 6) +
  ((C 4 + C (15+3+M.costPoint) + C 2 +
    (C (1+3+dotStep M cutCoeffAddress cutBasisAddress)*X+C 1+C 3)) + C 8)*X+C 6

private theorem cutCandidatePoly_eval (F : FieldPresentation K) (L : ℕ) :
    (cutCandidatePoly F).eval L = cutCandidateCost F L L := by
  simp only [cutCandidatePoly,cutCandidateCost,loadCutCoefficientsCost,encodedBankLoadCost,
    cutRecombineCost,cutDotCost,dotCost,eval_add,eval_mul,eval_C,eval_X,Nat.add_assoc]

private noncomputable def cutRankPassPoly (F : FieldPresentation K) : Polynomial ℕ :=
  C 8 + (C (300*macroBudget F)*(X+C 2)^4+C (34500*macroBudget F)*(C 6*X)^5)

private theorem cutRankPassPoly_eval (F : FieldPresentation K) (L : ℕ) :
    (cutRankPassPoly F).eval L = cutRankModeCost F L := by
  simp [cutRankPassPoly,cutRankModeCost,Nat.mul_assoc]

theorem cutRankModeCost_mono (F : FieldPresentation K) {m L : ℕ} (h : m ≤ L) :
    cutRankModeCost F m ≤ cutRankModeCost F L := by
  unfold cutRankModeCost
  gcongr

noncomputable def cutNonzeroPaidPoly (F : FieldPresentation K) (q : ℕ) : Polynomial ℕ :=
  C 30*(X+C q)+C 42+((cutCandidatePoly F + (C 24*X+C 8+C 10)+C 8)*X+C 6)

noncomputable def cutRankedPaidPoly (F : FieldPresentation K) (q : ℕ) : Polynomial ℕ :=
  C 30*(X+C q)+C 42+
    ((cutCandidatePoly F + ((cutRankPassPoly F + C 24)*X+C 14+C 10)+C 8)*X+C 6)

theorem nonzeroCutScanCost_le (F : FieldPresentation K) {c m n L : ℕ}
    (hc : c ≤ L) (hm : m ≤ L) (hn : n ≤ L) :
    30*(m+Fintype.card K)+42+
      ((visitCutCandidateCost F c m+8)*cappedCutChoiceCount (Fintype.card K) c n+6)
    ≤ (cutNonzeroPaidPoly F (Fintype.card K)).eval L := by
  have hN := (countCutCodes_le (Fintype.card K) c n).trans hn
  have hC := cutCandidateCost_mono F hc hm
  simp only [cutNonzeroPaidPoly,eval_add,eval_mul,eval_C,eval_X,cutCandidatePoly_eval,visitCutCandidateCost]
  gcongr

theorem rankedCutScanCost_le (F : FieldPresentation K) {a c m n L : ℕ}
    (ha : a ≤ L) (hc : c ≤ L) (hm : m ≤ L) (hn : n ≤ L) :
    30*(m+Fintype.card K)+42+
      ((cutCandidateCost F c m + ((cutRankModeCost F m+24)*a+14+10)+8)*
        cappedCutChoiceCount (Fintype.card K) c n+6)
    ≤ (cutRankedPaidPoly F (Fintype.card K)).eval L := by
  have hN := (countCutCodes_le (Fintype.card K) c n).trans hn
  have hC := cutCandidateCost_mono F hc hm
  have hRank := cutRankModeCost_mono F hm
  simp only [cutRankedPaidPoly,eval_add,eval_mul,eval_C,eval_X,cutCandidatePoly_eval,cutRankPassPoly_eval]
  gcongr

#print axioms nonzeroCutScanCost_le
#print axioms rankedCutScanCost_le
end EvenTI.P12ComparePrep
