import EvenP12CompareNativeScan
import EvenP12CountPreAssembly
import EvenP12CountPostAssembly
import EvenP11LiveEnds

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.Headline EvenTI.P10Oracle
open EvenTI.P12Compare EvenTI.P12CountPre EvenTI.P10Scan
open Mathproof.EvenTI.GlobalCoverage Mathproof.EvenTI.P9Recognizer Mathproof.EvenTI.P9Root
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime (TuringPolytime)
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The exact original solver contract accepts native elimination bases.
The comparison and both counting endpoints are instantiated with the same plan. -/
noncomputable def solverOfNativeCutBanks (F : FieldEncoding K) (FP : FieldPresentation K)
    (banks : ∀ {a b n : Nat} (T : Tensor K (a+b) n), CompleteCutBanks T)
    (hSelf : SelfScanSound F FP)
    (hRecognize : TuringPolytime (recognizeWords F
      (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))))
    (hPrepare : TuringPolytime (comparePreBankZ F banks))
    (hAttempt : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    VerifiedSolver F := by
  let P := comparePlanFromBanks F banks FP
  let enum := (Fintype.equivFin Kˣ).symm
  have hCompare : TuringPolytime (compareWords F P) :=
    turingPolytime_compareBanks F banks FP hPrepare hAttempt
  have hPre : TuringPolytime (countPreZ F P enum) :=
    countPreZ_turingPolytime_checked F P enum hCompare
  have hPost : TuringPolytime (countPostZ F P enum) :=
    EvenTI.P12CountPost.countPostZ_turingPolytime_of_compare F P enum hCompare
  have hRecognize' : TuringPolytime (recognizeWords F (coverageAccept K)) :=
    recognizeWords_eq_of_guarded F (LiveSpectral.spectralExec_agrees F)
      (liveScalarExec_agrees F FP hSelf) ▸ hRecognize
  exact assembleVerifiedSolver F (coverageAccept K) P enum
    (fun T g => (coverageAccept_invariant_iff).mpr (fun S a => sourceAccepted_act S a) T g)
    contract_uniformCoverage contract_higherOrderRate
    (fun hd he hn T S hT => by
      have h := (sourceAccept_eq_true T).mp hT
      exact ⟨h.2.1,comparePlanFromBanks_complete F banks FP hd he hn T S h,h.2.2⟩)
    hRecognize' hCompare
    (fun g hg => countWords_turingPolytime_of_zeroDelimited F P enum hPre hPost g hg)

#print axioms solverOfNativeCutBanks
end EvenTI.P12ComparePrep
