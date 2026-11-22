import EvenP12ComparePrepSpectral
import EvenP12ComparePrepNativeRoot
import EvenP12ScalarSpectralDriver
import EvenP9FullScannerSound

set_option autoImplicit false

namespace EvenTI.Headline

open EvenTI.Action EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.P10Scan
open EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.P12Scalar
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The comparison, spectral recognizer, scalar recognizer and both counting
endpoints share one exact serialized producer of native cut trials. -/
noncomputable def solverOfSharedTrialRuntime (F : FieldEncoding K) (FP : FieldPresentation K)
    (banks : ∀ {a b n : Nat} (T : Tensor K (a+b) n), CompleteCutBanks T)
    (anchor : List Nat → List Nat)
    (hAnchor : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A])
    (hAnchorTime : TuringPolytime anchor)
    (hProjection : TuringPolytime spectralPairRequest)
    (hPrepare : TuringPolytime (comparePreBankZ F banks))
    (hScalar : TuringPolytime (preparedSelfWords F FP (Fintype.equivFin Kˣ).symm))
    (hRecover : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    VerifiedSolver F := by
  have hCard : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hScore := spectralPairAnswer_time_of_route (Fintype.card K) anchor hCard hAnchorTime hProjection
  have hPairs : TuringPolytime (comparePrePairsZ F (nativeBalancedTrialPairs F banks)) := by
    rw [nativeBalancedTrialPairs_pre]
    exact hPrepare
  have hSpectral := recognizeSpectral_time_of_comparePre F (nativeBalancedTrialPairs F banks)
    (nativeBalancedTrialPairs_exact F banks) anchor hAnchor hPairs hScore
  have hRecognize := liveRecognize_of_native_scalar_spectral F FP banks hSpectral hPrepare hScalar
  exact solverOfNativeCutBanks F FP banks (selfScanSound F FP) hRecognize hPrepare hRecover

#print axioms solverOfSharedTrialRuntime
end EvenTI.Headline
