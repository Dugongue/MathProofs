import EvenP12ComparePrepTrialProvider
import EvenP12ScalarSpectralDriver
import EvenP13SpectralAnchorAgree

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P14Preparation

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Scalar
open EvenTI.P13Spectral EvenTI.Headline EvenTI.P12Guard
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem provided_requests_mem (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (exactPairs : ExactRawTrialPairs D pairs) (w x : List Nat) :
    x ∈ preparedPairRequests D pairs (selfPairWords w) ↔
      x ∈ selfRequests D (prepareTrials D) w := by
  unfold preparedPairRequests selfRequests
  cases hp : decodePair D (selfPairWords w) with
  | none => simp only [hp,List.not_mem_nil]
  | some p =>
    have h := decodePair_balanced hp
    simp only [hp,dif_pos h,List.mem_map]
    exact exists_congr fun b => and_congr (exactPairs h p.source p.target b) Iff.rfl

noncomputable def providedScalarWords (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (w : List Nat) : List Nat :=
  if (preparedPairRequests D pairs (selfPairWords w)).all
      (fun x => decide (preparedSelfWords D F (Fintype.equivFin Kˣ).symm x = [1]))
  then [1] else [0]

theorem providedScalarWords_time (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (pre : TuringPolytime (comparePrePairsZ D pairs))
    (attempt : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm)) :
    TuringPolytime (providedScalarWords D F pairs) := by
  have h := turingPolytime_comp selfPairWords_turingPolytime pre
  have hPack : TuringPolytime (fun w =>
      packSegments ([] :: preparedPairRequests D pairs (selfPairWords w))) := by
    convert h using 1
    funext w
    exact (comparePrePairsZ_pack D pairs (selfPairWords w)).symm
  exact packedTrialsAll_time hPack attempt (preparedSelfWords_bit D F _)

theorem providedScalarWords_exact (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (exactPairs : ExactRawTrialPairs D pairs)
    (w : List Nat) (hw : recognizeWords D (LiveSpectral.spectralExec D) w = [1]) :
    providedScalarWords D F pairs w = recognizeWords D (liveScalarExec D F) w := by
  have hb : ((preparedPairRequests D pairs (selfPairWords w)).all
      (fun x => decide (preparedSelfWords D F (Fintype.equivFin Kˣ).symm x = [1]))) =
      selfChecksBit D F (Fintype.equivFin Kˣ).symm (prepareTrials D) w := by
    unfold selfChecksBit
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,provided_requests_mem D pairs exactPairs w]
  have ha := scalarDriver_agrees_on_spectral D F (prepareTrials D) (fun _ => [1])
    (fun _ _ => Iff.rfl) (fun w h => (retainedGateWords_on_spectral D w h).symm) w hw
  simp only [providedScalarWords,hb]
  by_cases ht : selfChecksBit D F (Fintype.equivFin Kˣ).symm (prepareTrials D) w = true
  · simpa [scalarDriver,gateConj,ht] using ha
  · simpa [scalarDriver,gateConj,ht] using ha

/-- Physical cut-bank order flows through the same serialized plan into
spectral recognition, the scalar check, comparison and both count phases. -/
noncomputable def solverOfAutomaticCutTrialCalls (D : FieldEncoding K) (F : FieldPresentation K)
    (proj : TuringPolytime spectralPairRequest)
    (pre : TuringPolytime (comparePrePairsZ D (automaticCutTrialProvider D F)))
    (scalar : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (recover : TuringPolytime (preparedAttemptWords D (CellPreparation.recoveringPairAttempt D F))) :
    VerifiedSolver D := by
  let pairs : BalancedTrialPairs K := automaticCutTrialProvider D F
  have hExact : ExactRawTrialPairs D pairs := automaticCutTrialProvider_exact D F
  have hScore := spectralPairAnswer_time_of_route (Fintype.card K) (anchorWordResult D)
    Fintype.one_lt_card (anchorWordResult_turingPolytime D F) proj
  have hSpectral := recognizeSpectral_time_of_comparePre D pairs hExact (anchorWordResult D)
    (anchorWordResult_on_numbered D) pre hScore
  have hScalar := providedScalarWords_time D F pairs pre scalar
  have hRec := liveRecognize_time_of_guarded D F hSpectral hScalar
    (providedScalarWords_exact D F pairs hExact)
  exact solverOfProvidedPairs D F pairs (automaticCutTrialProvider_covers D F)
    (selfScanSound D F) hRec pre recover

#print axioms providedScalarWords_time
#print axioms solverOfAutomaticCutTrialCalls
end EvenTI.P14Preparation
