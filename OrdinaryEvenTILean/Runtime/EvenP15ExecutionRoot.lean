import EvenP14TrialExecutionRoot
import Mathproof.Meta.Problem18FieldPresentation20260930

set_option autoImplicit false

namespace EvenTI.P15Execution

open EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Scalar
open EvenTI.P13Spectral EvenTI.P14Preparation EvenTI.Headline EvenTI.P12Guard
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18FieldPresentation20260930 (exists_fieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The producer can use any physical trial order with the exact reference
membership relation. Recognition, comparison and both count phases share it. -/
noncomputable def solverOfExactTrialOrder (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (hExact : ExactRawTrialPairs D pairs)
    (pre : TuringPolytime (comparePrePairsZ D pairs))
    (scalar : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (recover : TuringPolytime (preparedAttemptWords D (CellPreparation.recoveringPairAttempt D F))) :
    VerifiedSolver D := by
  have hScore := spectralPairAnswer_time_of_route (Fintype.card K) (anchorWordResult D)
    Fintype.one_lt_card (anchorWordResult_turingPolytime D F) EvenTI.P14Projection.spectralPairRequest_turingPolytime
  have hSpectral := recognizeSpectral_time_of_comparePre D pairs hExact (anchorWordResult D)
    (anchorWordResult_on_numbered D) pre hScore
  have hScalar := providedScalarWords_time D F pairs pre scalar
  have hRec := liveRecognize_time_of_guarded D F hSpectral hScalar
    (providedScalarWords_exact D F pairs hExact)
  exact solverOfProvidedPairs D F pairs (fun h T S b hb => (hExact h T S b).mpr hb)
    (selfScanSound D F) hRec pre recover

/-- A machine-level certificate for the three shared callbacks, with no
prescribed ordering of physically generated equivalent candidates. -/
structure ExactTrialExecutions (D : FieldEncoding K) (F : FieldPresentation K) where
  pairs : BalancedTrialPairs K
  exactPairs : ExactRawTrialPairs D pairs
  pre : TuringPolytime (comparePrePairsZ D pairs)
  scalar : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm)
  recover : TuringPolytime (preparedAttemptWords D (CellPreparation.recoveringPairAttempt D F))

theorem fixedFieldEvenOrderTI_of_exactTrialExecutions
    (h : ∀ (L : Type) [Field L] [Fintype L] [DecidableEq L] (D : FieldEncoding L)
      (F : FieldPresentation L), Nonempty (ExactTrialExecutions D F)) :
    FixedFieldEvenOrderTI := by
  intro L _ _ D
  classical
  obtain ⟨F⟩ := exists_fieldPresentation (K := L)
  obtain ⟨e⟩ := h L D F
  exact ⟨solverOfExactTrialOrder D F e.pairs e.exactPairs e.pre e.scalar e.recover⟩

#print axioms solverOfExactTrialOrder
#print axioms fixedFieldEvenOrderTI_of_exactTrialExecutions
end EvenTI.P15Execution