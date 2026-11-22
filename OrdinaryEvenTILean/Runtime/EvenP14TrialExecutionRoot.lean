import EvenP14CutProviderAssembly
import EvenP14ProjectionEngine

set_option autoImplicit false

namespace EvenTI.P14Preparation

open EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Scalar
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Supply the checked binary projection, input-sized cut banks and exact trial
provider. Only execution of trial production and its two consuming callbacks
is required from the caller. -/
noncomputable def solverOfTrialExecution (D : FieldEncoding K) (F : FieldPresentation K)
    (pre : TuringPolytime (comparePrePairsZ D (automaticCutTrialProvider D F)))
    (scalar : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (recover : TuringPolytime (preparedAttemptWords D (CellPreparation.recoveringPairAttempt D F))) :
    VerifiedSolver D :=
  solverOfAutomaticCutTrialCalls D F EvenTI.P14Projection.spectralPairRequest_turingPolytime pre scalar recover

#print axioms solverOfTrialExecution
end EvenTI.P14Preparation
