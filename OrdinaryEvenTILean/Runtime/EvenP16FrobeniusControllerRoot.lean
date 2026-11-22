import EvenP15CRTControllerRoot
import EvenP16RecoverFrobeniusAttempt

set_option autoImplicit false

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation EvenTI.P15Execution EvenTI.P15Trial EvenTI.P16Recover
open EvenTI.P12Scalar EvenTI.P12ComparePrep EvenTI.P10Scan EvenTI.P15Recover
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPPartialCompiler20261001 (RamPolytimeOn)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The verified root accepts the linearized-Frobenius recovery implementation.
Its physical runtime obligation is the exact new attempt, including its
choice of a root from the kernel and its original output encoding. -/
theorem verifiedSolver_of_frobeniusSideControllers (D : FieldEncoding K) (F : FieldPresentation K)
    (sides : SideTrials K) (hSide : ExactRawTrialPairs D (sideProduct sides))
    (frame : TuringPolytime (sideFrameWords D sides))
    (scalar : RamPolytimeOn (SpectralSelfCall D (sideProduct sides))
      (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (recover : RamPolytimeOn (RecoveryCall D (sideProduct sides))
      (preparedAttemptWords D (recoveringPairAttemptFrobenius D F))) :
    Nonempty (VerifiedSolver D) :=
  verifiedSolver_of_liveControllers D F
    { pairs := sideProduct sides
      exactPairs := hSide
      pre := comparePrePairsZ_time_of_sideFrame D sides frame
      scalar := scalar
      attempt := recoveringPairAttemptFrobenius D F
      attemptSpec := recoveringPairAttemptFrobenius_refines D F
      recover := recover }

#print axioms verifiedSolver_of_frobeniusSideControllers
end EvenTI.P16Execution
