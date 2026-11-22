import EvenP15ControllerRoot
import EvenP15RecoverPairCRT
import EvenP15TrialAssembly

set_option autoImplicit false

namespace EvenTI.P15Execution

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.CellPreparation
open EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Scalar EvenTI.P15Trial EvenTI.P15Recover
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPPartialCompiler20261001 (RamPolytimeOn)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Attach the checked CRT recovery semantics and the checked serializer to
physical runners for the raw side frames, scalar calls, and CRT calls. -/
theorem verifiedSolver_of_crtSideControllers (D : FieldEncoding K) (F : FieldPresentation K)
    (sides : SideTrials K) (hSide : ExactRawTrialPairs D (sideProduct sides))
    (frame : TuringPolytime (sideFrameWords D sides))
    (scalar : RamPolytimeOn (SpectralSelfCall D (sideProduct sides))
      (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (recover : RamPolytimeOn (RecoveryCall D (sideProduct sides))
      (preparedAttemptWords D (recoveringPairAttemptCRT D F))) : Nonempty (VerifiedSolver D) :=
  verifiedSolver_of_liveControllers D F
    { pairs := sideProduct sides
      exactPairs := hSide
      pre := comparePrePairsZ_time_of_sideFrame D sides frame
      scalar := scalar
      attempt := recoveringPairAttemptCRT D F
      attemptSpec := recoveringPairAttemptCRT_refines D F
      recover := recover }

#print axioms verifiedSolver_of_crtSideControllers
end EvenTI.P15Execution