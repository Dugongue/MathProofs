import EvenP11LiveMachines
import EvenP12RecognizeAssembly
import EvenP12CompareAssembly
import EvenP12CountPreRoute
import EvenP12CountPostNormalize

set_option autoImplicit false

namespace EvenTI.Headline

open EvenTI.Contract
open EvenTI.P10Oracle EvenTI.P10Scan
open Mathproof.EvenTI.P9Recognizer
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime (TuringPolytime)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The concrete routines whose complete binary costs are required by the
checked runtime assembly. Each field states the cost of its exact word code. -/
structure RuntimePorts (F : FieldEncoding K) (FP : FieldPresentation K) where
  spectral : TuringPolytime (recognizeWords F (LiveSpectral.spectralExec F))
  scalar : TuringPolytime (recognizeWords F (liveScalarExec F FP))
  prepare : TuringPolytime (P12Compare.comparePreZ F)
  attempt : TuringPolytime
    (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))
  emit : TuringPolytime (P12CountPre.emitQueries F (Fintype.equivFin Kˣ).symm)
  normalize : TuringPolytime (fun w =>
    P12CountPost.postNormalize (Fintype.equivFin Kˣ).symm w
      (compareWords F (recoveringPlan F FP) (P12CountPost.postZSource w)))

/-- Wire the checked binary compilation stages into the original four fields. -/
def liveMachinesOfRuntimePorts (F : FieldEncoding K) (FP : FieldPresentation K)
    (ports : RuntimePorts F FP) : LiveMachines F FP := by
  have hCompare := P12Compare.turingPolytime_liveCompare_of_calls F FP ports.prepare ports.attempt
  exact {
    recognize := P12Guard.liveRecognize_time_of_gateTimes F FP ports.spectral ports.scalar
    compare := hCompare
    countPre := P12CountPre.countPreZ_turingPolytime_of_emitQueries F
      (Fintype.equivFin Kˣ).symm (recoveringPlan F FP) hCompare ports.emit
    countPost := P12CountPost.countPostZ_turingPolytime_of_normalize F
      (recoveringPlan F FP) (Fintype.equivFin Kˣ).symm ports.normalize
  }

theorem fixedFieldEvenOrderTI_of_runtime_ports
    (h : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (F : FieldEncoding K),
      ∃ FP : FieldPresentation K, Nonempty (RuntimePorts F FP)) : FixedFieldEvenOrderTI := by
  apply fixedFieldEvenOrderTI_of_live_machines
  intro K _ _ _ F
  obtain ⟨FP, ⟨ports⟩⟩ := h K F
  exact ⟨FP, ⟨liveMachinesOfRuntimePorts F FP ports⟩⟩

#print axioms liveMachinesOfRuntimePorts
#print axioms fixedFieldEvenOrderTI_of_runtime_ports

end EvenTI.Headline
