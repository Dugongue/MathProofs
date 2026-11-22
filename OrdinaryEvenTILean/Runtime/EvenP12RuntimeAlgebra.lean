import EvenP12RuntimePorts
import EvenP12CountPreAssembly
import EvenP12CountPostAssembly

set_option autoImplicit false

namespace EvenTI.Headline

open EvenTI.Contract EvenTI.P10Oracle EvenTI.P10Scan
open Mathproof.EvenTI.P9Recognizer
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime (TuringPolytime)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Supply the two counting fields by running their audited tape drivers
with the same concrete comparison machine as the comparison field. -/
def liveMachines_of_algebra_runtime (F : FieldEncoding K) (FP : FieldPresentation K)
    (recognize : TuringPolytime (recognizeWords F
      (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))))
    (prepare : TuringPolytime (P12Compare.comparePreZ F))
    (attempt : TuringPolytime
      (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    LiveMachines F FP := by
  have hcmp := P12Compare.turingPolytime_liveCompare_of_calls F FP prepare attempt
  exact {
    recognize := recognize
    compare := hcmp
    countPre := P12CountPre.countPreZ_turingPolytime_checked F (recoveringPlan F FP)
      (Fintype.equivFin Kˣ).symm hcmp
    countPost := P12CountPost.countPostZ_turingPolytime_of_compare F (recoveringPlan F FP)
      (Fintype.equivFin Kˣ).symm hcmp
  }

theorem fixedFieldEvenOrderTI_of_algebra_runtime
    (h : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (F : FieldEncoding K),
      ∃ FP : FieldPresentation K,
        TuringPolytime (recognizeWords F (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))) ∧
        TuringPolytime (P12Compare.comparePreZ F) ∧
        TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    FixedFieldEvenOrderTI := by
  apply fixedFieldEvenOrderTI_of_live_machines
  intro K _ _ _ F
  obtain ⟨FP, hrec, hprep, hatt⟩ := h K F
  exact ⟨FP, ⟨liveMachines_of_algebra_runtime F FP hrec hprep hatt⟩⟩

#print axioms liveMachines_of_algebra_runtime
#print axioms fixedFieldEvenOrderTI_of_algebra_runtime
end EvenTI.Headline
