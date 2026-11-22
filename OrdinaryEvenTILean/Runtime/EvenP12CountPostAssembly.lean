import EvenP12CountPostRoute
import EvenP12CountPostGate
import EvenP12CountPostRuntime
import EvenP12CountPostSuccess
import EvenP12CountPreFrame

namespace EvenTI.P12CountPost

open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle
open Lax51.TuringPolytime
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ}

theorem postRouteOut_turingPolytime (enum : Fin q ≃ Kˣ) :
    TuringPolytime (postRouteOut enum) := by
  have he : postRouteOut enum =
      normalizeClassified q ∘ (classifyFrame ∘ gateFrame) := by
    funext w
    exact (postRouteOut_eq_gateFrame enum w).trans (postNormalize_eq_normalizeClassified enum _)
  rw [he]
  exact turingPolytime_comp
    (turingPolytime_comp gateFrame_turingPolytime classifyFrame_turingPolytime)
      (normalizeClassified_turingPolytime q)

/-- Counts can reuse any comparison witness procedure whose success bit
agrees with the frozen trial plan. There is no witness-order obligation. -/
theorem countPostZ_turingPolytime_of_compare_success (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (compare : List ℕ → List ℕ)
    (hSuccess : ∀ x, (compareWords F P x).head? = some 2 ↔ (compare x).head? = some 2)
    (hCompare : TuringPolytime compare) :
    TuringPolytime (countPostZ F P enum) := by
  apply countPostZ_turingPolytime_of_normalize_success F P enum compare hSuccess
  have hIn : TuringPolytime postRouteIn := by
    rw [show postRouteIn = mapZ (positiveCallback postZSource) ∘
      (fun w => packSegments [w,w]) from funext postRouteIn_eq_duplicate]
    exact turingPolytime_comp EvenTI.P12CountPre.duplicateFrame_turingPolytime
      (turingPolytime_mapZ (positiveCallback_turingPolytime postZSource_turingPolytime))
  rw [show (fun w => postNormalize enum w (compare (postZSource w))) =
      postRouteOut enum ∘ (mapZ (positiveCallback compare) ∘ postRouteIn) from
    funext (postNormalize_eq_routed_callback compare enum)]
  exact turingPolytime_comp
    (turingPolytime_comp hIn (turingPolytime_mapZ (positiveCallback_turingPolytime hCompare)))
      (postRouteOut_turingPolytime enum)

/-- Physical post-processing with no assumption on the answer stream. Its
only tensor callback is the comparison machine. -/
theorem countPostZ_turingPolytime_of_compare (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (hCompare : TuringPolytime (compareWords F P)) :
    TuringPolytime (countPostZ F P enum) :=
  countPostZ_turingPolytime_of_compare_success F P enum (compareWords F P)
    (fun _ => Iff.rfl) hCompare

#print axioms postRouteOut_turingPolytime
#print axioms countPostZ_turingPolytime_of_compare_success
#print axioms countPostZ_turingPolytime_of_compare
end EvenTI.P12CountPost