import EvenP12CountPostNormalize
import EvenP12CountPostClassify

namespace EvenTI.P12CountPost

open EvenTI.Action EvenTI.Contract EvenTI.Counting EvenTI.P10Oracle
open Lax51.TuringPolytime
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ}

/-- Keep a copy of the source input and prepare one comparison query. -/
def postRouteIn (w : List ℕ) : List ℕ :=
  positiveWords w ++ 0 :: packSegments [postZSource w]

/-- Extract the retained source and its comparison result from the physical
callback stream. The comparison may return an empty segment on arbitrary input. -/
def postRouteOut (enum : Fin q ≃ Kˣ) (w : List ℕ) : List ℕ :=
  postNormalize enum (unpositiveWords (cut w).1) (unpositiveWords (cut (cut w).2).1)

theorem postRouteIn_eq_duplicate (w : List ℕ) :
    postRouteIn w = mapZ (positiveCallback postZSource) (packSegments [w, w]) := by
  rw [show packSegments [w,w] = positiveWords w ++ 0 :: packSegments [w] by
    simp [packSegments]]
  simp [postRouteIn]

theorem postNormalize_eq_routed_callback (compare : List ℕ → List ℕ)
    (enum : Fin q ≃ Kˣ) (w : List ℕ) :
    postNormalize enum w (compare (postZSource w)) =
      postRouteOut enum (mapZ (positiveCallback compare) (postRouteIn w)) := by
  simp only [postRouteIn, mapZ_positiveWords, mapRest_packSegments, List.map_cons, List.map_nil]
  unfold postRouteOut
  simp only [cut_positiveWords, unpositiveWords_positiveWords]
  rw [show packSegments [compare (postZSource w)] = positiveWords (compare (postZSource w)) ++ [0] by
    simp [packSegments]]
  simp

theorem postNormalize_eq_routed (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (w : List ℕ) :
    postNormalize enum w (compareWords F P (postZSource w)) =
      postRouteOut enum (mapZ (positiveCallback (compareWords F P)) (postRouteIn w)) :=
  postNormalize_eq_routed_callback (compareWords F P) enum w
theorem countPostZ_turingPolytime_of_routed (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ)
    (hDup : TuringPolytime (fun w => packSegments [w,w]))
    (hSource : TuringPolytime postZSource)
    (hCompare : TuringPolytime (compareWords F P))
    (hOut : TuringPolytime (postRouteOut enum)) :
    TuringPolytime (countPostZ F P enum) := by
  apply countPostZ_turingPolytime_of_normalize
  have hIn : TuringPolytime postRouteIn := by
    rw [show postRouteIn = mapZ (positiveCallback postZSource) ∘
      (fun w => packSegments [w,w]) from funext postRouteIn_eq_duplicate]
    exact turingPolytime_comp hDup
      (turingPolytime_mapZ (positiveCallback_turingPolytime hSource))
  rw [show (fun w => postNormalize enum w (compareWords F P (postZSource w))) =
    postRouteOut enum ∘ (mapZ (positiveCallback (compareWords F P)) ∘ postRouteIn) from
    funext (postNormalize_eq_routed F P enum)]
  exact turingPolytime_comp
    (turingPolytime_comp hIn (turingPolytime_mapZ (positiveCallback_turingPolytime hCompare))) hOut

#print axioms postRouteIn_eq_duplicate
#print axioms postNormalize_eq_routed
#print axioms countPostZ_turingPolytime_of_routed
end EvenTI.P12CountPost
