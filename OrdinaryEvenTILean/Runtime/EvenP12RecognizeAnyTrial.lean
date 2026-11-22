import EvenP12CompareAssembly

set_option autoImplicit false

namespace EvenTI.P12Guard

open Lax51.TuringPolytime
open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12Compare

/-- First-success selection on encoded Boolean answers implements disjunction. -/
theorem selectPacked_boolean (answers : List (List Nat))
    (hAnswers : ∀ x ∈ answers, x = [0] ∨ x = [1]) :
    selectPacked (packSegments answers) = if [1] ∈ answers then [1] else [0] := by
  rw [selectPacked_packSegments]
  induction answers with
  | nil => rfl
  | cons ans rest ih =>
    have ht : ∀ x ∈ rest, x = [0] ∨ x = [1] := fun x h => hAnswers x (List.mem_cons_of_mem _ h)
    rcases hAnswers ans (List.mem_cons_self ..) with h | h
    · subst ans
      simpa [List.findSome?_cons, okW] using ih ht
    · subst ans
      simp [List.findSome?_cons, okW]

/-- Apply a binary decision machine to every serialized trial and take their
disjunction with the checked streaming selector. The initial empty segment is
the oracle-map context. -/
theorem packedTrialsAny_time {prepare : List Nat → List (List Nat)}
    {decideTrial : List Nat → List Nat}
    (hPrepare : TuringPolytime (fun w => packSegments ([] :: prepare w)))
    (hDecide : TuringPolytime decideTrial)
    (hAnswer : ∀ x, decideTrial x = [0] ∨ decideTrial x = [1]) :
    TuringPolytime (fun w => if [1] ∈ (prepare w).map decideTrial then [1] else [0]) := by
  have hMap := turingPolytime_mapZ (positiveCallback_turingPolytime hDecide)
  have hAll := turingPolytime_comp (turingPolytime_comp hPrepare hMap) selectPacked_turingPolytime
  convert hAll using 1
  funext w
  change _ = selectPacked (mapZ (positiveCallback decideTrial)
    (positiveWords [] ++ 0 :: packSegments (prepare w)))
  rw [mapZ_positiveWords, mapRest_packSegments]
  change _ = selectPacked (packSegments ([] :: (prepare w).map decideTrial))
  simp only [packSegments, List.flatMap_cons, positiveWords, List.map_nil, List.nil_append]
  change _ = selectPacked (0 :: packSegments ((prepare w).map decideTrial))
  have he : selectPacked (0 :: packSegments ((prepare w).map decideTrial)) =
      selectPacked (packSegments ((prepare w).map decideTrial)) := by
    simp [selectPacked, selectTrace, selectNext, selectEmit]
  rw [he, selectPacked_boolean]
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact hAnswer t

#print axioms packedTrialsAny_time
end EvenTI.P12Guard
