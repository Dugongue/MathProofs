import EvenP12CompareSelector
import EvenP11Headline

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.P10Oracle EvenTI.P10Scan
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

set_option autoImplicit false

private theorem selectTrace_done (xs : List ℕ) : selectTrace 3 xs = (3, []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [selectTrace, selectNext, selectEmit, ih]

private theorem selectTrace_skip (a t : List ℕ) :
    selectTrace 1 (positiveWords a ++ 0 :: t) = selectTrace 0 t := by
  induction a with
  | nil => simp [positiveWords, selectTrace, selectNext, selectEmit]
  | cons x xs ih =>
    change selectTrace 1 ((x + 1) :: (positiveWords xs ++ 0 :: t)) = _
    simp [selectTrace, selectNext, selectEmit, ih]

private theorem selectTrace_copy (a t : List ℕ) :
    selectTrace 2 (positiveWords a ++ 0 :: t) = (3, a) := by
  induction a with
  | nil => simp [positiveWords, selectTrace, selectNext, selectEmit, selectTrace_done]
  | cons x xs ih =>
    change selectTrace 2 ((x + 1) :: (positiveWords xs ++ 0 :: t)) = _
    simp [selectTrace, selectNext, selectEmit, ih]

theorem selectPacked_packSegments (xs : List (List ℕ)) :
    selectPacked (packSegments xs) = (xs.findSome? okW).getD [0] := by
  induction xs with
  | nil => simp [selectPacked, packSegments, selectTrace, selectFinish]
  | cons w ws ih =>
    have hp : packSegments (w :: ws) = positiveWords w ++ 0 :: packSegments ws := by
      simp [packSegments]
    rw [hp, List.findSome?_cons]
    cases w with
    | nil =>
      simpa [positiveWords, selectPacked, selectTrace, selectNext, selectEmit, okW] using ih
    | cons a tail =>
      change selectPacked ((a + 1) :: (positiveWords tail ++ 0 :: packSegments ws)) = _
      cases a with
      | zero =>
        simpa [selectPacked, selectTrace, selectNext, selectEmit, selectTrace_skip, okW] using ih
      | succ a =>
        simp [selectPacked, selectTrace, selectNext, selectEmit, selectTrace_copy, selectFinish, okW]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Store each comparison request with its original input and the two prepared
trial encodings. The first empty segment is the unchanged oracle context. -/
def comparePreZ (F : FieldEncoding K) (words : List ℕ) : List ℕ :=
  0 :: packSegments ((pairWords F (preparedTrialWords F) words).map (pairW words))

/-- The exact comparison equation is independent of runtime assumptions. -/
theorem compareWords_eq_preparedScan (F : FieldEncoding K) (A : PairAttempt K) :
    compareWords F (comparisonPlan F A) =
      scanFirst (pairWords F (preparedTrialWords F)) (preparedAttemptWords F A) := by
  funext words
  unfold compareWords scanFirst
  cases hp : decodePair F words with
  | none => simp [pairWords_none F (preparedTrialWords F) hp]
  | some p =>
    have h := decodePair_balanced hp
    simp only
    rw [pairWords_eq F (preparedTrialWords F) hp h, List.findSome?_map]
    rw [findSome?_congr' (g := fun b => (attemptAt A (cutHalf p.d) h p.source p.target b).map
        fun g => transporterOutput F g ((Fintype.card K - 1) ^ (p.d - 1))) _
      (fun b hb => by
        simp only [Function.comp_def]
        rw [preparedAttemptWords_encoded F A words p hp h b, okW_attemptOutput])]
    rw [findSome?_option_map]
    have hs : search (comparisonPlan F A) p.source p.target =
        (pairsAt F (cutHalf p.d) h p.source p.target).findSome?
          (attemptAt A (cutHalf p.d) h p.source p.target) := by
      unfold search
      rw [comparisonPlan_enumerate, dif_pos h]
      exact findSome?_congr' _ (fun b _ => (comparisonPlan_attempt F A _ _ b).trans (dif_pos h))
    rw [hs]
    cases (pairsAt F (cutHalf p.d) h p.source p.target).findSome?
      (attemptAt A (cutHalf p.d) h p.source p.target) <;> rfl

/-- Exact physical callback factorization of the comparison with no
generic RAM scan-closure or result-selector assumptions. -/
theorem compareWords_eq_zeroDelimited (F : FieldEncoding K) (A : PairAttempt K) :
    compareWords F (comparisonPlan F A) =
      selectPacked ∘ mapZ (positiveCallback (preparedAttemptWords F A)) ∘ comparePreZ F := by
  rw [compareWords_eq_preparedScan]
  funext words
  change scanFirst _ _ _ =
    selectPacked (mapZ _ (positiveWords [] ++ 0 ::
      packSegments ((pairWords F (preparedTrialWords F) words).map (pairW words))))
  rw [mapZ_positiveWords, mapRest_packSegments]
  change scanFirst _ _ _ = selectPacked (0 ::
    packSegments (((pairWords F (preparedTrialWords F) words).map (pairW words)).map
      (preparedAttemptWords F A)))
  simp only [selectPacked, selectTrace, selectNext, selectEmit, if_pos rfl, ne_eq, not_true_eq_false,
    false_and, List.nil_append]
  change scanFirst _ _ _ =
    selectPacked (packSegments (((pairWords F (preparedTrialWords F) words).map (pairW words)).map
      (preparedAttemptWords F A)))
  rw [selectPacked_packSegments, scanFirst]
  simp [List.map_map, List.findSome?_map, Function.comp_def]

theorem turingPolytime_liveCompare_of_calls (F : FieldEncoding K) (FP : FieldPresentation K)
    (hPrepare : TuringPolytime (comparePreZ F))
    (hAttempt : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    TuringPolytime (compareWords F (Headline.recoveringPlan F FP)) := by
  change TuringPolytime (compareWords F (comparisonPlan F (CellPreparation.recoveringPairAttempt F FP)))
  rw [compareWords_eq_zeroDelimited]
  exact turingPolytime_comp (turingPolytime_comp hPrepare
    (turingPolytime_mapZ (positiveCallback_turingPolytime hAttempt))) selectPacked_turingPolytime

#print axioms compareWords_eq_zeroDelimited
#print axioms turingPolytime_liveCompare_of_calls

end EvenTI.P12Compare
