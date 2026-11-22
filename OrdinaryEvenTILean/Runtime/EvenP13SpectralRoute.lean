import EvenP13SpectralScore
import EvenP12RecognizeAnyTrial
import EvenP11SpectralGate
import EvenP13SpectralScore
import EvenP11SpectralGate
import EvenP12RecognizeAnyTrial

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P13Spectral

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.PrimaryAlignment
open EvenTI.Comparison EvenTI.P10Oracle EvenTI.P10Scan EvenTI.LiveSpectral EvenTI.P12Compare
open Mathproof.EvenTI.P9Recognizer
open EvenTI.CellPreparation (originalChoiceCap)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A trial request retains its cap and one word segment for each numbered
anchor. This encoding does not require storing the primary factor table. -/
def anchorPayload (F : FieldEncoding K) {l n : ℕ} (p : PreparedTrial K l n) : List ℕ :=
  packSegments ([originalChoiceCap l n] :: (numberedAnchors p).map (numberedAnchorWords F))

def anchorTrialRunner (q : ℕ) (anchor : List ℕ → List ℕ) : List ℕ → List ℕ :=
  scoreWords q ∘ mapZ (positiveCallback anchor)

theorem anchorTrialRunner_answer (F : FieldEncoding K) (anchor : List ℕ → List ℕ)
    (ha : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A])
    {l n : ℕ} (p : PreparedTrial K l n) :
    anchorTrialRunner (Fintype.card K) anchor (anchorPayload F p) =
      [if Fintype.card K ^ storedTrialExponent F p ≤ originalChoiceCap l n then 1 else 0] := by
  let xs := (numberedAnchors p).map (numberedAnchorWords F)
  have hp : anchorPayload F p = positiveWords [originalChoiceCap l n] ++ 0 :: packSegments xs := by
    simp [anchorPayload,packSegments,xs]
  rw [anchorTrialRunner,Function.comp_apply,hp,mapZ_positiveWords,mapRest_packSegments]
  have he : xs.map anchor = ((numberedAnchors p).map (storedAnchorExponent F)).map (fun v => [v]) := by
    simp [xs,List.map_map,Function.comp_def,ha]
  rw [he]
  change [if Fintype.card K ^ anchorSum
      (packSegments (((numberedAnchors p).map (storedAnchorExponent F)).map fun v => [v])) ≤
        (originalChoiceCap l n+1)-1 then 1 else 0] = _
  rw [anchorSum_packed]
  simp only [Nat.add_sub_cancel,storedTrialExponent]
  by_cases h : Fintype.card K ^ ((numberedAnchors p).map (storedAnchorExponent F)).sum ≤ originalChoiceCap l n
  · simp [h]
  · simp [h]

def requestTrials (F : FieldEncoding K) (w : List ℕ) : List (List ℕ) :=
  match decodeSource F w with
  | none => []
  | some s =>
    let l := cutHalf s.d
    if h : s.d = (l+1)+(l+1) then
      if (l = 1 ∧ 5 ≤ s.n) ∨ (2 ≤ l ∧ 1 ≤ s.n) then
        (prepareTrials F (castDense l h s.tensor)).map (anchorPayload F)
      else []
    else []

theorem recognizeWords_eq_anchorTrials (F : FieldEncoding K) (anchor : List ℕ → List ℕ)
    (ha : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A]) :
    recognizeWords F (spectralExec F) = fun w =>
      if [1] ∈ (requestTrials F w).map (anchorTrialRunner (Fintype.card K) anchor)
      then [1] else [0] := by
  funext w
  unfold recognizeWords requestTrials
  cases hs : decodeSource F w with
  | none => simp [hs]
  | some s =>
    simp only
    by_cases h : s.d = (cutHalf s.d+1)+(cutHalf s.d+1)
    · by_cases hg : (cutHalf s.d = 1 ∧ 5 ≤ s.n) ∨ (2 ≤ cutHalf s.d ∧ 1 ≤ s.n)
      · simp only [spectralExec,dif_pos h,spectralAt,if_pos hg,decide_eq_true hg,Bool.true_and,trialSpectral]
        have hr : ((prepareTrials F (castDense (cutHalf s.d) h s.tensor)).any fun p =>
          decide (Fintype.card K ^ storedTrialExponent F p ≤ originalChoiceCap (cutHalf s.d) s.n)) = true ↔
            [1] ∈ ((prepareTrials F (castDense (cutHalf s.d) h s.tensor)).map (anchorPayload F)).map
              (anchorTrialRunner (Fintype.card K) anchor) := by
          simp only [List.any_eq_true,decide_eq_true_eq,List.map_map,List.mem_map,Function.comp_def,
            anchorTrialRunner_answer F anchor ha]
          constructor
          · rintro ⟨p,hp,hv⟩
            exact ⟨p,hp,by simp [hv]⟩
          · rintro ⟨p,hp,hv⟩
            refine ⟨p,hp,?_⟩
            by_contra hn
            simp [hn] at hv
        split
        · rename_i hp
          rw [if_pos (hr.mp hp)]
        · rename_i hp
          rw [if_neg (fun hs => hp (hr.mpr hs))]
      · simp only [spectralExec,dif_pos h,spectralAt,if_neg hg,decide_eq_false hg,Bool.false_and,if_false,List.map_nil,List.not_mem_nil,Bool.false_eq_true]
    · simp only [spectralExec,dif_neg h,if_false,List.map_nil,List.not_mem_nil,Bool.false_eq_true]

theorem recognizeSpectral_time_of_requests (F : FieldEncoding K) (anchor : List ℕ → List ℕ)
    (hq : 2 ≤ Fintype.card K) (hAnchorTime : TuringPolytime anchor)
    (hAnchor : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A])
    (hRequests : TuringPolytime (fun w => packSegments ([] :: requestTrials F w))) :
    TuringPolytime (recognizeWords F (spectralExec F)) := by
  rw [recognizeWords_eq_anchorTrials F anchor hAnchor]
  refine EvenTI.P12Guard.packedTrialsAny_time hRequests ?_ ?_
  · exact turingPolytime_comp (turingPolytime_mapZ (positiveCallback_turingPolytime hAnchorTime))
      (scoreWords_turingPolytime _ hq)
  · intro w
    unfold anchorTrialRunner
    simp only [Function.comp_apply]
    cases hmap : mapZ (positiveCallback anchor) w with
    | nil => exact Or.inl rfl
    | cons c tail =>
      cases tail with
      | nil => exact Or.inl rfl
      | cons z ys =>
        by_cases h : Fintype.card K ^ anchorSum ys ≤ c-1
        · exact Or.inr (by simp [hmap,scoreWords,h])
        · exact Or.inl (by simp [hmap,scoreWords,h])

#print axioms recognizeSpectral_time_of_requests
end EvenTI.P13Spectral
