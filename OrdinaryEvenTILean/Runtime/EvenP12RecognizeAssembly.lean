import EvenP11LiveMachines
import EvenP12RecognizeGuardMachine
import EvenP12CountPreFrame

namespace EvenTI.P12Guard

open Lax51.TuringPolytime Lax51.BinaryWordEncoding
open EvenTI.P10Oracle

set_option autoImplicit false
set_option maxHeartbeats 510000

private theorem suffix_true_iff (a b : List Nat) :
    let xs := packSegments [a,b]
    3 ≤ xs.length ∧ xs.drop (xs.length - 3) = [0,2,0] ↔ b = [1] := by
  let xs := packSegments [a,b]
  change (3 ≤ xs.length ∧ xs.drop (xs.length - 3) = [0,2,0]) ↔ _
  constructor
  · rintro ⟨hl,hs⟩
    have hr := congrArg List.reverse hs
    have hsub : xs.length - (xs.length - 3) = 3 := by omega
    rw [List.reverse_drop, hsub] at hr
    have hshape :
        xs.reverse = 0 :: (b.reverse.map Nat.succ ++ 0 :: (a.reverse.map Nat.succ)) := by
      simp [xs,packSegments,positiveWords,List.reverse_append,List.map_reverse]
    rw [hshape] at hr
    cases he : b.reverse with
    | nil => simp [he] at hr
    | cons p ps =>
      cases ps with
      | nil =>
        have hp : p = 1 := by simp [he] at hr; omega
        have ht := congrArg List.reverse he
        simpa [hp] using ht
      | cons q qs => simp [he] at hr
  · intro h
    subst b
    have hx : xs = positiveWords a ++ [0,2,0] := by simp [xs,packSegments,positiveWords]
    rw [hx]
    have hel : ((positiveWords a) ++ [0,2,0]).length - 3 = (positiveWords a).length := by
      simp
    exact ⟨by simp, by rw [hel,List.drop_append_length]⟩

theorem route_pair (a b : List Nat) :
    routeOutput true (packSegments [a,b]) =
      if b = [1] then packSegments [[],a] else packSegments [[]] := by
  have hb := suffix_true_iff a b
  unfold routeOutput
  by_cases ht : b = [1]
  · subst b
    have hshape : packSegments [a,[1]] = positiveWords a ++ [0,2,0] := by
      simp [packSegments,positiveWords]
    have hlen : (packSegments [a,[1]]).length - 3 = (positiveWords a).length := by rw [hshape]; simp
    simp only [true_or, true_and, if_true, hlen]
    rw [hshape,List.take_append_of_le_length le_rfl,List.take_length]
    simp [packSegments,positiveWords]
  · change (3 ≤ (packSegments [a,b]).length ∧
      (packSegments [a,b]).drop ((packSegments [a,b]).length - 3) = [0,2,0]) ↔ b = [1] at hb
    have hf : ¬(3 ≤ (packSegments [a,b]).length ∧
      (packSegments [a,b]).drop ((packSegments [a,b]).length-3) = [0,2,0]) := fun h => ht (hb.mp h)
    simp only [true_or,true_and,if_neg hf,if_neg ht]
    rfl

theorem test_suffix (xs : List Nat) :
    routeOutput false xs = if xs = [0,2,0] then [1] else [0] := by
  unfold routeOutput
  by_cases h : xs.length = 3
  · simp [h]
  · have hne : xs ≠ [0,2,0] := fun he => h (by simp [he])
    simp [h,hne]

private theorem map_pair (f : List Nat → List Nat) (a b : List Nat) :
    mapZ (positiveCallback f) (packSegments [a,b]) = packSegments [a, f b] := by
  rw [show packSegments [a,b] = positiveWords a ++ 0 :: packSegments [b] by simp [packSegments]]
  rw [mapZ_positiveWords, mapRest_packSegments]
  simp [packSegments]

private theorem map_empty_tail (f : List Nat → List Nat) :
    mapZ (positiveCallback f) (packSegments [[]]) = packSegments [[]] := by
  change mapZ (positiveCallback f) (positiveWords [] ++ 0 :: packSegments []) = _
  rw [mapZ_positiveWords,mapRest_packSegments]
  rfl

def gateConj (f g : List Nat → List Nat) (x : List Nat) : List Nat :=
  if f x = [1] ∧ g x = [1] then [1] else [0]

/-- Intersect two actual decision machines on the same input. The tape
router retains a copy of the input and invokes the second machine only
when the first output is exactly the one-word answer `[1]`. -/
theorem gateConj_time {f g : List Nat → List Nat}
    (hf : TuringPolytime f) (hg : TuringPolytime g) : TuringPolytime (gateConj f g) := by
  let prep := fun x => packSegments [x,x]
  have h1 : TuringPolytime prep := EvenTI.P12CountPre.duplicateFrame_turingPolytime
  have h2 := turingPolytime_comp h1 (turingPolytime_mapZ (positiveCallback_turingPolytime hf))
  have h3 := turingPolytime_comp h2 (routeOutput_time true)
  have h4 := turingPolytime_comp h3 (turingPolytime_mapZ (positiveCallback_turingPolytime hg))
  have h5 := turingPolytime_comp h4 (routeOutput_time false)
  convert h5 using 1
  funext x
  simp only [Function.comp_apply,prep,map_pair,route_pair,gateConj]
  by_cases hx : f x = [1]
  · simp only [hx,true_and,if_true,map_pair,test_suffix]
    have he : packSegments [[],g x] = [0,2,0] ↔ g x = [1] := by
      have hkey : packSegments [[],[1]] = [0,2,0] := rfl
      rw [← hkey]
      constructor
      · intro h
        have hk := congrArg unpackSegments h
        simpa only [unpackSegments_packSegments,List.cons.injEq,true_and,and_true] using hk
      · intro h; rw [h]
    by_cases ht : g x = [1]
    · simp only [if_pos ht, if_pos (he.mpr ht)]
    · simp only [if_neg ht, if_neg (fun hh => ht (he.mp hh))]
  · simp only [hx,false_and,if_false,map_empty_tail,test_suffix]
    rfl

open EvenTI.Action EvenTI.Contract EvenTI.Headline Mathproof.EvenTI.P9Recognizer
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem recognizeWords_distribution (F : FieldEncoding K)
    (s c : ∀ {d n : Nat}, Tensor K d n → Bool) :
    recognizeWords F (execAccept s c) =
      gateConj (recognizeWords F s) (recognizeWords F c) := by
  funext x
  unfold recognizeWords gateConj
  cases h : decodeSource F x with
  | none => simp [h]
  | some p =>
    by_cases hs : s p.tensor = true
    · by_cases hc : c p.tensor = true
      · simp [h,execAccept,hs,hc]
      · have hc' : c p.tensor = false := Bool.eq_false_iff.mpr hc
        simp [h,execAccept,hs,hc']
    · have hs' : s p.tensor = false := Bool.eq_false_iff.mpr hs
      simp [h,execAccept,hs']

theorem liveRecognize_time_of_gateTimes (F : FieldEncoding K) (FP : FieldPresentation K)
    (hSpectral : TuringPolytime (recognizeWords F (LiveSpectral.spectralExec F)))
    (hScalar : TuringPolytime (recognizeWords F (liveScalarExec F FP))) :
    TuringPolytime (recognizeWords F (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))) := by
  rw [recognizeWords_distribution]
  exact gateConj_time hSpectral hScalar

#print axioms gateConj_time
#print axioms liveRecognize_time_of_gateTimes
end EvenTI.P12Guard
