import EvenP12ComparePrepNativeRoot

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.Headline EvenTI.P10Oracle
open EvenTI.TrialProducer EvenTI.P12Compare EvenTI.P12CountPre EvenTI.P10Scan
open Mathproof.EvenTI.GlobalCoverage Mathproof.EvenTI.P9Recognizer Mathproof.EvenTI.P9Root
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Physical preparation may choose its order jointly for the source and target. -/
abbrev BalancedTrialPairs (K : Type) [Field K] [DecidableEq K] :=
  ∀ {d n : ℕ}, d = (cutHalf d+1)+(cutHalf d+1) → Tensor K d n → Tensor K d n →
    List (PreparedTrial K (cutHalf d) n × PreparedTrial K (cutHalf d) n)

variable (F : FieldEncoding K) (pairs : BalancedTrialPairs K)

def CoversRawTrialPairs : Prop :=
  ∀ {d n : ℕ} (h : d = (cutHalf d+1)+(cutHalf d+1))
    (T S : Tensor K d n) (x : PreparedTrial K (cutHalf d) n × PreparedTrial K (cutHalf d) n),
    x ∈ pairsAt F (cutHalf d) h T S → x ∈ pairs h T S

noncomputable def comparePlanFromPairs (FP : FieldPresentation K) : TrialPlan K :=
  { recoveringPlan F FP with
    enumerate := fun {d n} T S =>
      if h : d = (cutHalf d+1)+(cutHalf d+1) then pairs h T S else [] }

theorem comparePlanFromPairs_complete (FP : FieldPresentation K)
    (hCover : CoversRawTrialPairs F pairs) {d n : ℕ} (hd : 4 ≤ d) (he : Even d)
    (hn : 2 ≤ n) (T S : Tensor K d n) (hT : sourceAccepted T) :
    CompleteTrials (comparePlanFromPairs F pairs FP) T S := by
  have hcut := (cutHalf_spec hd he).1
  have soundAt {l : ℕ} (h : d = (l + 1) + (l + 1))
      (b : PreparedTrial K l n × PreparedTrial K l n) (g : Changes K d n)
      (hg : attemptAt (CellPreparation.recoveringPairAttempt F FP) l h T S b = some g) :
      act g T = S := by
    subst d
    exact CellPreparation.recoveringPairAttempt_sound F FP _ _ _ _ _ hg
  refine ⟨?_,?_⟩
  · intro b _ g hg
    change (if h : d = (cutHalf d+1)+(cutHalf d+1) then
      attemptAt (CellPreparation.recoveringPairAttempt F FP) (cutHalf d) h T S b else none) = some g at hg
    rw [dif_pos hcut] at hg
    exact soundAt hcut b g hg
  · intro hg
    obtain ⟨b,hb,g,hg⟩ := (recoveringPlan_complete F FP hd he hn T S hT).2 hg
    refine ⟨b,?_,g,hg⟩
    change b ∈ (if h : d = (cutHalf d+1)+(cutHalf d+1) then pairs h T S else [])
    rw [dif_pos hcut]
    apply hCover hcut T S b
    change b ∈ (if h : d = (cutHalf d+1)+(cutHalf d+1) then pairsAt F (cutHalf d) h T S else []) at hb
    simpa only [dif_pos hcut] using hb

private theorem search_eq_findSome?_providedPairsAt (FP : FieldPresentation K) {d n : ℕ}
    (h : d = (cutHalf d+1)+(cutHalf d+1)) (T S : Tensor K d n) :
    search (comparePlanFromPairs F pairs FP) T S =
      (pairs h T S).findSome? (attemptAt (CellPreparation.recoveringPairAttempt F FP) (cutHalf d) h T S) := by
  unfold search
  change (if h' : d = (cutHalf d+1)+(cutHalf d+1) then pairs h' T S
    else []).findSome? ((recoveringPlan F FP).attempt T S) = _
  rw [dif_pos h]
  exact findSome?_congr' _ (fun b _ =>
    (comparisonPlan_attempt F (CellPreparation.recoveringPairAttempt F FP) _ _ b).trans (dif_pos h))
/-- The raw comparison callback emitted by a scan of the native banks. -/
def comparePrePairsZ (words : List ℕ) : List ℕ :=
  0 :: packSegments (match decodePair F words with
    | none => []
    | some p =>
      if h : p.d = (cutHalf p.d+1) + (cutHalf p.d+1) then
        (pairs h p.source p.target).map
          (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n => pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2)))
      else [])

theorem compareWords_eq_pairScan (FP : FieldPresentation K) :
    compareWords F (comparePlanFromPairs F pairs FP) =
      selectPacked ∘ mapZ (positiveCallback
        (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) ∘
        comparePrePairsZ F pairs := by
  funext words
  let A : PairAttempt K := CellPreparation.recoveringPairAttempt F FP
  let cb := preparedAttemptWords F A
  let requests := match decodePair F words with
    | none => []
    | some p =>
      if h : p.d = (cutHalf p.d+1) + (cutHalf p.d+1) then
        (pairs h p.source p.target).map
          (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n => pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2)))
      else []
  have hs : selectPacked (mapZ (positiveCallback cb) (0 :: packSegments requests)) =
      ((requests.map cb).findSome? okW).getD [0] := by
    change selectPacked (mapZ _ (positiveWords [] ++ 0 :: packSegments requests)) = _
    rw [mapZ_positiveWords, mapRest_packSegments]
    change selectPacked (0 :: packSegments (requests.map cb)) = _
    have hz (s : List ℕ) : selectPacked (0 :: s) = selectPacked s := by
      simp [selectPacked,selectTrace,selectEmit,selectNext]
    rw [hz,selectPacked_packSegments]
  change compareWords F (comparePlanFromPairs F pairs FP) words =
    selectPacked (mapZ (positiveCallback cb) (0 :: packSegments requests))
  rw [hs]
  unfold compareWords
  cases hp : decodePair F words with
  | none => simp [requests, hp]
  | some p =>
    have h := decodePair_balanced hp
    simp only [requests,hp,dif_pos h]
    rw [search_eq_findSome?_providedPairsAt F pairs FP h, List.map_map, List.findSome?_map]
    have hf := findSome?_congr' (f := okW ∘ cb ∘
      (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n =>
        pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2))))
      (g := fun b => (attemptAt A (cutHalf p.d) h p.source p.target b).map
        (fun g => transporterOutput F g ((Fintype.card K-1)^(p.d-1))))
      (pairs h p.source p.target)
      (fun b _ => by
        simp only [Function.comp_apply,cb]
        rw [preparedAttemptWords_encoded F A words p hp h b, okW_attemptOutput])
    rw [hf, findSome?_option_map]
    change (match (pairs h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) with
      | none => [0]
      | some g => transporterOutput F g ((Fintype.card K-1)^(p.d-1))) = _
    cases (pairs h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) <;> rfl

theorem turingPolytime_comparePairs (FP : FieldPresentation K)
    (hPrepare : TuringPolytime (comparePrePairsZ F pairs))
    (hAttempt : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    TuringPolytime (compareWords F (comparePlanFromPairs F pairs FP)) := by
  rw [compareWords_eq_pairScan]
  exact turingPolytime_comp (turingPolytime_comp hPrepare
    (turingPolytime_mapZ (positiveCallback_turingPolytime hAttempt))) selectPacked_turingPolytime

/-- The exact solver theorem permits pair-dependent physical trial order. -/
noncomputable def solverOfProvidedPairs (F : FieldEncoding K) (FP : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (hCover : CoversRawTrialPairs F pairs)
    (hSelf : SelfScanSound F FP)
    (hRecognize : TuringPolytime (recognizeWords F
      (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))))
    (hPrepare : TuringPolytime (comparePrePairsZ F pairs))
    (hAttempt : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    VerifiedSolver F := by
  let P := comparePlanFromPairs F pairs FP
  let enum := (Fintype.equivFin Kˣ).symm
  have hCompare : TuringPolytime (compareWords F P) :=
    turingPolytime_comparePairs F pairs FP hPrepare hAttempt
  have hPre : TuringPolytime (countPreZ F P enum) :=
    countPreZ_turingPolytime_checked F P enum hCompare
  have hPost : TuringPolytime (countPostZ F P enum) :=
    EvenTI.P12CountPost.countPostZ_turingPolytime_of_compare F P enum hCompare
  have hRecognize' : TuringPolytime (recognizeWords F (coverageAccept K)) :=
    recognizeWords_eq_of_guarded F (LiveSpectral.spectralExec_agrees F)
      (liveScalarExec_agrees F FP hSelf) ▸ hRecognize
  exact assembleVerifiedSolver F (coverageAccept K) P enum
    (fun T g => (coverageAccept_invariant_iff).mpr (fun S a => sourceAccepted_act S a) T g)
    contract_uniformCoverage contract_higherOrderRate
    (fun hd he hn T S hT => by
      have h := (sourceAccept_eq_true T).mp hT
      exact ⟨h.2.1,comparePlanFromPairs_complete F pairs FP hCover hd he hn T S h,h.2.2⟩)
    hRecognize' hCompare
    (fun g hg => countWords_turingPolytime_of_zeroDelimited F P enum hPre hPost g hg)


#print axioms comparePlanFromPairs_complete
#print axioms turingPolytime_comparePairs
#print axioms solverOfProvidedPairs
end EvenTI.P12ComparePrep