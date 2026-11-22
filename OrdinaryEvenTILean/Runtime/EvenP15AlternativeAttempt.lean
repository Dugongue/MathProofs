import EvenP15ExecutionRoot

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P15Execution

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Compare EvenTI.Headline
open Lax51.TuringPolytime
open Mathproof.EvenTI.GlobalCoverage
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A choice of any sound transporter on each successful trial is sufficient.
Only success coverage of the reference recovery needs to be preserved. -/
structure RecoveryRefines (D : FieldEncoding K) (F : FieldPresentation K) (A : PairAttempt K) : Prop where
  sound : ∀ {l n : ℕ} (T S : Dense K l n) (P Q : PreparedTrial K l n) g,
    A T S P Q = some g → act g T = S
  covers : ∀ {l n : ℕ} (T S : Dense K l n) (P Q : PreparedTrial K l n) g,
    sourceAccepted T → CellPreparation.recoveringPairAttempt D F T S P Q = some g → (A T S P Q).isSome = true

/-- The clocked callback need only agree on requests emitted by the producer. -/
def OnTrialRequests (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (A : PairAttempt K) (callback : List ℕ → List ℕ) : Prop :=
  ∀ (w : List ℕ) (p : ParsedPair K), decodePair D w = some p →
    ∀ (h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1))
      (b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n),
      b ∈ pairs h p.source p.target →
      callback (pairW w (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2))) =
        attemptOutput D (attemptAt A (cutHalf p.d) h p.source p.target b)

noncomputable def alternativeTrialPlan (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (A : PairAttempt K) : TrialPlan K :=
  { comparisonPlan D A with
    enumerate := fun {d n} T S =>
      if h : d = (cutHalf d+1)+(cutHalf d+1) then pairs h T S else [] }

private theorem recoverySoundAt {D : FieldEncoding K} {F : FieldPresentation K}
    {A : PairAttempt K} (hA : RecoveryRefines D F A) {d l n : ℕ}
    (h : d = (l+1)+(l+1)) (T S : Tensor K d n)
    (trial : PreparedTrial K l n × PreparedTrial K l n) (g : Changes K d n)
    (hr : attemptAt A l h T S trial = some g) : act g T = S := by
  subst d
  exact hA.sound T S trial.1 trial.2 g hr

private theorem recoveryCoversAt {D : FieldEncoding K} {F : FieldPresentation K}
    {A : PairAttempt K} (hA : RecoveryRefines D F A) {d l n : ℕ}
    (h : d = (l+1)+(l+1)) (T S : Tensor K d n)
    (trial : PreparedTrial K l n × PreparedTrial K l n) (g : Changes K d n)
    (hT : sourceAccepted T)
    (hr : attemptAt (CellPreparation.recoveringPairAttempt D F) l h T S trial = some g) :
    (attemptAt A l h T S trial).isSome = true := by
  subst d
  exact hA.covers T S trial.1 trial.2 g hT hr

theorem alternativeTrialPlan_complete (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (hCover : CoversRawTrialPairs D pairs)
    (A : PairAttempt K) (hA : RecoveryRefines D F A) {d n : ℕ}
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) (T S : Tensor K d n) (hT : sourceAccepted T) :
    CompleteTrials (alternativeTrialPlan D pairs A) T S := by
  have hcut := (cutHalf_spec hd he).1
  refine ⟨?_,?_⟩
  · intro b _ g hg
    change (if h : d = (cutHalf d+1)+(cutHalf d+1) then
      attemptAt A (cutHalf d) h T S b else none) = some g at hg
    rw [dif_pos hcut] at hg
    exact recoverySoundAt hA hcut T S b g hg
  · intro hg
    obtain ⟨b,hb,g₀,hg₀⟩ := (recoveringPlan_complete D F hd he hn T S hT).2 hg
    change b ∈ (if h : d = (cutHalf d+1)+(cutHalf d+1) then pairsAt D (cutHalf d) h T S else []) at hb
    rw [dif_pos hcut] at hb
    change (if h : d = (cutHalf d+1)+(cutHalf d+1) then
      attemptAt (CellPreparation.recoveringPairAttempt D F) (cutHalf d) h T S b else none) = some g₀ at hg₀
    rw [dif_pos hcut] at hg₀
    obtain ⟨g,hg⟩ := Option.isSome_iff_exists.mp (recoveryCoversAt hA hcut T S b g₀ hT hg₀)
    refine ⟨b,?_,g,?_⟩
    · change b ∈ (if h : d = (cutHalf d+1)+(cutHalf d+1) then pairs h T S else [])
      rw [dif_pos hcut]
      exact hCover hcut T S b hb
    · change (if h : d = (cutHalf d+1)+(cutHalf d+1) then
        attemptAt A (cutHalf d) h T S b else none) = some g
      rwa [dif_pos hcut]

private theorem searchAlternative_eq (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (A : PairAttempt K) {d n : ℕ} (h : d = (cutHalf d+1)+(cutHalf d+1)) (T S : Tensor K d n) :
    search (alternativeTrialPlan D pairs A) T S = (pairs h T S).findSome? (attemptAt A (cutHalf d) h T S) := by
  unfold search
  change (if h' : d = (cutHalf d+1)+(cutHalf d+1) then pairs h' T S
    else []).findSome? ((comparisonPlan D A).attempt T S) = _
  rw [dif_pos h]
  exact findSome?_congr' _ (fun b _ => (comparisonPlan_attempt D A _ _ b).trans (dif_pos h))

theorem alternativeCompare_eq (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (A : PairAttempt K) (cb : List ℕ → List ℕ) (hcb : OnTrialRequests D pairs A cb) :
    compareWords D (alternativeTrialPlan D pairs A) =
      selectPacked ∘ mapZ (positiveCallback cb) ∘ comparePrePairsZ D pairs := by
  funext words
  let requests := match decodePair D words with
    | none => []
    | some p =>
      if h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) then
        (pairs h p.source p.target).map
          (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n =>
            pairW words (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2)))
      else []
  have hs : selectPacked (mapZ (positiveCallback cb) (0 :: packSegments requests)) =
      ((requests.map cb).findSome? okW).getD [0] := by
    change selectPacked (mapZ _ (positiveWords [] ++ 0 :: packSegments requests)) = _
    rw [mapZ_positiveWords,mapRest_packSegments]
    change selectPacked (0 :: packSegments (requests.map cb)) = _
    have hz (s : List ℕ) : selectPacked (0 :: s) = selectPacked s := by
      simp [selectPacked,selectTrace,selectEmit,selectNext]
    rw [hz,selectPacked_packSegments]
  change compareWords D (alternativeTrialPlan D pairs A) words =
    selectPacked (mapZ (positiveCallback cb) (0 :: packSegments requests))
  rw [hs]
  unfold compareWords
  cases hp : decodePair D words with
  | none => simp [requests,hp]
  | some p =>
    have h := decodePair_balanced hp
    simp only [requests,hp,dif_pos h]
    rw [searchAlternative_eq D pairs A h,List.map_map,List.findSome?_map]
    have hf := findSome?_congr' (f := okW ∘ cb ∘
      (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n =>
        pairW words (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2))))
      (g := fun b => (attemptAt A (cutHalf p.d) h p.source p.target b).map
        (fun g => transporterOutput D g ((Fintype.card K-1)^(p.d-1))))
      (pairs h p.source p.target)
      (fun b hb => by
        simp only [Function.comp_apply]
        rw [hcb words p hp h b hb,okW_attemptOutput])
    rw [hf,findSome?_option_map]
    change (match (pairs h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) with
      | none => [0]
      | some g => transporterOutput D g ((Fintype.card K-1)^(p.d-1))) = _
    cases (pairs h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) <;> rfl

theorem alternativeCompare_time (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (A : PairAttempt K) (cb : List ℕ → List ℕ) (hc : OnTrialRequests D pairs A cb)
    (hPre : TuringPolytime (comparePrePairsZ D pairs)) (hCb : TuringPolytime cb) :
    TuringPolytime (compareWords D (alternativeTrialPlan D pairs A)) := by
  rw [alternativeCompare_eq D pairs A cb hc]
  exact turingPolytime_comp (turingPolytime_comp hPre
    (turingPolytime_mapZ (positiveCallback_turingPolytime hCb))) selectPacked_turingPolytime

#print axioms alternativeTrialPlan_complete
#print axioms alternativeCompare_eq
#print axioms alternativeCompare_time
end EvenTI.P15Execution