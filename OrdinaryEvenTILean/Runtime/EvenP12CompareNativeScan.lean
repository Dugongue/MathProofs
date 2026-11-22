import EvenP12CompareBasisIndependent

set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer EvenTI.Headline
open EvenTI.P10Oracle EvenTI.P10Scan
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable (F : FieldEncoding K)
variable (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T)

private def bankPairsAt {d n : ℕ} (h : d = (cutHalf d + 1) + (cutHalf d + 1))
    (T S : Tensor K d n) : List (PreparedTrial K (cutHalf d) n × PreparedTrial K (cutHalf d) n) :=
  (prepareFromBanks F banks (castDense (cutHalf d) h T)).product
    (prepareFromBanks F banks (castDense (cutHalf d) h S))

private theorem mem_bankPairsAt {d n : ℕ} (h : d = (cutHalf d + 1) + (cutHalf d + 1))
    (T S : Tensor K d n) (p : PreparedTrial K (cutHalf d) n × PreparedTrial K (cutHalf d) n) :
    p ∈ bankPairsAt F banks h T S ↔ p ∈ pairsAt F (cutHalf d) h T S := by
  rcases p with ⟨p,q⟩
  unfold bankPairsAt pairsAt
  exact List.mem_product.trans ((and_congr
    (mem_prepareFromBanks F banks (castDense (cutHalf d) h T) p)
    (mem_prepareFromBanks F banks (castDense (cutHalf d) h S) q)).trans List.mem_product.symm)

private theorem search_eq_findSome?_bankPairsAt (FP : FieldPresentation K) {d n : ℕ}
    (h : d = (cutHalf d+1) + (cutHalf d+1)) (T S : Tensor K d n) :
    search (comparePlanFromBanks F banks FP) T S =
      (bankPairsAt F banks h T S).findSome?
        (attemptAt (CellPreparation.recoveringPairAttempt F FP) (cutHalf d) h T S) := by
  unfold search
  change (if h' : d = (cutHalf d+1) + (cutHalf d+1) then bankPairsAt F banks h' T S
    else []).findSome? ((recoveringPlan F FP).attempt T S) = _
  rw [dif_pos h]
  exact findSome?_congr' _ (fun b _ =>
    (comparisonPlan_attempt F (CellPreparation.recoveringPairAttempt F FP) _ _ b).trans (dif_pos h))

theorem searchBank_none_iff (FP : FieldPresentation K) {d n : ℕ}
    (h : d = (cutHalf d+1) + (cutHalf d+1)) (T S : Tensor K d n) :
    search (comparePlanFromBanks F banks FP) T S = none ↔
      search (recoveringPlan F FP) T S = none := by
  rw [search_eq_findSome?_bankPairsAt F banks FP h T S]
  let A : PairAttempt K := CellPreparation.recoveringPairAttempt F FP
  have hraw : search (recoveringPlan F FP) T S =
      (pairsAt F (cutHalf d) h T S).findSome? (attemptAt A (cutHalf d) h T S) := by
    change search (comparisonPlan F A) T S = _
    unfold search
    rw [comparisonPlan_enumerate, dif_pos h]
    exact findSome?_congr' _ (fun b _ => (comparisonPlan_attempt F A _ _ b).trans (dif_pos h))
  rw [hraw]
  simp only [List.findSome?_eq_none_iff, mem_bankPairsAt, A]

/-- The raw comparison callback emitted by a scan of the native banks. -/
def comparePreBankZ (words : List ℕ) : List ℕ :=
  0 :: packSegments (match decodePair F words with
    | none => []
    | some p =>
      if h : p.d = (cutHalf p.d+1) + (cutHalf p.d+1) then
        (bankPairsAt F banks h p.source p.target).map
          (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n => pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2)))
      else [])

theorem compareWords_eq_bankScan (FP : FieldPresentation K) :
    compareWords F (comparePlanFromBanks F banks FP) =
      selectPacked ∘ mapZ (positiveCallback
        (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) ∘
        comparePreBankZ F banks := by
  funext words
  let A : PairAttempt K := CellPreparation.recoveringPairAttempt F FP
  let cb := preparedAttemptWords F A
  let requests := match decodePair F words with
    | none => []
    | some p =>
      if h : p.d = (cutHalf p.d+1) + (cutHalf p.d+1) then
        (bankPairsAt F banks h p.source p.target).map
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
  change compareWords F (comparePlanFromBanks F banks FP) words =
    selectPacked (mapZ (positiveCallback cb) (0 :: packSegments requests))
  rw [hs]
  unfold compareWords
  cases hp : decodePair F words with
  | none => simp [requests, hp]
  | some p =>
    have h := decodePair_balanced hp
    simp only [requests,hp,dif_pos h]
    rw [search_eq_findSome?_bankPairsAt F banks FP h, List.map_map, List.findSome?_map]
    have hf := findSome?_congr' (f := okW ∘ cb ∘
      (fun b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n =>
        pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2))))
      (g := fun b => (attemptAt A (cutHalf p.d) h p.source p.target b).map
        (fun g => transporterOutput F g ((Fintype.card K-1)^(p.d-1))))
      (bankPairsAt F banks h p.source p.target)
      (fun b _ => by
        simp only [Function.comp_apply,cb]
        rw [preparedAttemptWords_encoded F A words p hp h b, okW_attemptOutput])
    rw [hf, findSome?_option_map]
    change (match (bankPairsAt F banks h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) with
      | none => [0]
      | some g => transporterOutput F g ((Fintype.card K-1)^(p.d-1))) = _
    cases (bankPairsAt F banks h p.source p.target).findSome? (attemptAt A (cutHalf p.d) h p.source p.target) <;> rfl

theorem turingPolytime_compareBanks (FP : FieldPresentation K)
    (hPrepare : TuringPolytime (comparePreBankZ F banks))
    (hAttempt : TuringPolytime (preparedAttemptWords F (CellPreparation.recoveringPairAttempt F FP))) :
    TuringPolytime (compareWords F (comparePlanFromBanks F banks FP)) := by
  rw [compareWords_eq_bankScan]
  exact turingPolytime_comp (turingPolytime_comp hPrepare
    (turingPolytime_mapZ (positiveCallback_turingPolytime hAttempt))) selectPacked_turingPolytime

#print axioms searchBank_none_iff
#print axioms compareWords_eq_bankScan
#print axioms turingPolytime_compareBanks

end EvenTI.P12Compare
