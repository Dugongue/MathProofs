import EvenP12ComparePrepPairPlan
import EvenP12ScalarSemantics
import EvenP13SpectralRoute

set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.PrimaryAlignment EvenTI.LiveSpectral EvenTI.P10Oracle EvenTI.P10Scan
open EvenTI.P12Scalar EvenTI.P13Spectral
open EvenTI.CellPreparation (originalChoiceCap)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def preparedAnchorBlocks (w : List ℕ) : List (List ℕ) :=
  unlistW (unpairW w.tail).1

@[simp] theorem preparedAnchorBlocks_encode (F : FieldEncoding K) {l n : ℕ}
    (p : PreparedTrial K l n) :
    preparedAnchorBlocks (preparedTrialWords F p) =
      (numberedAnchors p).map (numberedAnchorWords F) := by
  simp [preparedAnchorBlocks,preparedTrialWords]

/-- The higher-order cap is read from the dense pair length. This formula
avoids constructing an unbounded natural from unchecked callback headers. -/
def spectralPairRequest (w : List ℕ) : List ℕ :=
  let raw := (unpairW w).1
  let l := cutHalf (raw.headD 0)
  let n := (raw.drop 1).headD 0
  let source := (unpairW (unpairW w).2).1
  let available := (raw.drop 2).length / 2
  let cap := if l = 1 then min n available else available
  if (l=1 ∧ 5≤n) ∨ (2≤l ∧ 1≤n) then
    packSegments ([cap] :: preparedAnchorBlocks source)
  else []

def spectralPairAnswer (q : ℕ) (anchor : List ℕ → List ℕ) (w : List ℕ) : List ℕ :=
  anchorTrialRunner q anchor (spectralPairRequest w)

theorem spectralPairAnswer_time_of_route (q : ℕ) (anchor : List ℕ → List ℕ)
    (hq : 2 ≤ q) (hAnchor : TuringPolytime anchor)
    (hRoute : TuringPolytime spectralPairRequest) :
    TuringPolytime (spectralPairAnswer q anchor) := by
  have hMap := turingPolytime_comp hRoute (turingPolytime_mapZ (positiveCallback_turingPolytime hAnchor))
  have hCombined := turingPolytime_comp hMap (scoreWords_turingPolytime q hq)
  exact hCombined
theorem spectralPairAnswer_boolean (q : ℕ) (anchor : List ℕ → List ℕ) (w : List ℕ) :
    spectralPairAnswer q anchor w = [0] ∨ spectralPairAnswer q anchor w = [1] := by
  unfold spectralPairAnswer anchorTrialRunner
  simp only [Function.comp_apply]
  generalize mapZ (positiveCallback anchor) (spectralPairRequest w) = o
  cases o with
  | nil => exact Or.inl rfl
  | cons c tail =>
    cases tail with
    | nil => exact Or.inl rfl
    | cons z rem =>
      by_cases hb : q ^ anchorSum rem ≤ c-1
      · exact Or.inr (by simp [scoreWords,hb])
      · exact Or.inl (by simp [scoreWords,hb])

theorem spectralPairAnswer_encode (F : FieldEncoding K) (anchor : List ℕ → List ℕ)
    (ha : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A])
    {d n : ℕ} (rest : List ℕ) (p q : PreparedTrial K (cutHalf d) n)
    (h : d = (cutHalf d+1)+(cutHalf d+1)) (hN : 2 ≤ n) (hLen : rest.length = 2*n^d) :
    spectralPairAnswer (Fintype.card K) anchor
      (pairW (d::n::rest) (pairW (preparedTrialWords F p) (preparedTrialWords F q))) =
      if ((cutHalf d=1 ∧ 5≤n) ∨ (2≤cutHalf d ∧ 1≤n)) ∧
          Fintype.card K ^ storedTrialExponent F p ≤ originalChoiceCap (cutHalf d) n
      then [1] else [0] := by
  unfold spectralPairAnswer spectralPairRequest
  simp only [unpairW_pairW,List.headD_cons,List.drop_succ_cons,List.drop_zero,preparedAnchorBlocks_encode]
  have hd : rest.length / 2 = n^d := by omega
  have hn : n ≤ n^d := by
    simpa using Nat.pow_le_pow_right (show 0<n by omega) (show 1≤d by omega)
  have hCap : (if cutHalf d=1 then min n (rest.length/2) else rest.length/2) =
      originalChoiceCap (cutHalf d) n := by
    rw [hd, originalChoiceCap]
    split
    · exact min_eq_left hn
    · exact congrArg (fun d => n^d) h
  rw [hCap]
  split
  · rename_i hh
    by_cases hb : Fintype.card K ^ storedTrialExponent F p ≤ originalChoiceCap (cutHalf d) n <;>
      simpa only [hh,true_and,anchorPayload,hb,if_true,if_false] using anchorTrialRunner_answer F anchor ha p
  · rename_i hh
    simp [hh,anchorTrialRunner,mapZ,scoreWords]

def preparedPairRequests (F : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (words : List ℕ) : List (List ℕ) :=
  match decodePair F words with
  | none => []
  | some p =>
    if h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) then
      (pairs h p.source p.target).map
        (fun b => pairW words (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2)))
    else []

theorem comparePrePairsZ_pack (F : FieldEncoding K) (pairs : BalancedTrialPairs K) (w : List ℕ) :
    comparePrePairsZ F pairs w = packSegments ([] :: preparedPairRequests F pairs w) := rfl

/-- For shared recognition the comparison preprocessor must preserve
membership both ways. An arbitrary superset only guarantees comparison. -/
def ExactRawTrialPairs (F : FieldEncoding K) (pairs : BalancedTrialPairs K) : Prop :=
  ∀ {d n : ℕ} (h : d = (cutHalf d+1)+(cutHalf d+1))
    (T S : Tensor K d n) (b : PreparedTrial K (cutHalf d) n × PreparedTrial K (cutHalf d) n),
    b ∈ pairs h T S ↔ b ∈ pairsAt F (cutHalf d) h T S

private theorem decodePair_selfPairWords_none' (F : FieldEncoding K) (w : List ℕ)
    (hSrc : decodeSource F w = none) : decodePair F (selfPairWords w) = none := by
  cases hp : decodePair F (selfPairWords w) with
  | none => rfl
  | some p =>
    exfalso
    cases w with
    | nil => simp [selfPairWords,decodePair] at hp
    | cons d tail =>
      cases tail with
      | nil => simp [selfPairWords,decodePair] at hp
      | cons n xs =>
        change decodePair F (d::n::(xs++xs)) = some p at hp
        simp only [decodePair] at hp
        split at hp
        · rename_i h
          simp only [Bool.and_eq_true,decide_eq_true_eq,List.length_append,List.all_append] at h
          obtain ⟨⟨hh,hl⟩,hDigits,_⟩ := h
          simp only [admissibleHeader,decide_eq_true_eq] at hh
          obtain ⟨hD,hE,hN,_,_⟩ := hh
          have hd : d ≤ n^d := (Nat.lt_two_pow_self (n:=d)).le.trans (Nat.pow_le_pow_left hN _)
          have hn : n ≤ n^d := by
            simpa using Nat.pow_le_pow_right (show 0<n by omega) (show 1≤d by omega)
          have hL : xs.length = n^d := by omega
          have ha : admissibleHeader d n xs.length = true := by
            simp [admissibleHeader,hD,hE,hN,hL,hd,hn]
          rw [hL] at ha
          simp [decodeSource,ha,hL,hDigits] at hSrc
        · contradiction

theorem recognizeWords_eq_comparePreAny (F : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (hExact : ExactRawTrialPairs F pairs) (anchor : List ℕ → List ℕ)
    (ha : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A]) :
    recognizeWords F (spectralExec F) = fun w =>
      if [1] ∈ (preparedPairRequests F pairs (selfPairWords w)).map
        (spectralPairAnswer (Fintype.card K) anchor) then [1] else [0] := by
  funext w
  cases hs : decodeSource F w with
  | none =>
    simp [recognizeWords,hs,preparedPairRequests,decodePair_selfPairWords_none' F w hs]
  | some p =>
    have hp := decodePair_selfPairWords F w p hs
    have h := decodePair_balanced hp
    obtain ⟨raw,hr,hLen,_,_,hN⟩ := decodePair_some hp
    let l := cutHalf p.d
    let T := castDense l h p.tensor
    let shape : Prop := (l=1 ∧ 5≤p.n) ∨ (2≤l ∧ 1≤p.n)
    let test (x : PreparedTrial K l p.n) : Prop :=
      Fintype.card K ^ storedTrialExponent F x ≤ originalChoiceCap l p.n
    change selfPairWords w = p.d::p.n::raw at hr
    have hCb (b : PreparedTrial K l p.n × PreparedTrial K l p.n) :
        spectralPairAnswer (Fintype.card K) anchor
          (pairW (selfPairWords w) (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2))) =
          (if shape ∧ test b.1 then [1] else [0]) := by
      rw [hr]
      exact spectralPairAnswer_encode F anchor ha raw b.1 b.2 h hN hLen
    have hExists : (∃ b ∈ pairs h p.tensor p.tensor, shape ∧ test b.1) ↔
        shape ∧ ∃ t ∈ prepareTrials F T, test t := by
      constructor
      · rintro ⟨b,hb,hs,hb'⟩
        have hmem : b ∈ (prepareTrials F T).product (prepareTrials F T) :=
          (hExact h p.tensor p.tensor b).mp hb
        exact ⟨hs,b.1,(List.mem_product.mp hmem).1,hb'⟩
      · rintro ⟨hs,t,ht,ht'⟩
        refine ⟨(t,t),(hExact h p.tensor p.tensor (t,t)).mpr ?_,hs,ht'⟩
        exact List.mem_product.mpr ⟨ht,ht⟩
    have hAny :
        [1] ∈ (preparedPairRequests F pairs (selfPairWords w)).map
            (spectralPairAnswer (Fintype.card K) anchor) ↔
          shape ∧ ∃ t ∈ prepareTrials F T, test t := by
      simp only [preparedPairRequests, hp,dif_pos h,List.map_map,List.mem_map,Function.comp_def,hCb]
      refine (exists_congr fun b => and_congr_right fun _ => ?_).trans hExists
      by_cases hb : shape ∧ test b.1 <;> simp [hb]
    have hSpec : spectralExec F p.tensor = true ↔ shape ∧ ∃ t ∈ prepareTrials F T, test t := by
      have hb : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) := h
      rw [spectralExec,dif_pos hb]
      simp [spectralAt,trialSpectral,shape,T,l,test,List.any_eq_true]
    simp only [recognizeWords,hs]
    by_cases hs' : spectralExec F p.tensor = true
    · simp [hs',(hAny.trans hSpec.symm).mpr hs']
    · have hf : ¬ [1] ∈ (preparedPairRequests F pairs (selfPairWords w)).map
          (spectralPairAnswer (Fintype.card K) anchor) := fun hMem => hs' ((hAny.trans hSpec.symm).mp hMem)
      simp [hs',hf]

theorem recognizeSpectral_time_of_comparePre (F : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (hExact : ExactRawTrialPairs F pairs) (anchor : List ℕ → List ℕ)
    (ha : ∀ A : NumberedAnchor K, anchor (numberedAnchorWords F A) = [storedAnchorExponent F A])
    (hPre : TuringPolytime (comparePrePairsZ F pairs))
    (hScore : TuringPolytime (spectralPairAnswer (Fintype.card K) anchor)) :
    TuringPolytime (recognizeWords F (spectralExec F)) := by
  rw [recognizeWords_eq_comparePreAny F pairs hExact anchor ha]
  have hCombined := turingPolytime_comp selfPairWords_turingPolytime hPre
  have hFrames : TuringPolytime (fun w => packSegments ([] :: preparedPairRequests F pairs (selfPairWords w))) := by
    convert hCombined using 1
    funext w
    exact (comparePrePairsZ_pack F pairs (selfPairWords w)).symm
  exact EvenTI.P12Guard.packedTrialsAny_time hFrames hScore (spectralPairAnswer_boolean _ _)


def nativeBalancedTrialPairs (F : FieldEncoding K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), EvenTI.P12Compare.CompleteCutBanks T) :
    BalancedTrialPairs K :=
  fun {d n} h T S =>
    (EvenTI.P12Compare.prepareFromBanks F banks (castDense (cutHalf d) h T)).product
      (EvenTI.P12Compare.prepareFromBanks F banks (castDense (cutHalf d) h S))

theorem nativeBalancedTrialPairs_exact (F : FieldEncoding K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), EvenTI.P12Compare.CompleteCutBanks T) :
    ExactRawTrialPairs F (nativeBalancedTrialPairs F banks) := by
  intro d n h T S b
  obtain ⟨p,q⟩ := b
  unfold nativeBalancedTrialPairs pairsAt
  exact List.mem_product.trans ((and_congr
    (EvenTI.P12Compare.mem_prepareFromBanks F banks (castDense (cutHalf d) h T) p)
    (EvenTI.P12Compare.mem_prepareFromBanks F banks (castDense (cutHalf d) h S) q)).trans List.mem_product.symm)

theorem nativeBalancedTrialPairs_pre (F : FieldEncoding K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), EvenTI.P12Compare.CompleteCutBanks T) :
    comparePrePairsZ F (nativeBalancedTrialPairs F banks) = EvenTI.P12Compare.comparePreBankZ F banks := rfl
#print axioms preparedAnchorBlocks_encode
#print axioms recognizeWords_eq_comparePreAny
#print axioms recognizeSpectral_time_of_comparePre
end EvenTI.P12ComparePrep
