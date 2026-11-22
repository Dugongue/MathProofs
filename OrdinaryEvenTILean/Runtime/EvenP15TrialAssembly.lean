import EvenP15TrialBinary
import EvenP15GuardedBinary
import EvenP12ComparePrepTrialProvider

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace EvenTI.P15Trial

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P12ComparePrep EvenTI.P10Words
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

abbrev SideTrials (K : Type) [Field K] [DecidableEq K] :=
  ∀ {d n : ℕ}, d = (cutHalf d+1)+(cutHalf d+1) → Tensor K d n → Tensor K d n →
    Bool → List (PreparedTrial K (cutHalf d) n)

def sideProduct (sides : SideTrials K) : BalancedTrialPairs K :=
  fun h T S => (sides h T S false).product (sides h T S true)

def sideFrameWords (D : FieldEncoding K) (sides : SideTrials K) (w : List ℕ) : List ℕ :=
  match decodePair D w with
  | none => []
  | some p =>
    if h : p.d=(cutHalf p.d+1)+(cutHalf p.d+1)
    then trialInputFrame w ((sides h p.source p.target false).map (preparedTrialWords D))
      ((sides h p.source p.target true).map (preparedTrialWords D))
    else []

theorem sideProduct_exact (D : FieldEncoding K) (sides : SideTrials K)
    (hSide : ∀ {d n : ℕ} (h : d=(cutHalf d+1)+(cutHalf d+1))
      (T S : Tensor K d n) (target : Bool) (p : PreparedTrial K (cutHalf d) n),
      p ∈ sides h T S target ↔ p ∈ prepareTrials D (castDense (cutHalf d) h (if target then S else T))) :
    ExactRawTrialPairs D (sideProduct sides) := by
  intro d n h T S p
  obtain ⟨P,Q⟩ := p
  exact List.mem_product.trans ((and_congr (hSide h T S false P) (hSide h T S true Q)).trans List.mem_product.symm)

private theorem encode_sideProduct (D : FieldEncoding K) {l n : ℕ} (w : List ℕ)
    (xs ys : List (PreparedTrial K l n)) :
    requestWords w (xs.map (preparedTrialWords D)) (ys.map (preparedTrialWords D)) =
      packSegments ([]::(xs.product ys).map
        (fun b => pairW w (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2)))) := by
  have h := product_map_map (preparedTrialWords D) (preparedTrialWords D) xs ys
  unfold requestWords
  change packSegments ([]::(((xs.map (preparedTrialWords D)).product (ys.map (preparedTrialWords D))).map _))=_
  rw [show ((xs.map (preparedTrialWords D)).product (ys.map (preparedTrialWords D))) =
    (xs.product ys).map (Prod.map (preparedTrialWords D) (preparedTrialWords D)) from h]
  simp only [List.map_map,Function.comp_def,Prod.map_fst,Prod.map_snd,preparedComparisonRequest]

/-- The binary serializer lifts the two completed per-side payload lists
to exactly the original comparison callback, including its malformed-input
return. The caller supplies only production of the frame before serialization. -/
theorem comparePrePairsZ_time_of_sideFrame (D : FieldEncoding K) (sides : SideTrials K)
    (frame : TuringPolytime (sideFrameWords D sides)) :
    TuringPolytime (comparePrePairsZ D (sideProduct sides)) := by
  obtain ⟨g,hg,hExact⟩ := serializedTrialRequests_binary
  have h := EvenTI.P15Execution.guardedBinary_time (pairValid_time D)
    (turingPolytime_comp frame hg)
  convert h using 1
  funext w
  rw [comparePrePairsZ_pack]
  cases he : decodePair D w with
  | none =>
    simp [preparedPairRequests,he,denseValidWords,denseValid_eq_isSome D,packSegments,positiveWords]
  | some p =>
    have hb := decodePair_balanced he
    simp only [preparedPairRequests,he,dif_pos hb,sideProduct,denseValidWords,denseValid_eq_isSome D,
      Option.isSome_some,if_true,if_pos rfl,Function.comp_apply,sideFrameWords,hExact]
    exact (encode_sideProduct D w (sides hb p.source p.target false) (sides hb p.source p.target true)).symm

#print axioms sideProduct_exact
#print axioms comparePrePairsZ_time_of_sideFrame
end EvenTI.P15Trial
