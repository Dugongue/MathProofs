import EvenP12ScalarSemantics
import EvenP12ScalarPackedAll
import EvenP12RecognizeGuarded
import EvenP12CompareNativeScan

namespace EvenTI.P12Scalar

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.CellPreparation EvenTI.Headline EvenTI.P10Oracle EvenTI.P10Scan
open EvenTI.P12Compare EvenTI.P12Guard
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

set_option autoImplicit false
set_option maxHeartbeats 650000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

abbrev TrialProvider (K : Type) [Field K] [DecidableEq K] :=
  ∀ {l n : ℕ}, Dense K l n → List (PreparedTrial K l n)

def rawRankGuard {l n : ℕ} (T : Dense K l n) : Bool :=
  decide (T ≠ 0) && rawRetainedFullRank (l := (l+1)+l) T

theorem rawRankGuard_eq_rank {l n : ℕ} (T : Dense K l n) (hn : 0 < n) :
    rawRankGuard T = rawRetainedFullRank (l := (l+1)+l) T := by
  unfold rawRankGuard
  cases h : rawRetainedFullRank (l := (l+1)+l) T
  · simp
  · have hne : T ≠ 0 := by
      intro hT
      have hr := (rawRetainedFullRank_spec T).mp h 0
      rw [hT] at hr
      have he : retainedForm (K := K) (d := (l+1)+l) (n := n) 0 0 = 0 := by
        ext i j
        rfl
      rw [he,Matrix.rank_zero] at hr
      omega
    simp [hne]

def retainedGate {d n : ℕ} (T : Tensor K d n) : Bool :=
  if h : d = (cutHalf d+1)+(cutHalf d+1) then rawRankGuard (castDense (cutHalf d) h T)
  else false

def retainedGateWords (F : FieldEncoding K) : List ℕ → List ℕ := recognizeWords F retainedGate

def selfRequests (F : FieldEncoding K) (provide : TrialProvider K) (w : List ℕ) : List (List ℕ) :=
  let input := selfPairWords w
  match decodePair F input with
  | none => []
  | some p =>
    if h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) then
      ((provide (castDense (cutHalf p.d) h p.source)).product
        (provide (castDense (cutHalf p.d) h p.target))).map
        (fun b => pairW input (pairW (preparedTrialWords F b.1) (preparedTrialWords F b.2)))
    else []

theorem bankSelfRequests_eq (F : FieldEncoding K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T) (w : List ℕ) :
    packSegments ([] :: selfRequests F (prepareFromBanks F banks) w) =
      comparePreBankZ F banks (selfPairWords w) := by
  rfl

theorem trialSelfRequests_eq (F : FieldEncoding K) (w : List ℕ) :
    packSegments ([] :: selfRequests F (prepareTrials F) w) = comparePreZ F (selfPairWords w) := by
  cases hp : decodePair F (selfPairWords w) with
  | none => simp [selfRequests,comparePreZ,hp,pairWords_none F _ hp,packSegments,positiveWords]
  | some p =>
    have h := decodePair_balanced hp
    simp only [selfRequests, hp, dif_pos h, comparePreZ, pairWords_eq F _ hp h,
      List.map_map, Function.comp_def,pairsAt]
    rfl

private theorem all_same_members {A : Type} (s t : List A) (f : A → Bool)
    (hm : ∀ a, a ∈ s ↔ a ∈ t) :
    s.all f = t.all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, hm]

theorem checkScalarOnDense_eq_provider (F : FieldEncoding K) (FP : FieldPresentation K)
    {q l n : ℕ} (enum : Fin q ≃ Kˣ) (provide : TrialProvider K)
    (hMem : ∀ {a b : ℕ} (T : Dense K a b) (P : PreparedTrial K a b),
      P ∈ provide T ↔ P ∈ prepareTrials F T) (T : Dense K l n) :
    checkScalarOnDense F FP enum T =
      (rawRankGuard T && ((provide T).product (provide T)).all
        (fun b => checkSelfPair F FP enum T b.1 b.2)) := by
  rw [checkScalarOnDense_eq_product]
  change (rawRankGuard T && _) = (rawRankGuard T && _)
  apply congrArg ((rawRankGuard T) && ·)
  apply all_same_members
  rintro ⟨b₁,b₂⟩
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := List.mem_product.mp h
    exact List.mem_product.mpr ⟨(hMem T b₁).mpr h₁,(hMem T b₂).mpr h₂⟩
  · intro h
    obtain ⟨h₁,h₂⟩ := List.mem_product.mp h
    exact List.mem_product.mpr ⟨(hMem T b₁).mp h₁,(hMem T b₂).mp h₂⟩

noncomputable def selfChecksBit (F : FieldEncoding K) (FP : FieldPresentation K)
    {q : ℕ} (enum : Fin q ≃ Kˣ) (provide : TrialProvider K) (w : List ℕ) : Bool :=
  (selfRequests F provide w).all (fun x => decide (preparedSelfWords F FP enum x = [1]))

theorem selfChecksBit_exact (F : FieldEncoding K) (FP : FieldPresentation K)
    {q : ℕ} (enum : Fin q ≃ Kˣ) (provide : TrialProvider K) (w : List ℕ)
    (p : ParsedSource K) (hp : decodeSource F w = some p)
    (h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1)) :
    selfChecksBit F FP enum provide w =
      let T := castDense (cutHalf p.d) h p.tensor
      ((provide T).product (provide T)).all (fun b => checkSelfPair F FP enum T b.1 b.2) := by
  have hh := decodePair_selfPairWords F w p hp
  simp only [selfChecksBit,selfRequests,hh,dif_pos h,List.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro b
  apply imp_congr_right
  intro _
  simp only [Function.comp_apply, decide_eq_true_eq]
  rw [preparedSelfWords_encode F FP enum _ ⟨p.d,p.n,p.tensor,p.tensor⟩ hh h]
  cases checkSelfPair F FP enum (castDense (cutHalf p.d) h p.tensor) b.1 b.2 <;> simp

noncomputable def scalarDriver (F : FieldEncoding K) (FP : FieldPresentation K)
    (provide : TrialProvider K) (rankWords : List ℕ → List ℕ) : List ℕ → List ℕ :=
  gateConj rankWords (fun w =>
    if selfChecksBit F FP (Fintype.equivFin Kˣ).symm provide w then [1] else [0])

theorem scalarDriver_agrees_on_spectral (F : FieldEncoding K) (FP : FieldPresentation K)
    (provide : TrialProvider K) (rankWords : List ℕ → List ℕ)
    (hMem : ∀ {a b : ℕ} (T : Dense K a b) (P : PreparedTrial K a b),
      P ∈ provide T ↔ P ∈ prepareTrials F T)
    (hRank : ∀ w, recognizeWords F (LiveSpectral.spectralExec F) w = [1] →
      rankWords w = retainedGateWords F w)
    (w : List ℕ) (hw : recognizeWords F (LiveSpectral.spectralExec F) w = [1]) :
    scalarDriver F FP provide rankWords w = recognizeWords F (liveScalarExec F FP) w := by
  cases hp : decodeSource F w with
  | none => simp [recognizeWords,hp] at hw
  | some p =>
    have hh := decodePair_selfPairWords F w p hp
    have h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) :=
      decodePair_balanced (p := ⟨p.d,p.n,p.tensor,p.tensor⟩) hh
    rw [scalarDriver,gateConj,hRank w hw,selfChecksBit_exact F FP _ provide w p hp h]
    simp only [retainedGateWords,recognizeWords,hp,retainedGate,liveScalarExec,dif_pos h]
    rw [checkScalarOnDense_eq_provider F FP _ provide hMem]
    cases rawRankGuard (castDense (cutHalf p.d) h p.tensor)
    · simp
    · simp only [if_true, true_and, Bool.true_and]
      split <;> simp_all only [if_true,if_false,List.cons.injEq,Nat.zero_ne_one,and_true]

theorem scalarDriver_turingPolytime (F : FieldEncoding K) (FP : FieldPresentation K)
    (provide : TrialProvider K) {rankWords : List ℕ → List ℕ}
    (hRequests : TuringPolytime (fun w => packSegments ([] :: selfRequests F provide w)))
    (hTrial : TuringPolytime (preparedSelfWords F FP (Fintype.equivFin Kˣ).symm))
    (hRank : TuringPolytime rankWords) :
    TuringPolytime (scalarDriver F FP provide rankWords) := by
  apply gateConj_time hRank
  exact packedTrialsAll_time hRequests hTrial (preparedSelfWords_bit F FP _)

theorem liveRecognize_of_native_scalar_calls (F : FieldEncoding K) (FP : FieldPresentation K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T)
    {rankWords : List ℕ → List ℕ}
    (hSpectral : TuringPolytime (recognizeWords F (LiveSpectral.spectralExec F)))
    (hRequests : TuringPolytime (comparePreBankZ F banks))
    (hTrial : TuringPolytime (preparedSelfWords F FP (Fintype.equivFin Kˣ).symm))
    (hRank : TuringPolytime rankWords)
    (hRankExact : ∀ w, recognizeWords F (LiveSpectral.spectralExec F) w = [1] →
      rankWords w = retainedGateWords F w) :
    TuringPolytime (recognizeWords F
      (Mathproof.EvenTI.P9Recognizer.execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))) := by
  have hPrep : TuringPolytime (fun w => packSegments ([] :: selfRequests F (prepareFromBanks F banks) w)) := by
    rw [funext (bankSelfRequests_eq F banks)]
    exact turingPolytime_comp (f := selfPairWords) (g := comparePreBankZ F banks)
      selfPairWords_turingPolytime hRequests
  exact liveRecognize_time_of_guarded F FP hSpectral
    (scalarDriver_turingPolytime F FP _ hPrep hTrial hRank)
    (scalarDriver_agrees_on_spectral F FP _ _ (mem_prepareFromBanks F banks) hRankExact)

#print axioms rawRankGuard_eq_rank
#print axioms selfChecksBit_exact
#print axioms scalarDriver_agrees_on_spectral
#print axioms liveRecognize_of_native_scalar_calls

end EvenTI.P12Scalar
