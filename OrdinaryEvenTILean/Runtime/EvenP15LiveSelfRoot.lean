import EvenP15ExecutionRoot
import EvenP12CountPostClassify

set_option autoImplicit false

namespace EvenTI.P15Execution

open EvenTI.Contract EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Scalar
open EvenTI.P14Preparation EvenTI.P12Guard EvenTI.Headline
open EvenTI.P12CountPost (indicatorWords indicatorWords_turingPolytime)
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The scalar callback is consulted on actual prepared self requests for
sources that pass the spectral gate. This is its full required domain. -/
def OnSpectralSelfRequests (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (run : List ℕ → List ℕ) : Prop :=
  ∀ w, recognizeWords D (LiveSpectral.spectralExec D) w = [1] →
    ∀ x ∈ preparedPairRequests D pairs (selfPairWords w),
      run x = [1] ↔ preparedSelfWords D F (Fintype.equivFin Kˣ).symm x = [1]

private theorem indicator_accepts (w : List ℕ) : indicatorWords w = [1] ↔ w = [1] := by
  by_cases h : w = [1] <;> simp [indicatorWords,h]

/-- Compile the scalar scan with an arbitrary certified callback. Normalizing
its one-bit response allows any behavior away from the actual requests. -/
theorem liveRecognize_time_of_liveOffers (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (hExact : ExactRawTrialPairs D pairs)
    (pre : TuringPolytime (comparePrePairsZ D pairs))
    (hSpectral : TuringPolytime (recognizeWords D (LiveSpectral.spectralExec D)))
    (cb : List ℕ → List ℕ) (hcbTime : TuringPolytime cb)
    (hcb : OnSpectralSelfRequests D F pairs cb) :
    TuringPolytime (recognizeWords D
      (Mathproof.EvenTI.P9Recognizer.execAccept (LiveSpectral.spectralExec D) (liveScalarExec D F))) := by
  let normalized := indicatorWords ∘ cb
  have hb : TuringPolytime normalized := turingPolytime_comp hcbTime indicatorWords_turingPolytime
  have hB (x : List ℕ) : normalized x = [0] ∨ normalized x = [1] := by
    by_cases h : cb x = [1] <;> simp [normalized,indicatorWords,h]
  have hComb := turingPolytime_comp selfPairWords_turingPolytime pre
  have hFrames : TuringPolytime (fun w => packSegments ([] :: preparedPairRequests D pairs (selfPairWords w))) := by
    convert hComb using 1
    funext w
    exact (comparePrePairsZ_pack D pairs (selfPairWords w)).symm
  have hSelf := packedTrialsAll_time hFrames hb hB
  apply liveRecognize_time_of_guarded D F hSpectral hSelf
  intro w hw
  rw [← providedScalarWords_exact D F pairs hExact w hw]
  unfold providedScalarWords
  have he : ((preparedPairRequests D pairs (selfPairWords w)).all
      (fun x => decide (normalized x = [1]))) =
      ((preparedPairRequests D pairs (selfPairWords w)).all
      (fun x => decide (preparedSelfWords D F (Fintype.equivFin Kˣ).symm x = [1]))) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true,List.all_eq_true]
    refine forall_congr' fun x => ?_
    refine imp_congr_right fun hx => ?_
    rw [decide_eq_true_eq,decide_eq_true_eq]
    exact (indicator_accepts (cb x)).trans (hcb w hw x hx)
  rw [he]

#print axioms liveRecognize_time_of_liveOffers
end EvenTI.P15Execution