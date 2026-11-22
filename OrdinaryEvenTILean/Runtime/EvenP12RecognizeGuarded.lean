import EvenP12RecognizeAssembly

set_option autoImplicit false

namespace EvenTI.P12Guard

open Lax51.TuringPolytime
open EvenTI.Contract EvenTI.Headline
open Mathproof.EvenTI.P9Recognizer
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The scalar machine may implement a cheaper fallback on inputs the
spectral test rejects. The compiled guard never calls it on those inputs. -/
theorem liveRecognize_time_of_guarded (F : FieldEncoding K) (FP : FieldPresentation K)
    {scalar : List Nat → List Nat}
    (hSpectral : TuringPolytime (recognizeWords F (LiveSpectral.spectralExec F)))
    (hScalar : TuringPolytime scalar)
    (hAgree : ∀ w, recognizeWords F (LiveSpectral.spectralExec F) w = [1] →
      scalar w = recognizeWords F (liveScalarExec F FP) w) :
    TuringPolytime (recognizeWords F (execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))) := by
  rw [recognizeWords_distribution]
  have h : gateConj (recognizeWords F (LiveSpectral.spectralExec F)) (recognizeWords F (liveScalarExec F FP)) =
      gateConj (recognizeWords F (LiveSpectral.spectralExec F)) scalar := by
    funext w
    by_cases he : recognizeWords F (LiveSpectral.spectralExec F) w = [1]
    · simp only [gateConj, hAgree w he]
    · simp only [gateConj, he, false_and, if_false]
  rw [h]
  exact gateConj_time hSpectral hScalar

#print axioms liveRecognize_time_of_guarded
end EvenTI.P12Guard
