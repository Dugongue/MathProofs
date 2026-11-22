import EvenP12ScalarDriver
import EvenP12ScalarSpectralRank

namespace EvenTI.P12Scalar

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.CellPreparation EvenTI.Headline EvenTI.P10Oracle EvenTI.P10Scan
open EvenTI.P12Compare EvenTI.P12Guard
open Mathproof.EvenTI.GlobalCoverage
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem castDense_spectral {d l n : ℕ} (T : Tensor K d n)
    (h : d = (l+1)+(l+1)) (hs : sourceSpectralAccepted T) :
    sourceSpectralAccepted (castDense l h T) := by
  subst d
  simpa [castDense] using hs

/-- The retained-rank predicate is already true whenever the actual
spectral word recognizer passes. Its separate physical program is unnecessary. -/
theorem retainedGateWords_on_spectral (F : FieldEncoding K) (w : List ℕ)
    (hw : recognizeWords F (LiveSpectral.spectralExec F) w = [1]) :
    retainedGateWords F w = [1] := by
  cases hp : decodeSource F w with
  | none => simp [recognizeWords,hp] at hw
  | some p =>
    have hbit : LiveSpectral.spectralExec F p.tensor = true := by
      by_contra h
      simp [recognizeWords,hp,h] at hw
    have hs := (LiveSpectral.spectralExec_agrees F p.tensor).mp hbit
    have hn : 0 < p.n := by
      rcases hs with ⟨_,h,_⟩ | ⟨_,_,_,h,_⟩ <;> omega
    have hh := decodePair_selfPairWords F w p hp
    have h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1) :=
      decodePair_balanced (p := ⟨p.d,p.n,p.tensor,p.tensor⟩) hh
    have hr := retainedFullRank_of_spectral (castDense (cutHalf p.d) h p.tensor)
      (castDense_spectral _ h hs)
    simp only [retainedGateWords,recognizeWords,hp,retainedGate,dif_pos h,
      rawRankGuard_eq_rank _ hn,hr,if_true]

/-- No retained-rank machine is assumed. The binary recognizer follows from
the three physical paths that it actually uses. -/
theorem liveRecognize_of_native_scalar_spectral (F : FieldEncoding K) (FP : FieldPresentation K)
    (banks : ∀ {a b n : ℕ} (T : Tensor K (a+b) n), CompleteCutBanks T)
    (hSpectral : TuringPolytime (recognizeWords F (LiveSpectral.spectralExec F)))
    (hRequests : TuringPolytime (comparePreBankZ F banks))
    (hTrial : TuringPolytime (preparedSelfWords F FP (Fintype.equivFin Kˣ).symm)) :
    TuringPolytime (recognizeWords F
      (Mathproof.EvenTI.P9Recognizer.execAccept (LiveSpectral.spectralExec F) (liveScalarExec F FP))) := by
  let provide : TrialProvider K := fun {l n} T => prepareFromBanks F banks (l := l) (n := n) T
  have hPrep : TuringPolytime (fun w => packSegments ([] :: selfRequests F provide w)) := by
    have he : (fun w => packSegments ([] :: selfRequests F provide w)) =
        comparePreBankZ F banks ∘ selfPairWords := funext (bankSelfRequests_eq F banks)
    rw [he]
    exact turingPolytime_comp selfPairWords_turingPolytime hRequests
  let scalar := fun w =>
    if selfChecksBit F FP (Fintype.equivFin Kˣ).symm provide w then [1] else [0]
  have hScalar : TuringPolytime scalar :=
    packedTrialsAll_time hPrep hTrial (preparedSelfWords_bit F FP _)
  apply liveRecognize_time_of_guarded F FP hSpectral hScalar
  intro w hw
  have he := scalarDriver_agrees_on_spectral F FP provide (fun _ => [1])
    (mem_prepareFromBanks F banks) (fun w h => (retainedGateWords_on_spectral F w h).symm) w hw
  by_cases hb : selfChecksBit F FP (Fintype.equivFin Kˣ).symm provide w = true
  · simpa [scalarDriver,gateConj,scalar,hb] using he
  · simpa [scalarDriver,gateConj,scalar,hb] using he

#print axioms retainedGateWords_on_spectral
#print axioms liveRecognize_of_native_scalar_spectral

end EvenTI.P12Scalar
