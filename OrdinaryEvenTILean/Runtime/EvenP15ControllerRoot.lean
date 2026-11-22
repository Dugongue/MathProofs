import EvenP15AlternativeAttempt
import EvenP15LiveSelfRoot
import EvenP15Totalizer

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P15Execution

open EvenTI.Action EvenTI.Contract EvenTI.Comparison EvenTI.TrialProducer
open EvenTI.P10Scan EvenTI.P10Oracle EvenTI.P12ComparePrep EvenTI.P12Compare EvenTI.P12Scalar
open EvenTI.P13Spectral EvenTI.P14Preparation EvenTI.Headline EvenTI.P12Guard
open Mathproof.EvenTI.GlobalCoverage Mathproof.EvenTI.P9Recognizer Mathproof.EvenTI.P9Root
open Lax51.TuringPolytime Lax51.BinaryWordEncoding
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18FieldPresentation20260930 (exists_fieldPresentation)
open Mathproof.Problem18IMPPartialCompiler20261001 (RamPolytimeOn)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Raw trial requests for which the comparison controller is invoked. -/
def RecoveryCall (D : FieldEncoding K) (pairs : BalancedTrialPairs K) (x : List ℕ) : Prop :=
  ∃ (w : List ℕ) (p : ParsedPair K), decodePair D w = some p ∧
    ∃ (h : p.d = (cutHalf p.d+1)+(cutHalf p.d+1))
      (b : PreparedTrial K (cutHalf p.d) p.n × PreparedTrial K (cutHalf p.d) p.n),
      b ∈ pairs h p.source p.target ∧
      x = pairW w (pairW (preparedTrialWords D b.1) (preparedTrialWords D b.2))

/-- Raw self requests for which the scalar controller is invoked. -/
def SpectralSelfCall (D : FieldEncoding K) (pairs : BalancedTrialPairs K) (x : List ℕ) : Prop :=
  ∃ w, recognizeWords D (LiveSpectral.spectralExec D) w = [1] ∧
    x ∈ preparedPairRequests D pairs (selfPairWords w)

/-- Fixed-field root with the actual polynomial producer and controllers.
The two controllers have correctness requirements on precisely the requests
used by the checked binary assembly. -/
noncomputable def solverOfLiveOffers (D : FieldEncoding K) (F : FieldPresentation K)
    (pairs : BalancedTrialPairs K) (hExact : ExactRawTrialPairs D pairs)
    (pre : TuringPolytime (comparePrePairsZ D pairs))
    (scalar : List ℕ → List ℕ) (scalarTime : TuringPolytime scalar)
    (scalarSpec : OnSpectralSelfRequests D F pairs scalar)
    (A : PairAttempt K) (hA : RecoveryRefines D F A)
    (recover : List ℕ → List ℕ) (recoverTime : TuringPolytime recover)
    (recoverSpec : OnTrialRequests D pairs A recover) : VerifiedSolver D := by
  let P := alternativeTrialPlan D pairs A
  let enum := (Fintype.equivFin Kˣ).symm
  have hScore := spectralPairAnswer_time_of_route (Fintype.card K) (anchorWordResult D)
    Fintype.one_lt_card (anchorWordResult_turingPolytime D F) EvenTI.P14Projection.spectralPairRequest_turingPolytime
  have hSpectral := recognizeSpectral_time_of_comparePre D pairs hExact (anchorWordResult D)
    (anchorWordResult_on_numbered D) pre hScore
  have hRec := liveRecognize_time_of_liveOffers D F pairs hExact pre hSpectral scalar scalarTime scalarSpec
  have hRec' : TuringPolytime (recognizeWords D (coverageAccept K)) :=
    recognizeWords_eq_of_guarded D (LiveSpectral.spectralExec_agrees D)
      (liveScalarExec_agrees D F (selfScanSound D F)) ▸ hRec
  have hCompare : TuringPolytime (compareWords D P) :=
    alternativeCompare_time D pairs A recover recoverSpec pre recoverTime
  have hPre := P12CountPre.countPreZ_turingPolytime_checked D P enum hCompare
  have hPost := P12CountPost.countPostZ_turingPolytime_of_compare D P enum hCompare
  exact assembleVerifiedSolver D (coverageAccept K) P enum
    (fun T g => (coverageAccept_invariant_iff).mpr (fun S a => sourceAccepted_act S a) T g)
    contract_uniformCoverage contract_higherOrderRate
    (fun hd he hn T S hT => by
      have h := (sourceAccept_eq_true T).mp hT
      exact ⟨h.2.1,alternativeTrialPlan_complete D F pairs (fun hc U V b hb => (hExact hc U V b).mpr hb)
        A hA hd he hn T S h,h.2.2⟩)
    hRec' hCompare
    (fun g hg => countWords_turingPolytime_of_zeroDelimited D P enum hPre hPost g hg)

/-- These are partial-correctness certificates for actual uniform RAM
programs. The verified clock supplies the unrestricted binary callbacks. -/
structure LiveControllerCertificates (D : FieldEncoding K) (F : FieldPresentation K) where
  pairs : BalancedTrialPairs K
  exactPairs : ExactRawTrialPairs D pairs
  pre : TuringPolytime (comparePrePairsZ D pairs)
  scalar : RamPolytimeOn (SpectralSelfCall D pairs) (preparedSelfWords D F (Fintype.equivFin Kˣ).symm)
  attempt : PairAttempt K
  attemptSpec : RecoveryRefines D F attempt
  recover : RamPolytimeOn (RecoveryCall D pairs) (preparedAttemptWords D attempt)

theorem verifiedSolver_of_liveControllers (D : FieldEncoding K) (F : FieldPresentation K)
    (e : LiveControllerCertificates D F) : Nonempty (VerifiedSolver D) := by
  obtain ⟨scalar,hs,hScalar⟩ := totalBinary_of_ramOn e.scalar
  obtain ⟨recover,hr,hRecover⟩ := totalBinary_of_ramOn e.recover
  refine ⟨solverOfLiveOffers D F e.pairs e.exactPairs e.pre scalar hs ?_ e.attempt e.attemptSpec recover hr ?_⟩
  · intro w hw x hx
    rw [hScalar x ⟨w,hw,hx⟩]
  · intro w p hp h b hb
    rw [hRecover _ ⟨w,p,hp,h,b,hb,rfl⟩]
    exact preparedAttemptWords_encoded D e.attempt w p hp h b

theorem fixedFieldEvenOrderTI_of_liveControllers
    (h : ∀ (L : Type) [Field L] [Fintype L] [DecidableEq L] (D : FieldEncoding L)
      (F : FieldPresentation L), Nonempty (LiveControllerCertificates D F)) : FixedFieldEvenOrderTI := by
  intro L _ _ D
  classical
  obtain ⟨F⟩ := exists_fieldPresentation (K := L)
  obtain ⟨e⟩ := h L D F
  exact verifiedSolver_of_liveControllers D F e

#print axioms solverOfLiveOffers
#print axioms verifiedSolver_of_liveControllers
#print axioms fixedFieldEvenOrderTI_of_liveControllers
end EvenTI.P15Execution