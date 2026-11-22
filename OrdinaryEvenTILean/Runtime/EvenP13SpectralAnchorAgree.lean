import EvenP13SpectralAnchorMachine
import EvenP13SpectralRoute
import EvenP13SharedTrialRuntime

set_option autoImplicit false

namespace EvenTI.P13Spectral

open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.P10Scan EvenTI.P10Oracle
open Lax51.TuringPolytime
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem17RepeatedBudget (repeatedBudget)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem anchorWordResult_on_numbered (D : FieldEncoding K) (A : NumberedAnchor K) :
    anchorWordResult D (numberedAnchorWords D A) = [storedAnchorExponent D A] := by
  obtain ⟨n,M⟩ := A
  cases n with
  | zero =>
    simp [anchorWordResult,numberedAnchorWords,storedAnchorExponent_eq,
      Matrix.charpoly_isEmpty,repeatedBudget]
  | succ n =>
    let A : NumberedAnchor K := numeric M
    let xs := (numberedAnchorWords D A).drop 1
    have hwords : numberedAnchorWords D A = (n+1)::xs := rfl
    have hlen : xs.length = (n+1)*(n+1) := by simp [xs,numberedAnchorWords,A,numeric] <;> ring
    have hval : ∀ a ∈ xs, a < Fintype.card K := by
      intro a ha
      simp only [xs,numberedAnchorWords,List.drop_succ_cons,List.drop_zero,List.mem_ofFn] at ha
      obtain ⟨i,rfl⟩ := ha
      exact (D _).isLt
    change anchorWordResult D (numberedAnchorWords D A) = [storedAnchorExponent D A]
    have hm := readAnchorMatrix_encoded D A
    rw [hwords] at hm ⊢
    have hd : xs.all (fun a => decide (a < Fintype.card K)) = true := by
      simp only [List.all_eq_true,decide_eq_true_eq]
      exact hval
    have shape : (0 < n+1 ∧ xs.length = (n+1)*(n+1)) ∧
        xs.all (fun a => decide (a < Fintype.card K)) = true := ⟨⟨by omega,hlen⟩,hd⟩
    have hm' : readAnchorMatrix D (n+1) ((n+1)::xs) = M := hm
    simp only [anchorWordResult,if_pos shape,hm'] <;> rfl

theorem recognizeSpectral_time_of_paid_trial_requests (D : FieldEncoding K) (F : FieldPresentation K)
    (hq : 2 ≤ Fintype.card K)
    (hRequests : TuringPolytime (fun w => packSegments ([] :: requestTrials D w))) :
    TuringPolytime (recognizeWords D (EvenTI.LiveSpectral.spectralExec D)) :=
  recognizeSpectral_time_of_requests D (anchorWordResult D) hq
    (anchorWordResult_turingPolytime D F) (anchorWordResult_on_numbered D) hRequests

#print axioms anchorWordResult_on_numbered
#print axioms recognizeSpectral_time_of_paid_trial_requests
end EvenTI.P13Spectral

namespace EvenTI.Headline

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.P12Scalar EvenTI.P13Spectral
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.TuringPolytime

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The exact binary anchor computation is supplied by the compiled
matrix recognizer. All trial consumers reuse the same native producer. -/
noncomputable def solverOfPaidTrialCallbacks (D : FieldEncoding K) (F : FieldPresentation K)
    (banks : ∀ {a b n : Nat} (T : Tensor K (a+b) n), CompleteCutBanks T)
    (hProjection : TuringPolytime spectralPairRequest)
    (hPrepare : TuringPolytime (comparePreBankZ D banks))
    (hScalar : TuringPolytime (preparedSelfWords D F (Fintype.equivFin Kˣ).symm))
    (hRecover : TuringPolytime (preparedAttemptWords D (CellPreparation.recoveringPairAttempt D F))) :
    VerifiedSolver D :=
  solverOfSharedTrialRuntime D F banks (anchorWordResult D) (anchorWordResult_on_numbered D)
    (anchorWordResult_turingPolytime D F) hProjection hPrepare hScalar hRecover

#print axioms solverOfPaidTrialCallbacks
end EvenTI.Headline
