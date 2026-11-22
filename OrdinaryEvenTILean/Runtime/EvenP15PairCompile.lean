import EvenP15Totalizer
import EvenP15GuardedBinary
import EvenP12ComparePrepPairPlan

set_option autoImplicit false

namespace EvenTI.P15Execution

open EvenTI.Contract EvenTI.P10Words EvenTI.P12ComparePrep
open Lax51.TuringPolytime Lax51.BinaryWordEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPPartialCompiler20261001 (RamPolytimeOn)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem comparePre_time_of_partialBinary (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (callback : List ℕ → List ℕ) (hCallback : TuringPolytime callback)
    (hExact : ∀ x, (decodePair D x).isSome = true → callback x = comparePrePairsZ D pairs x) :
    TuringPolytime (comparePrePairsZ D pairs) := by
  have ht := guardedBinary_time (pairValid_time D) hCallback
  convert ht using 1
  funext x
  cases hx : decodePair D x with
  | none =>
    have hv : denseValid (Fintype.card K) 2 x = false := by rw [denseValid_eq_isSome D x,hx] <;> rfl
    simp [denseValidWords,hv,comparePrePairsZ,hx,EvenTI.P10Oracle.packSegments]
  | some p =>
    have hv : denseValid (Fintype.card K) 2 x = true := by rw [denseValid_eq_isSome D x,hx] <;> rfl
    have hOut := hExact x (by rw [hx] <;> rfl)
    simp [denseValidWords,hv,hOut]

/-- The physical trial producer can certify its runs just on well-formed
pairs. The compiled guard supplies the exact rejection for every other word list. -/
theorem comparePrePairsZ_time_of_ramOn (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (h : RamPolytimeOn (fun x => (decodePair D x).isSome = true) (comparePrePairsZ D pairs)) :
    TuringPolytime (comparePrePairsZ D pairs) := by
  obtain ⟨callback,hCallback,hExact⟩ := totalBinary_of_ramOn h
  exact comparePre_time_of_partialBinary D pairs callback hCallback hExact

theorem comparePrePairsZ_time_of_wordRuns (D : FieldEncoding K) (pairs : BalancedTrialPairs K)
    (c : Com) (B T : Polynomial ℕ)
    (h : ∀ w : List ℕ, (decodePair D w).isSome = true → ∃ (ext : String → ℕ) (s : Env),
      Run (B.eval (bitSize w)) c (initEnv ext (w.length::w)) s (T.eval (bitSize w)) ∧
      s.out = comparePrePairsZ D pairs w) : TuringPolytime (comparePrePairsZ D pairs) := by
  obtain ⟨callback,hCallback,hExact⟩ := totalBinary_of_boundedWordRuns _ _ c B T h
  exact comparePre_time_of_partialBinary D pairs callback hCallback hExact

#print axioms comparePrePairsZ_time_of_ramOn
#print axioms comparePrePairsZ_time_of_wordRuns
end EvenTI.P15Execution