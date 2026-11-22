import EvenP14CutRunLift
import Mathproof.Meta.Problem18P36ClockedPartialTotalization20261004
import Mathproof.Meta.Problem18P36TaggedClockMachine20261004
import Mathproof.Meta.Problem18RootGuardedWordParser20261001
import Mathproof.Meta.Problem18P34Machine20261002Layout

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace EvenTI.P15Execution

open Turing Polynomial Lax51.BinaryWordEncoding Lax51.TuringPolytime
open Mathproof.Problem18EncodedTMComposition20261001
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18FiniteTransducer20261001
open Mathproof.Problem18RootWordCodec20261001 (fromRAM fromRAM_encode)
open Mathproof.Problem18RootGuardedWordParser20261001 (decodedWords decoderMachine decoder_roundtrip)
open Mathproof.Problem18IMPPartialCompiler20261001 (RamPolytimeOn ramPolytimeOn_of_bounded_imp)
open Mathproof.Problem18P36TaggedClockMachine20261004 (taggedMachine statusOutput)
open Mathproof.Problem18P36ClockTagEmitter20261004 (emitterMachine)
open Mathproof.Problem18P36ClockedRAMSemantics20261004 (simulationAfterFuel_eq_of_runsTo simulationSucceeded simulationRawOutput)
open Lax51Proofs.RamToTM (simulationWordWidth polynomial_eval_le_simpleMajorant ramSimulation_haltList)

inductive ClockWordState
  | first
  | failed
  | pass (seen : Bool)
  deriving Fintype, DecidableEq

private def clockWordNext : ClockWordState → Symbol → ClockWordState × List Bool
  | .first, .one => (.pass false, [])
  | .first, _ => (.failed, [])
  | .failed, _ => (.failed, [])
  | .pass s, a => let p := fromRAM.next s a; (.pass p.1,p.2)

private def clockWordFinish : ClockWordState → List Bool
  | .pass s => fromRAM.finish s
  | _ => []

/-- Parse the arbitrary status-bearing output of the checked bounded clock. -/
private def clockWordsBits : Transducer Symbol Bool ClockWordState where
  initial := .first
  next := clockWordNext
  finish := clockWordFinish
  next_bound s a := by cases s <;> cases a <;> simp [clockWordNext,fromRAM] <;> split <;> simp
  finish_bound s := by cases s <;> simp [clockWordFinish,fromRAM] <;> split <;> simp

private theorem clockWordsBits_pass (xs : List Symbol) (seen : Bool) :
    run clockWordsBits (.pass seen) xs = run fromRAM seen xs := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    change (fromRAM.next seen a).2 ++ run clockWordsBits (.pass (fromRAM.next seen a).1) xs = _
    rw [ih]
    rfl

private theorem clockWordsBits_encoded (xs : List ℕ) :
    run clockWordsBits .first (.one :: encode xs) = BitstringEncoding.bitEncode xs := by
  change run clockWordsBits (.pass false) (encode xs) = _
  rw [clockWordsBits_pass,fromRAM_encode]

private noncomputable def clockedWordOutput (p : Lax51Proofs.Microcode.Program)
    (W T : Polynomial ℕ) (x : List ℕ) : List ℕ :=
  decodedWords (run clockWordsBits .first (statusOutput p W T x))

private theorem clockedWordOutput_time (p : Lax51Proofs.Microcode.Program)
    (W T : Polynomial ℕ) : TuringPolytime (clockedWordOutput p W T) := by
  refine ⟨?_⟩
  exact TMComposition.computableInPolyTime
    (TMComposition.computableInPolyTime
      (TMComposition.computableInPolyTime (emitterMachine p W T) (taggedMachine p W T))
      (computable clockWordsBits)) decoderMachine

/-- A bounded RAM program may be certified on its actual invocation domain.
The verified clock and total word decoder provide one binary polynomial-time
function on all words, agreeing with arbitrary output lists on that domain. -/
theorem totalBinary_of_ramOn {valid : List ℕ → Prop} {f : List ℕ → List ℕ}
    (h : RamPolytimeOn valid f) :
    ∃ g, TuringPolytime g ∧ ∀ x, valid x → g x = f x := by
  obtain ⟨p₀,W,T₀,hp⟩ := h
  let p := Lax51Proofs.CellToMicrocode.compile p₀
  let T : Polynomial ℕ := 3*T₀
  refine ⟨clockedWordOutput p W T,clockedWordOutput_time p W T,?_⟩
  intro x hx
  obtain ⟨hfit,hr⟩ := hp x hx
  have hw : W.eval (bitSize x) ≤ simulationWordWidth W x :=
    (polynomial_eval_le_simpleMajorant W (bitSize x)).trans (by simp [simulationWordWidth])
  obtain ⟨t,ht,hr⟩ := hr _ hw
  have hm := Lax51Proofs.CellToMicrocode.runsTo hr
  have hclock : 3*t ≤ T.eval (bitSize x) := by simpa [T] using Nat.mul_le_mul_left 3 ht
  have hfinal := simulationAfterFuel_eq_of_runsTo p W T x (f x) (3*t) hfit hclock hm
  have hs : simulationSucceeded p W T x = true := by
    simp [simulationSucceeded,hfinal,Turing.haltList]
  have ho : simulationRawOutput p W T x = encode (f x) := by
    unfold simulationRawOutput
    rw [hfinal,ramSimulation_haltList]
    rfl
  have hStatus : statusOutput p W T x = .one :: encode (f x) := by
    change (if simulationSucceeded p W T x then .one else .zero) :: simulationRawOutput p W T x = _
    rw [hs,ho]
    rfl
  change decodedWords (run clockWordsBits .first (statusOutput p W T x)) = f x
  rw [hStatus,clockWordsBits_encoded,decoder_roundtrip]

/-- Problem 1.8's compiler and the checked clock also accept physical word
bounds that are supplied as polynomials in the original input bits. -/
theorem totalBinary_of_boundedWordRuns (valid : List ℕ → Prop) (f : List ℕ → List ℕ)
    (c : Com) (P T : Polynomial ℕ)
    (hr : ∀ x : List ℕ, valid x → ∃ (ext : String → ℕ) (s : Env),
      Run (P.eval (bitSize x)) c (initEnv ext (x.length::x)) s (T.eval (bitSize x)) ∧ s.out = f x) :
    ∃ g, TuringPolytime g ∧ ∀ x, valid x → g x = f x := by
  open Mathproof.Problem18P34Machine20261002Layout in
  apply totalBinary_of_ramOn
  apply ramPolytimeOn_of_bounded_imp valid (layout c) c f P T (layout_ok c)
  intro x hx
  obtain ⟨ext,s,hr,ho⟩ := hr x hx
  have hP : P.eval (bitSize x) ≤ 2^(P.eval (bitSize x)+bitSize x+1) :=
    (Nat.lt_two_pow_self (n := P.eval (bitSize x))).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨ext,s,EvenTI.P12ComparePrep.cutRunWordLift hP hr,ho⟩

#print axioms totalBinary_of_ramOn
#print axioms totalBinary_of_boundedWordRuns
end EvenTI.P15Execution