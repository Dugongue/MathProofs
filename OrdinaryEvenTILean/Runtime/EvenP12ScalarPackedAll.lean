import EvenP12RecognizeAnyTrial
import EvenP12CountPostSource

namespace EvenTI.P12Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open EvenTI.P10Oracle EvenTI.P12Guard

set_option autoImplicit false
set_option maxHeartbeats 550000

def flipBit (w : List ℕ) : List ℕ := if w.headD 0 = 1 then [0] else [1]

def flipBitProg : Com := .seq (.read "length")
  (.ite (.lt (.lit 0) (.var "length"))
    (.seq (.read "word")
      (.ite (.eq (.var "word") (.lit 1)) (.write (.lit 0)) (.write (.lit 1))))
    (.write (.lit 1)))

def flipBitLayout : Layout := ⟨["length","word"],[],5⟩

theorem flipBitProg_ok : Com.Ok flipBitLayout flipBitProg := by
  simp [flipBitProg,flipBitLayout,Com.Ok,Expr.Ok,Cond.Ok,condExpr]

theorem flipBitProg_run (xs : List ℕ) {B : ℕ} (hB : 1 < B)
    (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B) :
    ∃ t, Run B flipBitProg (initEnv (fun _ => 0) (xs.length::xs)) t 32 ∧
      t.out = flipBit xs := by
  let σ := initEnv (fun _ => 0) (xs.length::xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have hr : Run B (.read "length") σ s 1 := Run.read rfl
  have eL : (Expr.var "length").evalB B s = some xs.length := by
    simpa [s] using evalB_var (B := B) (σ := s) (x := "length") (by simpa [s] using hlen)
  have eg := evalB_condLt (evalB_lit (show 0 < B by omega)) eL
  cases xs with
  | nil =>
    have eg' : (Cond.lt (.lit 0) (.var "length")).evalB B s = some false := by simpa using eg
    refine ⟨_,(hr.seq (Run.ite_false eg' (Run.write (evalB_lit hB)))).mono ?_,?_⟩
    · decide
    · simp [s,σ,initEnv,flipBit]
  | cons a tail =>
    have eg' : (Cond.lt (.lit 0) (.var "length")).evalB B s = some true := by simpa using eg
    let t := {s.setVar "word" a with inp := tail}
    have ht : Run B (.read "word") s t 1 := Run.read rfl
    have he : (Expr.var "word").evalB B t = some a := by
      have ha := hv a List.mem_cons_self
      simpa [t] using evalB_var (B := B) (σ := t) (x := "word") (by simpa [t] using ha)
    have ea := evalB_condEq he (evalB_lit hB)
    by_cases hh : a = 1
    · have ea' : (Cond.eq (.var "word") (.lit 1)).evalB B t = some true := by simpa [hh] using ea
      refine ⟨_,(hr.seq (Run.ite_true (d := .write (.lit 1)) eg' (ht.seq
        (Run.ite_true (d := .write (.lit 1)) ea' (Run.write (evalB_lit (by omega : 0 < B))))))).mono ?_,?_⟩
      · decide
      · simp [t,s,σ,initEnv,flipBit,hh]
    · have ea' : (Cond.eq (.var "word") (.lit 1)).evalB B t = some false := by simpa [hh] using ea
      refine ⟨_,(hr.seq (Run.ite_true (d := .write (.lit 1)) eg' (ht.seq
        (Run.ite_false (c := .write (.lit 0)) ea' (Run.write (evalB_lit hB)))))).mono ?_,?_⟩
      · decide
      · simp [t,s,σ,initEnv,flipBit,hh]

theorem flipBit_turingPolytime : TuringPolytime flipBit := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp flipBitLayout flipBitProg flipBit
    (Polynomial.C 2) (Polynomial.C 32) flipBitProg_ok
  intro xs
  let B := 2^(2+bitSize xs+1)
  have hB : 1 < B := Nat.one_lt_two_pow (by omega)
  have hbase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hlen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hbase
  obtain ⟨t,hr,ho⟩ := flipBitProg_run xs hB hlen (fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hbase)
  exact ⟨fun _ => 0,t,by simpa only [B,Polynomial.eval_C] using hr,ho⟩

/-- Use the existing OR stream machine with two checked Boolean flips
to implement the universal self-branch scan on actual input tapes. -/
theorem packedTrialsAll_time {prepare : List Nat → List (List Nat)}
    {decideTrial : List Nat → List Nat}
    (hPrepare : TuringPolytime (fun w => packSegments ([] :: prepare w)))
    (hDecide : TuringPolytime decideTrial)
    (hAnswer : ∀ x, decideTrial x = [0] ∨ decideTrial x = [1]) :
    TuringPolytime (fun w =>
      if (prepare w).all (fun x => decide (decideTrial x = [1])) then [1] else [0]) := by
  let bad := flipBit ∘ decideTrial
  have hBad : TuringPolytime bad := turingPolytime_comp hDecide flipBit_turingPolytime
  have hBool (x : List Nat) : bad x = [0] ∨ bad x = [1] := by
    rcases hAnswer x with h|h <;> simp [bad,flipBit,h]
  have hScan := packedTrialsAny_time hPrepare hBad hBool
  have hRun := turingPolytime_comp hScan flipBit_turingPolytime
  convert hRun using 1
  funext w
  change _ = flipBit (if [1] ∈ (prepare w).map bad then [1] else [0])
  have hHit : [1] ∈ (prepare w).map bad ↔
      ¬ (prepare w).all (fun x => decide (decideTrial x = [1])) = true := by
    rw [List.mem_map, List.all_eq_true]
    push Not
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    rcases hAnswer x with h|h <;> simp [bad,flipBit,h]
  by_cases h : (prepare w).all (fun x => decide (decideTrial x = [1])) = true
  · simp [h,show [1] ∉ (prepare w).map bad from fun e => (hHit.mp e) h,flipBit]
  · simp [h,hHit.mpr h,flipBit]

#print axioms flipBit_turingPolytime
#print axioms packedTrialsAll_time

end EvenTI.P12Scalar
