import EvenP12CountPostNormalize
import EvenP12CountPreInput
import EvenP12CountPreEmit
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12CountPost

open EvenTI.P10Oracle EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false
set_option maxHeartbeats 480000

theorem take_cut (xs : List ℕ) : xs.take (cut xs).1.length = (cut xs).1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | zero => rfl
    | succ a => simpa only [cut, List.length_cons, List.take_succ_cons] using
        congrArg (List.cons (a + 1)) ih

theorem postZSource_slice (xs : List ℕ) :
    postZSource xs = (((xs.take (cut xs).1.length).drop (xs.headD 0)).map Nat.pred) := by
  rw [take_cut]
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases a with
    | zero => rfl
    | succ a =>
      change ((unpositiveWords (cut xs).1).drop a) = (((cut xs).1.drop a).map Nat.pred)
      simp [unpositiveWords, List.map_drop]

def emitPred : Com := .write (.sub (.var "word") (.lit 1))

theorem emitPred_run {B : ℕ} {σ : Env} (hB : 1 < B) (hw : σ.vars "word" < B) :
    Run B emitPred σ {σ with out := σ.out ++ [Nat.pred (σ.vars "word")]} 4 := by
  exact Run.write (evalB_bin (op := .sub) (evalB_var hw) (evalB_lit hB)
    (by simp; omega))

def postSourceScan : Com :=
  .seq (.assign "stop" (.var "cursor"))
    (.seq (.assign "cursor" (.get "data" (.lit 0)))
      (.ite bankGuard (bankLoop emitPred) .skip))

def postSourceProg : Com :=
  .seq (.read "length") (.seq inputLoadLoop
    (.seq (.seq (.assign "cursor" (.lit 0)) (segmentLoop false)) postSourceScan))

def postSourceLayout : Layout := ⟨["length","i","word","cursor","stop"], ["data"], 5⟩

theorem inputLoad_ok_of (L : Layout) (hl : "length" ∈ L.scalars)
    (hi : "i" ∈ L.scalars) (hw : "word" ∈ L.scalars)
    (hd : "data" ∈ L.arrays) (ht : 0 < L.temps) :
    Com.Ok L inputLoadLoop := by
  change Com.Ok L (.while (.lt (.var "i") (.var "length"))
    (.seq (.read "word") (.seq (.store "data" (.var "i") (.var "word"))
      (.assign "i" (.add (.var "i") (.lit 1))))))
  simp [Com.Ok,Expr.Ok,Cond.Ok,condExpr,hl,hi,hw,hd,ht]

theorem postSourceProg_ok : Com.Ok postSourceLayout postSourceProg := by
  have hLoad : Com.Ok postSourceLayout inputLoadLoop := inputLoad_ok_of _ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simp [Com.Ok,postSourceLayout],hLoad,?_⟩
  simp [postSourceLayout,postSourceScan,segmentLoop,segmentCond,segmentBody,
    advanceCursor,bankGuard,bankLoop,bankBody,emitPred,Com.Ok,Expr.Ok,Cond.Ok,condExpr]
theorem postSourceScan_run (xs : List ℕ) {B : ℕ} {σ : Env}
    (hB : 1 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hcur : σ.vars "cursor" = (cut xs).1.length)
    (hbank : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B postSourceScan σ τ (15*xs.length + 15) ∧
      τ.out = σ.out ++ postZSource xs := by
  let stop := (cut xs).1.length
  let start := xs.headD 0
  have hstop : stop ≤ xs.length := postCutLength_le xs
  have hhead : (sentinelWords xs)[0]? = some start := by cases xs <;> rfl
  have hstart : start < B := by cases xs with
    | nil => simpa [start] using (show 0 < B by omega)
    | cons x xs => exact hv x (by simp)
  let s := σ.setVar "stop" stop
  let t := s.setVar "cursor" start
  have er : (Expr.var "cursor").evalB B σ = some stop := by
    simpa only [hcur] using evalB_var (B := B) (σ := σ) (x := "cursor") (by omega)
  have r₁ : Run B (.assign "stop" (.var "cursor")) σ s 2 := Run.assign er
  have r₂ : Run B (.assign "cursor" (.get "data" (.lit 0))) s t 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by simpa [s,hbank] using hhead) hstart)
  have eg : bankGuard.evalB B t = some (decide (start < stop)) := by
    have ee := evalB_condLt (B := B) (σ := t) (e := .var "cursor") (f := .var "stop")
      (evalB_var (by simpa [t] using hstart))
      (evalB_var (by simp [t,s]; omega))
    simpa [bankGuard,t,s] using ee
  by_cases h : start < stop
  · have hg : bankGuard.evalB B t = some true := by simpa [h] using eg
    obtain ⟨τ,hr,_,_,_,_,ho⟩ := bankLoop_run xs (σ := t) (start := start) (stop := stop) emitPred Nat.pred (fun _ hw => emitPred_run hB hw)
      h.le hstop (by simp [t]) (by simp [t,s]) (by simpa [t,s] using hbank) hlen hB hv
    refine ⟨τ, (r₁.seq (r₂.seq (Run.ite_true (d := .skip) hg hr))).mono ?_, ?_⟩
    · simp [bankGuard] <;> omega
    · rw [postZSource_slice]
      exact ho
  · have hg : bankGuard.evalB B t = some false := by simpa [h] using eg
    refine ⟨t, (r₁.seq (r₂.seq (Run.ite_false (c := bankLoop emitPred) hg Run.skip))).mono ?_, ?_⟩
    · simp [bankGuard] <;> omega
    · have hnil : (xs.take stop).drop start = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_take]
        exact (Nat.min_le_left _ _).trans (Nat.le_of_not_gt h)
      rw [postZSource_slice]
      change σ.out = σ.out ++ (((xs.take stop).drop start).map Nat.pred)
      simp [hnil]

theorem postZSource_turingPolytime : TuringPolytime postZSource := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp postSourceLayout postSourceProg postZSource
    (Polynomial.C 3) (50 * Polynomial.X + 50) postSourceProg_ok
  intro xs
  let B := 2 ^ (3 + bitSize xs + 1)
  have hB : 1 < B := Nat.one_lt_two_pow (by omega)
  have hBits := Lax51Proofs.Encoding.length_le_bitSize xs
  have hbase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hlen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hbase
  have hv : ∀ x ∈ xs, x < B := fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hbase
  let σ := initEnv (fun _ => xs.length + 1) (xs.length :: xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have r₁ : Run B (.read "length") σ s 1 := Run.read rfl
  obtain ⟨t,r₂,_,hbank,hout,hinp⟩ := inputLoad_run xs (σ := s)
    (by simp [s]) (by simp [s,σ,initEnv]) rfl
    (by simp [s,σ,initEnv,inputBuffer_zero]) hlen hB hv
  rw [inputBuffer_full] at hbank
  -- The bank loader does not modify cursor. Set it explicitly before scanning.
  let t₀ := t.setVar "cursor" 0
  have r₀ : Run B (.assign "cursor" (.lit 0)) t t₀ 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨u,r₃,hcur,_,harr,_,hou⟩ := segmentLoop_run false xs (start := 0) (σ := t₀)
    (by omega) (by simp [t₀]) (by simpa [t₀] using hbank) hlen hv
  obtain ⟨v,r₄,hov⟩ := postSourceScan_run xs hB hlen hv
    (by simpa using hcur) (by simpa [harr,t₀] using hbank)
  refine ⟨fun _ => xs.length + 1, v, ?_, ?_⟩
  · simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact (r₁.seq (r₂.seq ((r₀.seq r₃).seq r₄))).mono (by omega)
  · simpa [hou,t₀,hout,s,σ,initEnv] using hov

#print axioms postZSource_slice
#print axioms postSourceScan_run
#print axioms postZSource_turingPolytime
end EvenTI.P12CountPost
