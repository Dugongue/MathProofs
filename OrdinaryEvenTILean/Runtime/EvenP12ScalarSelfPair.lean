import EvenP12CountPostSource
import EvenP12CountPreEmit
import EvenP12CountPreInput

namespace EvenTI.P12Scalar

open EvenTI.P12CountPre
open EvenTI.P12CountPost (inputLoad_ok_of postSourceLayout)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open EvenTI.Contract EvenTI.Action

set_option autoImplicit false
set_option maxHeartbeats 550000

/-- Reuse comparison codecs with the original source copied to both banks. -/
def selfPairWords (xs : List ℕ) : List ℕ := xs ++ xs.drop 2

private def directWord : Com := .write (.var "word")
private def copyBank : Com := bankLoop directWord
private def secondCopy : Com := .seq (.assign "cursor" (.lit 2)) copyBank
private def hasPayload : Cond := .lt (.lit 2) (.var "stop")

private def selfPairBody : Com :=
  .seq (.assign "stop" (.var "length")) (.seq (.assign "cursor" (.lit 0))
    (.seq copyBank (.ite hasPayload secondCopy .skip)))

def selfPairProg : Com := .seq (.read "length") (.seq inputLoadLoop selfPairBody)

theorem selfPairProg_ok : Com.Ok postSourceLayout selfPairProg := by
  have hLoad : Com.Ok postSourceLayout inputLoadLoop := inputLoad_ok_of _ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simp [Com.Ok,postSourceLayout],hLoad,?_⟩
  simp [selfPairBody,copyBank,directWord,secondCopy,hasPayload,bankLoop,bankGuard,bankBody,
    advanceCursor,postSourceLayout,Com.Ok,Expr.Ok,Cond.Ok,condExpr]

private theorem copyBank_run (xs : List ℕ) {B start : ℕ} {σ : Env}
    (hB : 2 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hstart : start ≤ xs.length) (hCursor : σ.vars "cursor" = start)
    (hStop : σ.vars "stop" = xs.length) (hbank : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B copyBank σ τ (13*(xs.length-start)+4) ∧
      τ.vars "stop" = xs.length ∧ τ.arrs "data" = sentinelWords xs ∧
      τ.out = σ.out ++ xs.drop start := by
  obtain ⟨τ,hr,hVars,hArr,_,_,ho⟩ := bankLoop_run xs (σ := σ) directWord id
    (fun t h => show Run B directWord t {t with out := t.out ++ [t.vars "word"]} 2
      from Run.write (evalB_var h))
    hstart (Nat.le_refl _) hCursor hStop hbank hlen (by omega) hv
  refine ⟨τ,hr,(hVars "stop" (by decide) (by decide)).trans hStop,(congrFun hArr "data").trans hbank,?_⟩
  simpa using ho

theorem selfPairBody_run (xs : List ℕ) {B : ℕ} {σ : Env}
    (hB : 2 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hLength : σ.vars "length" = xs.length)
    (hbank : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B selfPairBody σ τ (26*xs.length + 24) ∧
      τ.out = σ.out ++ selfPairWords xs := by
  let s := σ.setVar "stop" xs.length
  have eS : (Expr.var "length").evalB B σ = some xs.length := by
    simpa only [hLength] using evalB_var (B := B) (σ := σ) (x := "length") (by rwa [hLength])
  let t := s.setVar "cursor" 0
  have hS : Run B (.assign "stop" (.var "length")) σ s 2 := Run.assign eS
  have hT : Run B (.assign "cursor" (.lit 0)) s t 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨u,hr,hStop,hData,hOut⟩ := copyBank_run xs (σ := t)
    hB hlen hv (start := 0) (Nat.zero_le _) (by simp [t]) (by simp [t,s])
    (by simpa [t,s] using hbank)
  have hOut' : u.out = σ.out ++ xs := by simpa [t,s] using hOut
  have eStop : (Expr.var "stop").evalB B u = some xs.length := by
    simpa only [hStop] using evalB_var (B := B) (σ := u) (x := "stop") (by rwa [hStop])
  have eg : hasPayload.evalB B u = some (decide (2 < xs.length)) := evalB_condLt (evalB_lit hB) eStop
  by_cases hp : 2 < xs.length
  · have eg' : hasPayload.evalB B u = some true := by simpa [hp] using eg
    let v := u.setVar "cursor" 2
    have rV : Run B (.assign "cursor" (.lit 2)) u v 2 := Run.assign (evalB_lit hB)
    obtain ⟨z,hZ,_,_,ho⟩ := copyBank_run xs (σ := v) hB hlen hv (start := 2) hp.le
      (by simp [v]) (by simpa [v] using hStop) (by simpa [v] using hData)
    refine ⟨z,(hS.seq (hT.seq (hr.seq (Run.ite_true (d := .skip) eg' (rV.seq hZ))))).mono ?_,?_⟩
    · simp [hasPayload] <;> omega
    · simpa [v,hOut',selfPairWords,List.append_assoc] using ho
  · have eg' : hasPayload.evalB B u = some false := by simpa [hp] using eg
    refine ⟨u,(hS.seq (hT.seq (hr.seq (Run.ite_false (c := secondCopy) eg' Run.skip)))).mono ?_,?_⟩
    · simp [hasPayload] <;> omega
    · simpa [selfPairWords,List.drop_eq_nil_of_le (Nat.le_of_not_gt hp)] using hOut'

theorem selfPairWords_turingPolytime : TuringPolytime selfPairWords := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp postSourceLayout selfPairProg selfPairWords
    (Polynomial.C 3) (42*Polynomial.X + 45) selfPairProg_ok
  intro xs
  let B := 2^(3+bitSize xs+1)
  have hB : 2 < B := by
    exact (show 2 < 2^3 by decide).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hBits := Lax51Proofs.Encoding.length_le_bitSize xs
  have hbase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hlen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hbase
  have hv : ∀ x ∈ xs, x < B := fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hbase
  let σ := initEnv (fun _ => xs.length+1) (xs.length::xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have hS : Run B (.read "length") σ s 1 := Run.read rfl
  obtain ⟨t,ht,hLength,hBusy,hOut,_⟩ := inputLoad_run xs (σ := s)
    (by simp [s]) (by simp [s,σ,initEnv]) rfl
    (by simp [s,σ,initEnv,inputBuffer_zero]) hlen (by omega) hv
  obtain ⟨u,hu,ho⟩ := selfPairBody_run xs hB hlen hv hLength (hBusy.trans (inputBuffer_full _))
  refine ⟨fun _ => xs.length+1,u,?_,?_⟩
  · simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact (hS.seq (ht.seq hu)).mono (by omega)
  · simpa [hOut,s,σ,initEnv] using ho

theorem selfPairWords_encode {K : Type} [Field K] [Fintype K]
    (F : FieldEncoding K) {d n : ℕ} (T : Tensor K d n) :
    selfPairWords (sourceInput F T) = comparisonInput F T T := by
  simp [selfPairWords,sourceInput,comparisonInput]

#print axioms selfPairWords_turingPolytime
#print axioms selfPairWords_encode
end EvenTI.P12Scalar
