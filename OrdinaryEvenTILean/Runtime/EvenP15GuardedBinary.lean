import EvenP14ProjectionEngine
import EvenP12RecognizeAssembly
import EvenP12ComparePrepRaw

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Lax51.BinaryWordEncoding Lax51.TuringPolytime
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Mathproof.Problem18P34Machine20261002Layout (layout layout_ok)
open EvenTI.P10Oracle EvenTI.P12CountPre EvenTI.P12Guard EvenTI.P14Projection

private def finishRoute (xs : List ℕ) : List ℕ :=
  if 2 ≤ xs.length then ((xs.take (xs.length-1)).drop 1).map (· - 1) else [0]

private def passGuard : Cond := .lt (.var "length") (.lit 2)
private def replayUnshift : Com := .write (.sub (.var "word") (.lit 1))
private def replayRoute : Com := .seq (.assign "cursor" (.lit 1))
  (.seq (.assign "stop" (.sub (.var "length") (.lit 1))) (bankLoop replayUnshift))
private def finishRouteProg : Com := .seq (.read "length")
  (.seq inputLoadLoop (.ite passGuard (.write (.lit 0)) replayRoute))

private theorem finishRouteProg_run (xs : List ℕ) {B : ℕ} (hB : 2 < B)
    (hLen : xs.length < B) (hWords : ∀ a ∈ xs, a < B) :
    ∃ t, Run B finishRouteProg (initEnv (fun _ => xs.length+1) (xs.length::xs)) t
      (29*xs.length+30) ∧ t.out=finishRoute xs := by
  let s := initEnv (fun _ => xs.length+1) (xs.length::xs)
  let u := {s.setVar "length" xs.length with inp := xs}
  have r₀ : Run B (.read "length") s u 1 := Run.read rfl
  obtain ⟨v,r₁,hl,hbank,ho,_⟩ := inputLoad_run xs (σ:=u) (by simp [u])
    (by simp [u,s,initEnv]) rfl (by simp [u,s,initEnv,inputBuffer_zero]) hLen (by omega) hWords
  have hv : v.out=[] := by simpa [u,s,initEnv] using ho
  have et : passGuard.evalB B v = some (decide (xs.length < 2)) :=
    evalB_condLt (liveVar hl hLen) (evalB_lit hB)
  by_cases h : xs.length < 2
  · have ht : passGuard.evalB B v = some true := by simpa [h] using et
    have rr : Run B (.write (.lit 0)) v {v with out := v.out ++ [0]} 2 :=
      Run.write (evalB_lit (by omega))
    refine ⟨_,(r₀.seq (r₁.seq (Run.ite_true (d:=replayRoute) ht rr))).mono ?_,?_⟩
    · simp [passGuard,Cond.size,Expr.size]; omega
    · simpa [hv,finishRoute,show ¬ 2 ≤ xs.length by omega]
  · have ht : passGuard.evalB B v = some false := by simpa [h] using et
    let w := v.setVar "cursor" 1
    let w' := w.setVar "stop" (xs.length-1)
    have r₂ : Run B (.assign "cursor" (.lit 1)) v w 2 := Run.assign (evalB_lit (by omega))
    have r₃ : Run B (.assign "stop" (.sub (.var "length") (.lit 1))) w w' 4 := by
      apply Run.assign
      exact evalB_bin (op:=.sub) (liveVar (by simpa [w] using hl) hLen)
        (evalB_lit (by omega)) (by change xs.length-1<B; omega)
    obtain ⟨t,r₄,_,_,_,_,htOut⟩ := bankLoop_run xs (σ:=w') replayUnshift (fun a => a-1)
      (c:=4) (fun z hz => Run.write (evalB_bin (op:=.sub) (evalB_var hz) (evalB_lit (by omega))
        (by change z.vars "word"-1<B; omega))) (by omega : 1 ≤ xs.length-1)
      (by omega) (by simp [w',w]) (by simp [w']) (hbank.trans (inputBuffer_full xs)) hLen (by omega) hWords
    refine ⟨t,(r₀.seq (r₁.seq (Run.ite_false (c:=.write (.lit 0)) ht (r₂.seq (r₃.seq r₄))))).mono ?_,?_⟩
    · simp [passGuard,Cond.size,Expr.size]; omega
    · simpa [w',w,hv,finishRoute,show 2 ≤ xs.length by omega] using htOut

private theorem finishRoute_time : TuringPolytime finishRoute := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp (layout finishRouteProg) finishRouteProg finishRoute
    (Polynomial.C 2) (29*Polynomial.X+30) (layout_ok _)
  intro xs
  let L := bitSize xs
  let B := 2^(2+L+1)
  have hb : 2 < B := (show 2 < 2^3 by decide).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hM : 2^(L+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hs := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hM
  have hw : ∀ a ∈ xs, a<B := fun _ ha => (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one ha).trans_le hM
  obtain ⟨t,hr,ho⟩ := finishRouteProg_run xs hb hs hw
  refine ⟨fun _ => xs.length+1,t,?_ ,ho⟩
  simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  have hh := Lax51Proofs.Encoding.length_le_bitSize xs
  exact hr.mono (by omega)

private theorem finishRoute_pair (x : List ℕ) : finishRoute (packSegments [[],x]) = x := by
  have hl : (packSegments [[],x]).length-1 = (0::positiveWords x).length := by
    simp [packSegments,positiveWords]
  have hs : 2 ≤ (packSegments [[],x]).length := by simp [packSegments,positiveWords] <;> omega
  rw [finishRoute,if_pos hs,hl]
  rw [show packSegments [[],x] = (0::positiveWords x)++[0] by simp [packSegments,positiveWords]]
  rw [List.take_append_of_le_length le_rfl,List.take_length,List.drop_succ_cons,List.drop_zero]
  simp [positiveWords,List.map_map,Function.comp_def]

private theorem mapGatePair (f : List ℕ → List ℕ) (x y : List ℕ) :
    mapZ (positiveCallback f) (packSegments [x,y]) = packSegments [x,f y] := by
  rw [show packSegments [x,y] = positiveWords x ++ 0 :: packSegments [y] by simp [packSegments]]
  rw [mapZ_positiveWords,mapRest_packSegments]
  simp [packSegments]

/-- Dispatch an actual polynomial-time word function on the accepting route
of a polynomial-time guard. Invalid requests return the literal `[0]`. -/
theorem guardedBinary_time {guard f : List ℕ → List ℕ}
    (hg : TuringPolytime guard) (hf : TuringPolytime f) :
    TuringPolytime (fun x => if guard x = [1] then f x else [0]) := by
  have h₁ := turingPolytime_comp duplicateFrame_turingPolytime
    (turingPolytime_mapZ (positiveCallback_turingPolytime hg))
  have h₂ := turingPolytime_comp h₁ (routeOutput_time true)
  have h₃ := turingPolytime_comp h₂ (turingPolytime_mapZ (positiveCallback_turingPolytime hf))
  have h₄ := turingPolytime_comp h₃ finishRoute_time
  convert h₄ using 1
  funext x
  simp only [Function.comp_apply,mapGatePair,route_pair]
  by_cases h : guard x = [1]
  · simp only [h,if_true,mapGatePair,finishRoute_pair]
  · have h0 : mapZ (positiveCallback f) (packSegments [[]]) = [0] := by
      change mapZ (positiveCallback f) (positiveWords [] ++ 0 :: packSegments []) = [0]
      rw [mapZ_positiveWords,mapRest_packSegments]
      rfl
    simp only [if_neg h,h0]
    rfl

#print axioms guardedBinary_time
end EvenTI.P15Execution