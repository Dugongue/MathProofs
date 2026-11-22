import EvenP12CountPostSource
import EvenP12CountPostRoute
import EvenP12CountPrePrefix
import EvenP12CountPostSuccess

namespace EvenTI.P12CountPost

open EvenTI.P10Oracle EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false
set_option maxHeartbeats 490000

/-- On a compare-stream output, expose the retained context when the
comparator announces success. This function is total on malformed streams. -/
def gateFrame (xs : List ℕ) : List ℕ :=
  if ((cut xs).2).headD 0 = 3 then unpositiveWords (cut xs).1 else []

private theorem successCode_decode (w : List ℕ) :
    (unpositiveWords (cut w).1).head? = some 2 ↔ w.headD 0 = 3 := by
  cases w with
  | nil => simp [cut,unpositiveWords]
  | cons a w =>
    cases a with
    | zero => simp [cut,unpositiveWords]
    | succ a => simp [cut,unpositiveWords]

theorem postRouteOut_eq_gateFrame {K : Type} [Field K] [Fintype K] {q : ℕ} (enum : Fin q ≃ Kˣ)
    (w : List ℕ) :
    postRouteOut enum w = postNormalize enum (gateFrame w) [2] := by
  classical
  unfold postRouteOut gateFrame
  by_cases h : ((cut w).2).headD 0 = 3
  · rw [if_pos h]
    apply postNormalize_congr_success
    simp [(successCode_decode (cut w).2).mpr h]
  · rw [if_neg h]
    have hh : ¬ (unpositiveWords (cut (cut w).2).1).head? = some 2 :=
      fun e => h ((successCode_decode (cut w).2).mp e)
    unfold postNormalize postNormalizeParsed
    cases postZSource (unpositiveWords (cut w).1) <;> simp only [hh,false_and,if_false] <;> rfl
private theorem drop_cut (xs : List ℕ) :
    xs.drop ((cut xs).1.length + 1) = (cut xs).2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | zero => rfl
    | succ a => simpa only [cut, List.length_cons, List.drop_succ_cons] using ih

private def haveDelimiter : Cond := .lt (.var "cursor") (.var "length")
private def nextCode : Expr := .get "data" (.add (.var "cursor") (.lit 1))
private def isSuccess : Cond := .eq nextCode (.lit 3)
private def rewindCopy : Com :=
  .seq (.assign "stop" (.var "cursor"))
    (.seq (.assign "cursor" (.lit 0)) (bankLoop emitPred))

def gateBody : Com := .ite haveDelimiter (.ite isSuccess rewindCopy .skip) .skip

def gateProg : Com :=
  .seq (.read "length") (.seq inputLoadLoop
    (.seq (.seq (.assign "cursor" (.lit 0)) (segmentLoop false)) gateBody))

theorem gateProg_ok : Com.Ok postSourceLayout gateProg := by
  have hLoad : Com.Ok postSourceLayout inputLoadLoop := inputLoad_ok_of _ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simp [Com.Ok,postSourceLayout],hLoad,?_⟩
  simp [postSourceLayout,gateBody,haveDelimiter,isSuccess,nextCode,rewindCopy,
    segmentLoop,segmentCond,segmentBody,advanceCursor,bankGuard,bankLoop,bankBody,
    emitPred,Com.Ok,Expr.Ok,Cond.Ok,condExpr]

theorem gateBody_run (xs : List ℕ) {B : ℕ} {σ : Env}
    (hB : 3 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hcur : σ.vars "cursor" = (cut xs).1.length)
    (hl : σ.vars "length" = xs.length)
    (hbank : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B gateBody σ τ (15*xs.length + 30) ∧ τ.out = σ.out ++ gateFrame xs := by
  let stop := (cut xs).1.length
  have hstop : stop ≤ xs.length := postCutLength_le xs
  have ec : (Expr.var "cursor").evalB B σ = some stop := by
    simpa only [hcur] using evalB_var (B := B) (σ := σ) (x := "cursor") (by omega)
  have eL : (Expr.var "length").evalB B σ = some xs.length := by
    simpa only [hl] using evalB_var (B := B) (σ := σ) (x := "length") (by omega)
  have ed := evalB_condLt ec eL
  by_cases hd : stop < xs.length
  · have ed₁ : haveDelimiter.evalB B σ = some true := by simpa [haveDelimiter,hd] using ed
    let a := ((cut xs).2).headD 0
    have heq : (sentinelWords xs)[stop+1]? = some a := by
      have he : a = xs.getD (stop+1) 0 := by
        change ((cut xs).2).headD 0 = _
        rw [show (cut xs).2 = xs.drop (stop+1) from (drop_cut xs).symm]
        simp [List.headD_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [he]
      by_cases hh : stop+1 < xs.length
      · simp [sentinelWords, List.getElem?_append_left hh, List.getD_eq_getElem?_getD, hh]
      · have hlast : stop+1 = xs.length := by omega
        rw [hlast]
        simp [sentinelWords,List.getElem?_append_right,List.getD_eq_getElem?_getD]
    have ha : a < B := by
      cases hh : (cut xs).2 with
      | nil => simp [a,hh] <;> omega
      | cons c cs =>
        have hmem : c ∈ xs := by
          apply List.mem_of_mem_drop (i := stop+1)
          change c ∈ xs.drop ((cut xs).1.length+1)
          rw [drop_cut]
          simp [hh]
        simpa [a,hh] using hv c hmem
    have en : nextCode.evalB B σ = some a := evalB_get
      (evalB_bin (op := .add) ec (evalB_lit (by omega)) (by simp; omega))
      (by simpa [hbank] using heq) ha
    have es := evalB_condEq en (evalB_lit hB)
    by_cases hs : a = 3
    · have es' : isSuccess.evalB B σ = some true := by simpa [isSuccess,hs] using es
      let s := σ.setVar "stop" stop
      let t := s.setVar "cursor" 0
      have r₁ : Run B (.assign "stop" (.var "cursor")) σ s 2 := Run.assign ec
      have r₂ : Run B (.assign "cursor" (.lit 0)) s t 2 := Run.assign (evalB_lit (by omega))
      obtain ⟨τ,hr,_,_,_,_,ho⟩ := bankLoop_run xs (σ := t) (start := 0) (stop := stop) emitPred Nat.pred
        (fun _ hw => emitPred_run (by omega) hw) (show 0 ≤ stop from Nat.zero_le _) hstop
        (by simp [t]) (by simp [t,s]) (by simpa [t,s] using hbank) hlen (by omega) hv
      refine ⟨τ,(Run.ite_true (d := .skip) ed₁
        (Run.ite_true (d := .skip) es' (r₁.seq (r₂.seq hr)))).mono ?_,?_⟩
      · simp [haveDelimiter,isSuccess,nextCode] <;> omega
      · have hs₁ : ((cut xs).2).headD 0 = 3 := hs
        rw [gateFrame,if_pos hs₁]
        simpa [t,s,stop,take_cut,unpositiveWords] using ho
    · have es' : isSuccess.evalB B σ = some false := by simpa [isSuccess,hs] using es
      refine ⟨σ,(Run.ite_true (d := .skip) ed₁
        (Run.ite_false (c := rewindCopy) es' Run.skip)).mono ?_,?_⟩
      · simp [haveDelimiter,isSuccess,nextCode] <;> omega
      · have hs₁ : ((cut xs).2).headD 0 ≠ 3 := hs
        rw [gateFrame,if_neg hs₁,List.append_nil]
  · have ed₀ : haveDelimiter.evalB B σ = some false := by simpa [haveDelimiter,hd] using ed
    have hempty : (cut xs).2 = [] := by
      rw [← drop_cut]
      apply List.drop_eq_nil_of_le
      change xs.length ≤ stop+1
      omega
    refine ⟨σ,(Run.ite_false (c := .ite isSuccess rewindCopy .skip) ed₀ Run.skip).mono ?_,?_⟩
    · simp [haveDelimiter] <;> omega
    · simp [gateFrame,hempty]

theorem gateFrame_turingPolytime : TuringPolytime gateFrame := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp postSourceLayout gateProg gateFrame
    (Polynomial.C 3) (50 * Polynomial.X + 65) gateProg_ok
  intro xs
  let B := 2 ^ (3 + bitSize xs + 1)
  have hB : 3 < B := (show 3 < 2^3 by decide).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hBits := Lax51Proofs.Encoding.length_le_bitSize xs
  have hbase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hlen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hbase
  have hv : ∀ x ∈ xs, x < B := fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hbase
  let σ := initEnv (fun _ => xs.length + 1) (xs.length :: xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have r₁ : Run B (.read "length") σ s 1 := Run.read rfl
  obtain ⟨t,r₂,hLt,hbank,hout,hinp⟩ := inputLoad_run xs (σ := s)
    (by simp [s]) (by simp [s,σ,initEnv]) rfl
    (by simp [s,σ,initEnv,inputBuffer_zero]) hlen (by omega) hv
  rw [inputBuffer_full] at hbank
  let t₀ := t.setVar "cursor" 0
  have r₀ : Run B (.assign "cursor" (.lit 0)) t t₀ 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨u,r₃,hcur,_,harr,_,hou⟩ := segmentLoop_run false xs (start := 0) (σ := t₀)
    (by omega) (by simp [t₀]) (by simpa [t₀] using hbank) hlen hv
  have hLu : u.vars "length" = xs.length :=
    (vars_eq_of_untouched r₃ (segment_untouched false (x := "length") (by decide))).trans
      (by simpa [t₀] using hLt)
  obtain ⟨v,r₄,hov⟩ := gateBody_run xs hB hlen hv
    (by simpa using hcur) hLu (by simpa [harr,t₀] using hbank)
  refine ⟨fun _ => xs.length + 1, v, ?_, ?_⟩
  · simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact (r₁.seq (r₂.seq ((r₀.seq r₃).seq r₄))).mono (by omega)
  · simpa [hou,t₀,hout,s,σ,initEnv] using hov

#print axioms postRouteOut_eq_gateFrame
#print axioms gateBody_run
#print axioms gateFrame_turingPolytime
end EvenTI.P12CountPost
