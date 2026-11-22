import EvenP12CountPostPadding
import EvenP12CountPrePrefix

namespace EvenTI.P12CountPost

open EvenTI.P10Oracle EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false
set_option maxHeartbeats 600000

theorem indexedBits_last (q d i : ℕ) (g : ℕ → ℕ) :
    indexedBits q (d+1) i g =
      (List.range q).map (fun k => g (q*(i+d)+k)) ++ indexedBits q d i g := by
  induction d generalizing i with
  | zero => simp [indexedBits]
  | succ d ih =>
    rw [indexedBits,ih (i+1)]
    simp only [indexedBits,List.append_assoc]
    rw [show i+1+d = i+(d+1) by omega]

theorem indexedBits_reverseFlags (q : ℕ) (xs : List ℕ) (base d : ℕ) :
    indexedBits q d 0 (fun j => flagAt xs (base+2*j)) = reverseFlags q xs base d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [indexedBits_last,reverseFlags,ih]
    have h : (fun k => flagAt xs (base+2*(q*(0+d)+k))) =
        (fun k => flagAt xs (base+(2*q*d+2*k))) := by
      funext k
      congr 1
      ring
    rw [h]

private def insidePrefix : Cond := .lt (.var "first") (.var "cursor")
private def arityTooLarge : Cond := .lt (.var "cursor") (.var "rows")
private def readArity : Expr := .sub (.get "data" (.var "first")) (.lit 1)
private def setAnswerBase : Com := .assign "base" (.add (.var "cursor") (.lit 1))
private def emitGridFrame (q : ℕ) : Com :=
  .seq setAnswerBase (.seq (.write (.var "rows")) (emitGrid q))

def normalizeBody (q : ℕ) : Com :=
  .seq (.assign "first" (.get "data" (.lit 0)))
    (.ite insidePrefix
      (.seq (.assign "rows" readArity) (.ite arityTooLarge .skip (emitGridFrame q)))
      .skip)

def normalizeProg (q : ℕ) : Com :=
  .seq (.read "length") (.seq inputLoadLoop
    (.seq (.seq (.assign "cursor" (.lit 0)) (segmentLoop false)) (normalizeBody q)))

def normalizeLayout : Layout :=
  ⟨["length","i","word","cursor","stop","first","rows","base","cell"], ["data"], 4⟩

private theorem emitFlagRow_ok (q : ℕ) : Com.Ok normalizeLayout (emitFlagRow q) := by
  induction q with
  | zero => trivial
  | succ q ih =>
    rw [emitFlagRow]
    constructor
    · exact ih
    · simp [emitFlag,normalizeLayout,Com.Ok,Cond.Ok,Expr.Ok,condExpr]

theorem normalizeProg_ok (q : ℕ) : Com.Ok normalizeLayout (normalizeProg q) := by
  have hLoad : Com.Ok normalizeLayout inputLoadLoop := inputLoad_ok_of _ (by decide)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simp [Com.Ok,normalizeLayout],hLoad,?_⟩
  simp [normalizeBody, insidePrefix, arityTooLarge, readArity, setAnswerBase,
    emitGridFrame, emitGrid, gridGuard, gridBody, normalizeLayout, Com.Ok, Cond.Ok, Expr.Ok,
    condExpr, segmentLoop, segmentCond, segmentBody, advanceCursor] <;> exact emitFlagRow_ok q
theorem normalizeBody_run (q : ℕ) (xs : List ℕ) {B : ℕ} {σ : Env}
    (hConst : 2*q+4 < B) (hlen : xs.length < B) (hv : ∀ x ∈ xs, x < B)
    (hBig : (2*q+2)*(xs.length+1) < B)
    (hC : σ.vars "cursor" = (cut xs).1.length)
    (hL : σ.vars "length" = xs.length)
    (hdata : σ.arrs "data" = sentinelWords xs) :
    ∃ τ, Run B (normalizeBody q) σ τ ((26*q+15)*xs.length + 64) ∧
      τ.out = σ.out ++ normalizeClassified q xs := by
  let stop := (cut xs).1.length
  let p := xs.headD 0
  have hStop : stop ≤ xs.length := postCutLength_le xs
  have hpTop : (sentinelWords xs)[0]? = some p := by cases xs <;> rfl
  have hp : p < B := by
    cases xs with
    | nil => simp [p]; omega
    | cons x xs => exact hv x (by simp)
  let s := σ.setVar "first" p
  have ep : (Expr.get "data" (.lit 0)).evalB B σ = some p :=
    evalB_get (evalB_lit (by omega)) (by rwa [hdata]) hp
  have r₁ : Run B (.assign "first" (.get "data" (.lit 0))) σ s 3 := Run.assign ep
  have e₁ : (Expr.var "first").evalB B s = some p := by
    simpa [s] using evalB_var (B := B) (σ := s) (x := "first") (by simpa [s] using hp)
  have eC : (Expr.var "cursor").evalB B s = some stop := by
    have hh : s.vars "cursor" = stop := by simpa [s] using hC
    simpa only [hh] using evalB_var (B := B) (σ := s) (x := "cursor") (by rw [hh]; omega)
  have et := evalB_condLt e₁ eC
  by_cases hs : p < stop
  · have eg : insidePrefix.evalB B s = some true := by simpa [insidePrefix,hs] using et
    have hpos := hs.trans_le hStop
    let d := (xs.getD p 0).pred
    have hd : d = xs[p] - 1 := by simp [d,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hpos]
    have hword : xs[p] < B := hv _ (List.getElem_mem hpos)
    have ev : (Expr.get "data" (.var "first")).evalB B s = some xs[p] := by
      refine evalB_get e₁ ?_ hword
      simp [s,hdata,sentinelWords,List.getElem?_append_left hpos,List.getElem?_eq_getElem hpos]
    let t := s.setVar "rows" d
    have eD : readArity.evalB B s = some d := by
      rw [hd]
      exact evalB_bin (op := .sub) ev (evalB_lit (by omega)) (by simp; omega)
    have r₂ : Run B (.assign "rows" readArity) s t 5 := Run.assign eD
    have eRows : (Expr.var "rows").evalB B t = some d := by
      simpa [t] using evalB_var (B := B) (σ := t) (x := "rows") (by simp [t]; omega)
    have eStop : (Expr.var "cursor").evalB B t = some stop := by
      have hh : t.vars "cursor" = stop := by simpa [t,s] using hC
      simpa only [hh] using evalB_var (B := B) (σ := t) (x := "cursor") (by rw [hh]; omega)
    have ed := evalB_condLt eStop eRows
    by_cases hb : stop < d
    · have ed' : arityTooLarge.evalB B t = some true := by simpa [arityTooLarge,hb] using ed
      refine ⟨t,(r₁.seq (Run.ite_true (d := .skip) eg
        (r₂.seq (Run.ite_true (d := emitGridFrame q) ed' Run.skip)))).mono ?_,?_⟩
      · simp [insidePrefix,arityTooLarge] <;> omega
      · have hnorm : normalizeClassified q xs = [] := by
          unfold normalizeClassified
          change (if p < stop then if d ≤ stop then _ else [] else []) = _
          rw [if_pos hs,if_neg (Nat.not_le_of_gt hb)]
        simp [hnorm,t,s]
    · have ed' : arityTooLarge.evalB B t = some false := by simpa [arityTooLarge,hb] using ed
      let base := stop + 1
      have hMul := Nat.mul_le_mul_left (2*q) (show d ≤ xs.length+1 by omega)
      have hpCap : base + 2*q*d < B := by
        have he : (2*q+2)*(xs.length+1) = 2*q*(xs.length+1) + 2*(xs.length+1) := by ring
        rw [he] at hBig
        omega
      let t₀ := t.setVar "base" base
      let u := {t₀ with out := t₀.out ++ [d]}
      have eB : (Expr.add (.var "cursor") (.lit 1)).evalB B t = some base :=
        evalB_bin (op := .add) eStop (evalB_lit (by omega)) (by change base < B; omega)
      have rB : Run B setAnswerBase t t₀ 4 := Run.assign eB
      have eOut : (Expr.var "rows").evalB B t₀ = some d := by
        simpa [t₀,t] using evalB_var (B := B) (σ := t₀) (x := "rows") (by simp [t₀,t]; omega)
      have rW : Run B (.write (.var "rows")) t₀ u 2 := Run.write eOut
      obtain ⟨v,rv,hov⟩ := emitGrid_run q xs (σ := u) base d (by omega) hlen hv
        (by omega) (by omega) (by simpa [u,t₀,t,s] using hL)
        (by simpa [u,t₀,t,s] using hdata) (by simp [u,t₀]) (by simp [u,t₀,t]) hpCap
      refine ⟨v,(r₁.seq (Run.ite_true (d := .skip) eg
        (r₂.seq (Run.ite_false (c := .skip) ed' (rB.seq (rW.seq rv)))))).mono ?_,?_⟩
      · have hm := Nat.mul_le_mul_left (26*q+15) (show d ≤ xs.length by omega)
        simp [insidePrefix,arityTooLarge] <;> omega
      · rw [hov]
        have hnorm : normalizeClassified q xs = d :: reverseFlags q xs base d := by
          unfold normalizeClassified
          change (if p < stop then if d ≤ stop then
            d :: indexedBits q d 0 (fun j => flagAt xs (base+2*j))
            else [] else []) = _
          rw [if_pos hs,if_pos (Nat.le_of_not_gt hb),indexedBits_reverseFlags]
        simp [hnorm,u,t₀,t,s,List.append_assoc]
  · have eg : insidePrefix.evalB B s = some false := by simpa [insidePrefix,hs] using et
    refine ⟨s,(r₁.seq (Run.ite_false (c := .seq (.assign "rows" readArity)
      (.ite arityTooLarge .skip (emitGridFrame q))) eg Run.skip)).mono ?_,?_⟩
    · simp [insidePrefix] <;> omega
    · have hh : normalizeClassified q xs = [] := by
        unfold normalizeClassified
        change (if p < stop then _ else []) = _
        rw [if_neg hs]
      simp [hh,s]

theorem normalizeClassified_turingPolytime (q : ℕ) : TuringPolytime (normalizeClassified q) := by
  apply Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  apply ramPolytime_of_bounded_imp normalizeLayout (normalizeProg q) (normalizeClassified q)
    (Polynomial.C (2*q+6)) (Polynomial.C (26*q+50) * Polynomial.X + Polynomial.C 100)
    (normalizeProg_ok q)
  intro xs
  let B := 2 ^ (2*q+6 + bitSize xs + 1)
  have hBits := Lax51Proofs.Encoding.length_le_bitSize xs
  have hBase : 2^(bitSize xs+1) ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  have hConst : 2*q+4 < B :=
    (Nat.lt_two_pow_self (n := 2*q+4)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlen := (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs).trans_le hBase
  have hv : ∀ x ∈ xs, x < B := fun x hx =>
    (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hx).trans_le hBase
  have hCoeff : 2*q+2 < 2^(2*q+6) :=
    (Nat.lt_two_pow_self (n := 2*q+2)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hLenPow : xs.length+1 ≤ 2^(bitSize xs+1) :=
    Nat.succ_le_of_lt (Lax51Proofs.Encoding.length_lt_two_pow_bitSize_add_one xs)
  have hBig : (2*q+2)*(xs.length+1) < B := calc
    _ < 2^(2*q+6)*(xs.length+1) := Nat.mul_lt_mul_of_pos_right hCoeff (by omega)
    _ ≤ 2^(2*q+6)*2^(bitSize xs+1) := Nat.mul_le_mul_left _ hLenPow
    _ = B := by rw [← pow_add]; simp [B,Nat.add_assoc]
  let σ := initEnv (fun _ => xs.length + 1) (xs.length :: xs)
  let s := {σ.setVar "length" xs.length with inp := xs}
  have r₁ : Run B (.read "length") σ s 1 := Run.read rfl
  obtain ⟨t,r₂,hLt,hbank,hout,hinp⟩ := inputLoad_run xs (σ := s)
    (by simp [s]) (by simp [s,σ,initEnv]) rfl (by simp [s,σ,initEnv,inputBuffer_zero])
    hlen (by omega) hv
  rw [inputBuffer_full] at hbank
  let t₀ := t.setVar "cursor" 0
  have r₀ : Run B (.assign "cursor" (.lit 0)) t t₀ 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨u,r₃,hcur,_,harr,_,hou⟩ := segmentLoop_run false xs (start := 0) (σ := t₀)
    (by omega) (by simp [t₀]) (by simpa [t₀] using hbank) hlen hv
  have hLu : u.vars "length" = xs.length :=
    (vars_eq_of_untouched r₃ (segment_untouched false (x := "length") (by decide))).trans
      (by simpa [t₀] using hLt)
  obtain ⟨v,r₄,hov⟩ := normalizeBody_run q xs hConst hlen hv hBig
    (by simpa using hcur) hLu (by simpa [harr,t₀] using hbank)
  refine ⟨fun _ => xs.length + 1, v, ?_, ?_⟩
  · simp only [Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]
    apply (r₁.seq (r₂.seq ((r₀.seq r₃).seq r₄))).mono
    have hm := Nat.mul_le_mul_left (26*q+50) hBits
    simp only [Nat.add_mul] at hm ⊢
    omega
  · simpa [hou,t₀,hout,s,σ,initEnv] using hov

#print axioms normalizeBody_run
#print axioms normalizeClassified_turingPolytime
end EvenTI.P12CountPost
