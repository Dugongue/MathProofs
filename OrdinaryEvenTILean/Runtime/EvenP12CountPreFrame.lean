
import EvenP11OracleIntegration
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open EvenTI.P10Oracle

set_option autoImplicit false

def comparisonInputOf (words : List Nat) : List Nat :=
  words.drop (words.headD 0 + 1)

private def routeStart (skipPrefix : Bool) (words : List Nat) : Nat :=
  if skipPrefix then words.headD 0 + 1 else 0

def framed (skipPrefix : Bool) (words : List Nat) : List Nat :=
  positiveWords words ++ 0 :: positiveWords (words.drop (routeStart skipPrefix words)) ++ [0]

def comparisonFrame : List Nat → List Nat := framed true

private def natSucc (name : String) : Expr := .add (.var name) (.lit 1)

private def frameBuf (xs : List Nat) (i : Nat) : List Nat :=
  arrOf xs.length (fun j => if j < i then xs.getD j 0 + 1 else 0)

private theorem frameBuf_set (xs : List Nat) {i : Nat} (hi : i < xs.length) :
    (frameBuf xs i).set i (xs[i] + 1) = frameBuf xs (i + 1) := by
  unfold frameBuf
  rw [set_arrOf]
  apply arrOf_congr
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [List.getD_eq_getElem?_getD, hi]
  · by_cases hlt : k < i
    · simp [hki, hlt, show k < i + 1 by omega]
    · simp [hki, hlt, show ¬ k < i + 1 by omega]

private def belowLength : Cond := .lt (.var "i") (.var "length")

private def loadBody : Com :=
  .seq (.read "word") (.seq (.assign "word" (natSucc "word"))
    (.seq (.store "words" (.var "i") (.var "word"))
      (.seq (.write (.var "word")) (.assign "i" (natSucc "i")))))

private def loadLoop : Com := .while belowLength loadBody

private def replayBody : Com :=
  .seq (.write (.get "words" (.var "i"))) (.assign "i" (natSucc "i"))

private def replayLoop : Com := .while belowLength replayBody

private def startExpr (skipPrefix : Bool) : Expr :=
  if skipPrefix then .get "words" (.lit 0) else .lit 0

private def replayIf (skipPrefix : Bool) : Com :=
  .ite (.lt (.lit 0) (.var "length"))
    (.seq (.assign "i" (startExpr skipPrefix)) replayLoop) .skip

def frameProgram (skipPrefix : Bool) : Com :=
  .seq (.read "length") (.seq loadLoop
    (.seq (.write (.lit 0)) (.seq (replayIf skipPrefix) (.write (.lit 0)))))

private def frameLayout : Layout := ⟨["length", "i", "word"], ["words"], 10⟩

theorem frameProgram_ok (skipPrefix : Bool) : Com.Ok frameLayout (frameProgram skipPrefix) := by
  cases skipPrefix <;> simp [frameProgram, frameLayout, loadLoop, loadBody, replayLoop, replayBody, replayIf, startExpr,
    belowLength, natSucc, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

private theorem eval_succ {B : Nat} {σ : Env} {name : String}
    (h : σ.vars name + 1 < B) :
    (natSucc name).evalB B σ = some (σ.vars name + 1) :=
  evalB_bin (op := .add) (evalB_var (by omega)) (evalB_lit (by omega)) h

theorem frameLoad_run (xs : List Nat) {B : Nat} {σ : Env}
    (hl : σ.vars "length" = xs.length) (hi : σ.vars "i" = 0)
    (hInp : σ.inp = xs) (hArr : σ.arrs "words" = frameBuf xs 0)
    (hlen : xs.length < B) (hB : 1 < B) (hv : ∀ v ∈ xs, v + 1 < B) :
    ∃ τ, Run B loadLoop σ τ (22 * xs.length + 5) ∧
      τ.vars "length" = xs.length ∧ τ.arrs "words" = frameBuf xs xs.length ∧
      τ.out = σ.out ++ positiveWords xs := by
  let I (t : Env) : Prop := t.vars "i" ≤ xs.length ∧ t.vars "length" = xs.length ∧
    t.inp = xs.drop (t.vars "i") ∧ t.arrs "words" = frameBuf xs (t.vars "i") ∧
    t.out ++ positiveWords t.inp = σ.out ++ positiveWords xs
  let V (t : Env) : Nat := xs.length - t.vars "i"
  have hg (t : Env) (h : I t) :
      belowLength.evalB B t = some (decide (t.vars "i" < xs.length)) := by
    have e := evalB_condLt (B := B) (σ := t) (e := .var "i") (f := .var "length")
      (evalB_var (by have := h.1; omega)) (evalB_var (h.2.1 ▸ hlen))
    simpa only [belowLength, h.2.1] using e
  have hStep (t : Env) (ht : I t) (hk : belowLength.evalB B t = some true) :
      ∃ t', Run B loadBody t t' 17 ∧ I t' ∧ V t' < V t := by
    rw [hg t ht] at hk
    have hj : t.vars "i" < xs.length := by simpa using hk
    let j := t.vars "i"
    let a := xs[j]
    have ha : a + 1 < B := hv a (List.getElem_mem hj)
    have hread : t.inp = a :: xs.drop (j + 1) := by
      rw [ht.2.2.1]
      exact List.drop_eq_getElem_cons hj
    let t₁ := {t.setVar "word" a with inp := xs.drop (j + 1)}
    let t₂ := t₁.setVar "word" (a + 1)
    let t₃ := t₂.setArr "words" j (a + 1)
    let t₄ := {t₃ with out := t₃.out ++ [a + 1]}
    let t₅ := t₄.setVar "i" (j + 1)
    have r₁ : Run B (.read "word") t t₁ 1 := Run.read hread
    have e₂ : (natSucc "word").evalB B t₁ = some (a + 1) := by
      have h : t₁.vars "word" = a := by simp [t₁]
      simpa only [h] using eval_succ (σ := t₁) (name := "word") (by rw [h]; exact ha)
    have r₂ := Run.assign (x := "word") e₂
    have eᵢ : (Expr.var "i").evalB B t₂ = some j := by
      have h : t₂.vars "i" = j := by simp [t₂,t₁,j]
      simpa only [h] using evalB_var (B := B) (σ := t₂) (x := "i")
        (by rw [h]; omega)
    have eᵥ : (Expr.var "word").evalB B t₂ = some (a + 1) := by
      have h : t₂.vars "word" = a + 1 := by simp [t₂]
      simpa only [h] using evalB_var (B := B) (σ := t₂) (x := "word") (by rw [h]; exact ha)
    have hind : j < (t₂.arrs "words").length := by
      simpa [t₂,t₁, ht.2.2.2.1, frameBuf] using hj
    have r₃ := Run.store (a := "words") eᵢ eᵥ hind
    have e₄ : (Expr.var "word").evalB B t₃ = some (a + 1) := by
      simpa [t₃, evalB_var_iff, t₂, ha]
    have r₄ : Run B (.write (.var "word")) t₃ t₄ 2 := Run.write e₄
    have e₅ : (natSucc "i").evalB B t₄ = some (j + 1) := by
      have h : t₄.vars "i" = j := by simp [t₄,t₃,t₂,t₁,j]
      simpa only [h] using eval_succ (σ := t₄) (name := "i") (by rw [h]; omega)
    have hrun : Run B loadBody t t₅ (1 + (4 + (3 + (2 + 4)))) :=
      r₁.seq (r₂.seq (r₃.seq (r₄.seq (Run.assign (x := "i") e₅))))
    refine ⟨t₅, hrun.mono (by decide), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [t₅]; omega
      · simp [t₅,t₄,t₃,t₂,t₁,ht.2.1]
      · simp [t₅,t₄,t₃,t₂,t₁]
      · simp only [t₅, out_setVar, arrs_setVar, vars_setVar, if_true, t₄, t₃, arrs_setArr, t₂,
          t₁, ht.2.2.2.1]
        exact frameBuf_set xs hj
      · have heq : positiveWords t.inp = (a + 1) :: positiveWords (xs.drop (j + 1)) := by
          rw [hread]
          rfl
        have hp := congrArg (t.out ++ ·) heq
        have ht' := ht.2.2.2.2
        exact by
          change (t.out ++ [a + 1]) ++ positiveWords (xs.drop (j + 1)) =
            σ.out ++ positiveWords xs
          rw [List.append_assoc, List.singleton_append, ← hp]
          exact ht'
    · simp [V,t₅,j]; omega
  have hInit : I σ := by simp [I, hl, hi, hInp, hArr]
  obtain ⟨τ, hrun, ht, hf⟩ := Run.while_count I V 17 (fun t h => ⟨_, hg t h⟩) hStep hInit
  rw [hg τ ht] at hf
  have hfinal : τ.vars "i" = xs.length := by
    have h := ht.1
    have : ¬ τ.vars "i" < xs.length := by simpa using hf
    omega
  have hnil : τ.inp = [] := by simp [ht.2.2.1, hfinal]
  refine ⟨τ, hrun.mono ?_, ht.2.1, ?_, ?_⟩
  · simp [belowLength,V,hi]; omega
  · simpa [hfinal] using ht.2.2.2.1
  · simpa [hnil, positiveWords] using ht.2.2.2.2

theorem frameReplay_run (xs : List Nat) {B : Nat} {σ : Env} {start : Nat}
    (hl : σ.vars "length" = xs.length) (hs : σ.vars "i" = start)
    (hArr : σ.arrs "words" = frameBuf xs xs.length)
    (hlen : xs.length < B) (hStart : start < B) (hv : ∀ v ∈ xs, v + 1 < B) :
    ∃ τ, Run B replayLoop σ τ (16 * xs.length + 5) ∧
      τ.out = σ.out ++ positiveWords (xs.drop start) := by
  let I (t : Env) : Prop := t.vars "i" < B ∧ t.vars "length" = xs.length ∧
    t.arrs "words" = frameBuf xs xs.length ∧
    t.out ++ positiveWords (xs.drop (t.vars "i")) = σ.out ++ positiveWords (xs.drop start)
  let V (t : Env) : Nat := xs.length - t.vars "i"
  have hg (t : Env) (h : I t) : belowLength.evalB B t =
      some (decide (t.vars "i" < xs.length)) := by
    have e := evalB_condLt (σ := t) (B := B) (e := .var "i") (f := .var "length")
      (evalB_var h.1) (evalB_var (by rw [h.2.1]; exact hlen))
    simpa only [belowLength, h.2.1] using e
  have hstep (t : Env) (ht : I t) (hc : belowLength.evalB B t = some true) :
      ∃ t', Run B replayBody t t' 9 ∧ I t' ∧ V t' < V t := by
    rw [hg t ht] at hc
    have hi : t.vars "i" < xs.length := by simpa using hc
    let j := t.vars "i"
    let a := xs[j] + 1
    have ha : a < B := hv xs[j] (List.getElem_mem hi)
    have e : (Expr.get "words" (.var "i")).evalB B t = some a := by
      refine evalB_get (evalB_var ht.1) ?_ ha
      rw [ht.2.2.1, frameBuf, getElem?_arrOf _ hi]
      simp [hi, a, j, List.getD_eq_getElem?_getD]
    let t₁ := {t with out := t.out ++ [a]}
    let t₂ := t₁.setVar "i" (j + 1)
    have e₂ : (natSucc "i").evalB B t₁ = some (j + 1) :=
      eval_succ (σ := t₁) (name := "i") (by change j + 1 < B; omega)
    have r₁ : Run B (.write (.get "words" (.var "i"))) t t₁ 3 := Run.write e
    have hrun : Run B replayBody t t₂ (3 + 4) := r₁.seq (Run.assign (x := "i") e₂)
    refine ⟨t₂, hrun.mono (by decide), ?_, ?_⟩
    · refine ⟨?_, by simp [t₂,t₁,ht.2.1], ?_, ?_⟩
      · simp [t₂]; omega
      · simpa [t₂,t₁] using ht.2.2.1
      · have heq : positiveWords (xs.drop (t.vars "i")) =
            a :: positiveWords (xs.drop (j + 1)) := by
          rw [List.drop_eq_getElem_cons hi]
          rfl
        have hp := congrArg (t.out ++ ·) heq
        exact by
          change (t.out ++ [a]) ++ positiveWords (xs.drop (j + 1)) =
            σ.out ++ positiveWords (xs.drop start)
          rw [List.append_assoc, List.singleton_append, ← hp]
          exact ht.2.2.2
    · simp [V,t₂,j]; omega
  obtain ⟨τ, hrun, ht, hf⟩ := Run.while_count I V 9 (fun t h => ⟨_, hg t h⟩) hstep
    ⟨by rw [hs]; exact hStart, hl, hArr, by rw [hs]⟩
  rw [hg τ ht] at hf
  have hfinal : xs.length ≤ τ.vars "i" := by simpa using hf
  refine ⟨τ, hrun.mono ?_, ?_⟩
  · simp [belowLength,V,hs]; omega
  · simpa [List.drop_eq_nil_of_le hfinal, positiveWords] using ht.2.2.2

theorem framed_ramPolytime (skipPrefix : Bool) : RamPolytime (framed skipPrefix) := by
  apply ramPolytime_of_bounded_imp frameLayout (frameProgram skipPrefix) (framed skipPrefix)
    (Polynomial.C 3) (40 * Polynomial.X + 30) (frameProgram_ok skipPrefix)
  intro xs
  let B := 2 ^ (3 + bitSize xs + 1)
  have hB : 1 < B := by
    dsimp [B]
    exact Nat.one_lt_two_pow (by omega)
  have hl := Lax51Proofs.Encoding.length_le_bitSize xs
  have hlen : xs.length < B := (Nat.lt_two_pow_self (n := xs.length)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hv : ∀ v ∈ xs, v + 1 < B := by
    intro v h
    have h₀ := Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one h
    exact lt_of_le_of_lt (Nat.succ_le_of_lt h₀)
      (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) (by omega))
  let σ := initEnv (fun _ => xs.length) (xs.length :: xs)
  let σ₀ := {σ.setVar "length" xs.length with inp := xs}
  have hread : Run B (.read "length") σ σ₀ 1 := Run.read rfl
  have hArr : σ₀.arrs "words" = frameBuf xs 0 := by
    simp [σ₀,σ,initEnv,frameBuf,replicate_eq_arrOf]
  obtain ⟨τ,hload,hlen',ha,ho⟩ := frameLoad_run xs (σ := σ₀)
    (by simp [σ₀]) (by simp [σ₀,σ,initEnv]) rfl hArr hlen hB hv
  let τ₀ := {τ with out := τ.out ++ [0]}
  have hzero : Run B (.write (.lit 0)) τ τ₀ 2 := Run.write (evalB_lit (by omega))
  have htail : ∃ ω, Run B (replayIf skipPrefix) τ₀ ω (16 * xs.length + 12) ∧
      ω.out = τ₀.out ++ positiveWords (xs.drop (routeStart skipPrefix xs)) := by
    by_cases hN : 0 < xs.length
    · have hhd : xs.headD 0 = xs[0] := by cases xs with | nil => simp at hN | cons => rfl
      have h0 : xs[0] + 1 < B := hv _ (List.getElem_mem hN)
      have hstart : routeStart skipPrefix xs < B := by
        cases skipPrefix
        · change 0 < B
          omega
        · change xs.headD 0 + 1 < B
          rwa [hhd]
      have e : (startExpr skipPrefix).evalB B τ₀ = some (routeStart skipPrefix xs) := by
        cases skipPrefix
        · exact evalB_lit (by omega)
        · change (Expr.get "words" (.lit 0)).evalB B τ₀ = some (xs.headD 0 + 1)
          rw [hhd]
          refine evalB_get (evalB_lit (by omega)) ?_ h0
          change (τ.arrs "words")[0]? = some (xs[0] + 1)
          rw [ha, frameBuf, getElem?_arrOf _ hN]
          simp [hN,List.getD_eq_getElem?_getD]
      let τ₁ := τ₀.setVar "i" (routeStart skipPrefix xs)
      have hass : Run B (.assign "i" (startExpr skipPrefix)) τ₀ τ₁ 3 := by
        apply (Run.assign e).mono
        cases skipPrefix <;> decide
      obtain ⟨ω,hre,how⟩ := frameReplay_run xs (σ := τ₁)
        (by simpa [τ₁,τ₀] using hlen') (by simp [τ₁]) (by simpa [τ₁,τ₀] using ha)
        hlen hstart hv
      have hguard : (Cond.lt (.lit 0) (.var "length")).evalB B τ₀ = some true := by
        have hh := evalB_condLt (σ := τ₀) (B := B)
          (evalB_lit (n := 0) (by omega)) (evalB_var (x := "length") (by simpa [τ₀,hlen'] using hlen))
        simpa [τ₀,hlen',hN] using hh
      refine ⟨ω, (Run.ite_true (d := .skip) hguard (hass.seq hre)).mono ?_, ?_⟩
      · simp <;> omega
      · simpa [τ₁] using how
    · have hnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hguard : (Cond.lt (.lit 0) (.var "length")).evalB B τ₀ = some false := by
        have hh := evalB_condLt (σ := τ₀) (B := B)
          (evalB_lit (n := 0) (by omega)) (evalB_var (x := "length") (by simpa [τ₀,hlen'] using hlen))
        simpa [τ₀,hlen',hN] using hh
      refine ⟨τ₀, (Run.ite_false (c := .seq (.assign "i" (startExpr skipPrefix)) replayLoop)
        hguard Run.skip).mono ?_, ?_⟩
      · simp <;> omega
      · simp [hnil, positiveWords]
  obtain ⟨ω,hre,how⟩ := htail
  have hend : Run B (.write (.lit 0)) ω {ω with out := ω.out ++ [0]} 2 :=
    Run.write (evalB_lit (by omega))
  have hw : Run B (frameProgram skipPrefix) σ {ω with out := ω.out ++ [0]} _ :=
    hread.seq (hload.seq (hzero.seq (hre.seq hend)))
  refine ⟨fun _ => xs.length, {ω with out := ω.out ++ [0]}, ?_, ?_⟩
  · simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact hw.mono (by omega)
  · simp [framed, how, τ₀, ho, σ₀, σ, initEnv, List.append_assoc]

theorem comparisonFrame_turingPolytime : TuringPolytime comparisonFrame :=
  Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime (framed_ramPolytime true)

theorem duplicateFrame_turingPolytime : TuringPolytime (fun w => packSegments [w,w]) := by
  have he : (fun w => packSegments [w,w]) = framed false := by
    funext w
    simp [packSegments, framed, routeStart, List.append_assoc]
  rw [he]
  exact Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime (framed_ramPolytime false)

#print axioms comparisonFrame_turingPolytime
#print axioms duplicateFrame_turingPolytime
end EvenTI.P12CountPre

