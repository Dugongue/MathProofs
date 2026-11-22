import EvenP11OracleIntegration
import EvenP10TrialWordAttempt
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12Compare

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime
open EvenTI.P10Oracle

set_option autoImplicit false

/-- Phases 0, 1, 2 and 3 denote a segment start, skipping a failed
segment, copying a successful segment and ignoring later segments. -/
def selectNext (p a : ℕ) : ℕ :=
  if p = 0 then (if a = 0 then 0 else if 1 < a then 2 else 1)
  else if p = 1 then (if a = 0 then 0 else 1)
  else if p = 2 then (if a = 0 then 3 else 2) else p

def selectEmit (p a : ℕ) : List ℕ :=
  if a ≠ 0 ∧ (p = 2 ∨ p = 0 ∧ 1 < a) then [a - 1] else []

def selectTrace (p : ℕ) : List ℕ → ℕ × List ℕ
  | [] => (p, [])
  | a :: xs =>
    let z := selectTrace (selectNext p a) xs
    (z.1, selectEmit p a ++ z.2)

def selectFinish (p : ℕ) : List ℕ := if p < 2 then [0] else []

def selectPacked (xs : List ℕ) : List ℕ :=
  let z := selectTrace 0 xs
  z.2 ++ selectFinish z.1

def phase (p : ℕ) : Com := .assign "p" (.lit p)
def phaseIs (p : ℕ) : Cond := .eq (.var "p") (.lit p)
def emptyWord : Cond := .eq (.var "x") (.lit 0)
def successWord : Cond := .lt (.lit 1) (.var "x")
def writeWord : Com := .write (.sub (.var "x") (.lit 1))

def selectDispatch : Com :=
  .ite (phaseIs 0)
    (.ite emptyWord .skip (.ite successWord (.seq writeWord (phase 2)) (phase 1)))
    (.ite (phaseIs 1) (.ite emptyWord (phase 0) .skip)
      (.ite (phaseIs 2) (.ite emptyWord (phase 3) writeWord) .skip))

def selectBody : Com :=
  .seq (.read "x") (.seq selectDispatch (.assign "left" (.sub (.var "left") (.lit 1))))

def selectGuard : Cond := .lt (.lit 0) (.var "left")

def selectProgram : Com :=
  .seq (.read "left") (.seq (phase 0)
    (.seq (.while selectGuard selectBody)
      (.ite (.lt (.var "p") (.lit 2)) (.write (.lit 0)) .skip)))

def selectLayout : Layout := ⟨["left", "p", "x"], [], 5⟩

theorem selectProgram_ok : Com.Ok selectLayout selectProgram := by
  simp [selectProgram, selectGuard, selectBody, selectLayout, selectDispatch, phaseIs,
    emptyWord, successWord, phase, writeWord, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

private theorem phaseIs_eval {B : ℕ} {σ : Env} {p : ℕ}
    (hm : σ.vars "p" < B) (hp : p < B) :
    (phaseIs p).evalB B σ = some (decide (σ.vars "p" = p)) :=
  evalB_condEq (evalB_var hm) (evalB_lit hp)

private theorem emptyWord_eval {B : ℕ} {σ : Env} (hB : 4 < B) (hm : σ.vars "x" < B) :
    emptyWord.evalB B σ = some (decide (σ.vars "x" = 0)) :=
  evalB_condEq (evalB_var hm) (evalB_lit (by omega))

private theorem successWord_eval {B : ℕ} {σ : Env} (hB : 4 < B) (hm : σ.vars "x" < B) :
    successWord.evalB B σ = some (decide (1 < σ.vars "x")) :=
  evalB_condLt (evalB_lit (by omega)) (evalB_var hm)

private theorem writeWord_run {B : ℕ} {σ : Env} (hB : 4 < B) (hm : σ.vars "x" < B) :
    Run B writeWord σ {σ with out := σ.out ++ [σ.vars "x" - 1]} 4 :=
  Run.write (evalB_bin (evalB_var hm) (evalB_lit (by omega)) (by simp; omega))

private theorem selectNext_le {p a : ℕ} (hp : p ≤ 3) : selectNext p a ≤ 3 := by
  unfold selectNext
  split_ifs <;> omega

private theorem selectDispatch_run {B : ℕ} {σ : Env} (hB : 4 < B)
    (hp : σ.vars "p" ≤ 3) (ha : σ.vars "x" < B) :
    ∃ τ, Run B selectDispatch σ τ 32 ∧
      τ.vars "p" = selectNext (σ.vars "p") (σ.vars "x") ∧
      τ.vars "left" = σ.vars "left" ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ selectEmit (σ.vars "p") (σ.vars "x") := by
  have e0 := phaseIs_eval (σ := σ) (p := 0) (by omega : σ.vars "p" < B) (by omega)
  have e1 := phaseIs_eval (σ := σ) (p := 1) (by omega : σ.vars "p" < B) (by omega)
  have e2 := phaseIs_eval (σ := σ) (p := 2) (by omega : σ.vars "p" < B) (by omega)
  have eZ := emptyWord_eval hB ha
  have eS := successWord_eval hB ha
  have step (j : ℕ) (hj : j < B) (t : Env) : Run B (phase j) t (t.setVar "p" j) 2 :=
    Run.assign (evalB_lit hj)
  by_cases hp0 : σ.vars "p" = 0
  · have e0t : (phaseIs 0).evalB B σ = some true := by simpa [hp0] using e0
    by_cases hz : σ.vars "x" = 0
    · have ezt : emptyWord.evalB B σ = some true := by simpa [hz] using eZ
      refine ⟨σ, (Run.ite_true e0t (Run.ite_true ezt Run.skip)).mono ?_, ?_⟩
      · decide
      · simp [selectNext, selectEmit, hp0, hz]
    · have ezf : emptyWord.evalB B σ = some false := by simpa [hz] using eZ
      by_cases hs : 1 < σ.vars "x"
      · have est : successWord.evalB B σ = some true := by simpa [hs] using eS
        let t : Env := {σ with out := σ.out ++ [σ.vars "x" - 1]}
        refine ⟨t.setVar "p" 2, (Run.ite_true e0t (Run.ite_false ezf
          (Run.ite_true est ((writeWord_run hB ha).seq (step 2 (by omega) t))))).mono ?_, ?_⟩
        · decide
        · simp [t, Env.setVar, selectNext, selectEmit, hp0, hz, hs]
      · have esf : successWord.evalB B σ = some false := by simpa [hs] using eS
        refine ⟨σ.setVar "p" 1, (Run.ite_true e0t (Run.ite_false ezf
          (Run.ite_false esf (step 1 (by omega) σ)))).mono ?_, ?_⟩
        · decide
        · simp [Env.setVar, selectNext, selectEmit, hp0, hz, hs]
  · have e0f : (phaseIs 0).evalB B σ = some false := by simpa [hp0] using e0
    by_cases hp1 : σ.vars "p" = 1
    · have e1t : (phaseIs 1).evalB B σ = some true := by simpa [hp1] using e1
      by_cases hz : σ.vars "x" = 0
      · have ezt : emptyWord.evalB B σ = some true := by simpa [hz] using eZ
        refine ⟨σ.setVar "p" 0, (Run.ite_false e0f (Run.ite_true e1t
          (Run.ite_true ezt (step 0 (by omega) σ)))).mono ?_, ?_⟩
        · decide
        · simp [Env.setVar, selectNext, selectEmit, hp1, hz]
      · have ezf : emptyWord.evalB B σ = some false := by simpa [hz] using eZ
        refine ⟨σ, (Run.ite_false e0f (Run.ite_true e1t (Run.ite_false ezf Run.skip))).mono ?_, ?_⟩
        · decide
        · simp [selectNext, selectEmit, hp1, hz]
    · have e1f : (phaseIs 1).evalB B σ = some false := by simpa [hp1] using e1
      by_cases hp2 : σ.vars "p" = 2
      · have e2t : (phaseIs 2).evalB B σ = some true := by simpa [hp2] using e2
        by_cases hz : σ.vars "x" = 0
        · have ezt : emptyWord.evalB B σ = some true := by simpa [hz] using eZ
          refine ⟨σ.setVar "p" 3, (Run.ite_false e0f (Run.ite_false e1f
            (Run.ite_true e2t (Run.ite_true ezt (step 3 (by omega) σ))))).mono ?_, ?_⟩
          · decide
          · simp [Env.setVar, selectNext, selectEmit, hp2, hz]
        · have ezf : emptyWord.evalB B σ = some false := by simpa [hz] using eZ
          refine ⟨{σ with out := σ.out ++ [σ.vars "x" - 1]},
            (Run.ite_false e0f (Run.ite_false e1f (Run.ite_true e2t
              (Run.ite_false ezf (writeWord_run hB ha))))).mono ?_, ?_⟩
          · decide
          · simp [selectNext, selectEmit, hp2, hz]
      · have e2f : (phaseIs 2).evalB B σ = some false := by simpa [hp2] using e2
        refine ⟨σ, (Run.ite_false e0f (Run.ite_false e1f (Run.ite_false e2f Run.skip))).mono ?_, ?_⟩
        · decide
        · simp [selectNext, selectEmit, hp0, hp1, hp2]

theorem selectLoop_run (B : ℕ) (σ : Env) (hB : 4 < B)
    (hleft : σ.vars "left" = σ.inp.length) (hsize : σ.inp.length < B)
    (hp : σ.vars "p" ≤ 3) (hv : ∀ x ∈ σ.inp, x < B) :
    ∃ τ, Run B (.while selectGuard selectBody) σ τ (45 * σ.inp.length + 8) ∧
      τ.vars "p" = (selectTrace (σ.vars "p") σ.inp).1 ∧
      τ.out = σ.out ++ (selectTrace (σ.vars "p") σ.inp).2 := by
  let z := selectTrace (σ.vars "p") σ.inp
  let I : Env → Prop := fun t => t.vars "left" = t.inp.length ∧ t.inp.length < B ∧
    t.vars "p" ≤ 3 ∧ (∀ x ∈ t.inp, x < B) ∧
    (selectTrace (t.vars "p") t.inp).1 = z.1 ∧
    t.out ++ (selectTrace (t.vars "p") t.inp).2 = σ.out ++ z.2
  have hg (t : Env) (ht : I t) : selectGuard.evalB B t = some (decide (0 < t.inp.length)) := by
    unfold selectGuard
    rw [← ht.1]
    exact evalB_condLt (evalB_lit (by omega)) (evalB_var (by have := ht.2.1; omega))
  have hs (t : Env) (ht : I t) (hc : selectGuard.evalB B t = some true) :
      ∃ u, Run B selectBody t u 37 ∧ I u ∧ u.inp.length < t.inp.length := by
    rw [hg t ht] at hc
    cases hi : t.inp with
    | nil => simp [hi] at hc
    | cons a xs =>
      let s : Env := {t.setVar "x" a with inp := xs}
      have hread : Run B (.read "x") t s 1 := Run.read hi
      have hpa : s.vars "p" ≤ 3 := by simpa [s, Env.setVar] using ht.2.2.1
      have hsa : s.vars "x" < B := by
        simpa [s, Env.setVar] using ht.2.2.2.1 a (by simp [hi])
      obtain ⟨v, hr, hvp, hvl, hvi, hvo⟩ := selectDispatch_run hB hpa hsa
      have hvleft : v.vars "left" = xs.length + 1 := by
        simpa [s, Env.setVar, ht.1, hi] using hvl
      have hL : v.vars "left" < B := by
        rw [hvleft]
        simpa [hi] using ht.2.1
      have hSub : (Expr.sub (.var "left") (.lit 1)).evalB B v = some xs.length := by
        have he := evalB_bin (op := .sub) (evalB_var hL)
          (evalB_lit (by omega : 1 < B))
          (show Bop.sub.apply (v.vars "left") 1 < B by simp [hvleft]; omega)
        simpa [hvleft] using he
      let u := v.setVar "left" xs.length
      have hrun : Run B selectBody t u (1 + (32 + 4)) :=
        hread.seq (hr.seq (Run.assign hSub))
      have hUp : u.vars "p" = selectNext (t.vars "p") a := by
        simpa [u, s, Env.setVar] using hvp
      have hUi : u.inp = xs := by simpa [u, s, Env.setVar] using hvi
      have hUo : u.out = t.out ++ selectEmit (t.vars "p") a := by
        simpa [u, s, Env.setVar] using hvo
      refine ⟨u, hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · change xs.length = u.inp.length
        rw [hUi]
      · rw [hUi]
        have := ht.2.1
        simp [hi] at this
        omega
      · rw [hUp]; exact selectNext_le ht.2.2.1
      · rw [hUi]
        intro a hm
        apply ht.2.2.2.1
        simp [hi, hm]
      · rw [hUi, hUp]
        have hh := ht.2.2.2.2.1
        rw [hi] at hh
        exact hh
      · rw [hUo, hUi, hUp, List.append_assoc]
        have hh := ht.2.2.2.2.2
        rw [hi] at hh
        exact hh
      · simp [hUi, hi]
  obtain ⟨τ, hr, hτ, hfalse⟩ := Run.while_count I (fun t => t.inp.length) 37
    (fun t ht => ⟨_, hg t ht⟩) hs ⟨hleft,hsize,hp,hv,rfl,rfl⟩
  rw [hg τ hτ] at hfalse
  have hnil : τ.inp = [] := List.length_eq_zero_iff.mp (by simpa using hfalse)
  refine ⟨τ, hr.mono ?_, ?_, ?_⟩
  · simp [selectGuard, size_condLt, size_lit, size_var]
    omega
  · simpa [hnil, selectTrace] using hτ.2.2.2.2.1
  · simpa [hnil, selectTrace] using hτ.2.2.2.2.2

private theorem selectTrace_phase_le (p : ℕ) (xs : List ℕ) (hp : p ≤ 3) :
    (selectTrace p xs).1 ≤ 3 := by
  induction xs generalizing p with
  | nil => exact hp
  | cons a rest ih => exact ih _ (selectNext_le hp)
theorem selectPacked_ramPolytime : RamPolytime selectPacked := by
  apply ramPolytime_of_bounded_imp selectLayout selectProgram selectPacked
    (Polynomial.C 3) (45 * Polynomial.X + 30) selectProgram_ok
  intro xs
  have hx := Lax51Proofs.Encoding.length_le_bitSize xs
  let B := 2 ^ ((Polynomial.C 3 : Polynomial ℕ).eval (bitSize xs) + bitSize xs + 1)
  have hB : 4 < B := by
    dsimp [B]
    simp only [Polynomial.eval_C]
    exact (show 4 < 2^3 by decide).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hl : xs.length < B := by
    dsimp [B]
    simp only [Polynomial.eval_C]
    exact (Nat.lt_two_pow_self (n := xs.length)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hv : ∀ v ∈ xs, v < B := by
    intro v hm
    dsimp [B]
    simp only [Polynomial.eval_C]
    exact (Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one hm).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  let σ := initEnv (fun _ => 0) (xs.length :: xs)
  let s := {σ.setVar "left" xs.length with inp := xs}
  let t := s.setVar "p" 0
  have hr : Run B (.read "left") σ s 1 := Run.read rfl
  have hinit : Run B (phase 0) s t 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ, ht, hphase, hout⟩ := selectLoop_run B t hB (by simp [t, s, Env.setVar]) hl
    (by simp [t, Env.setVar]) hv
  have hval : τ.vars "p" ≤ 3 := by
    rw [hphase]
    simp only [t, s, Env.setVar, if_pos rfl]
    exact selectTrace_phase_le 0 xs (by decide)
  have htest : (Cond.lt (.var "p") (.lit 2)).evalB B τ =
      some (decide (τ.vars "p" < 2)) :=
    evalB_condLt (evalB_var (by omega)) (evalB_lit (by omega))
  by_cases he : τ.vars "p" < 2
  · have htest' : (Cond.lt (.var "p") (.lit 2)).evalB B τ = some true := by simpa [he] using htest
    let u := {τ with out := τ.out ++ [0]}
    have hw : Run B (.write (.lit 0)) τ u 2 := Run.write (evalB_lit (by omega))
    refine ⟨fun _ => 0, u, (hr.seq (hinit.seq (ht.seq (Run.ite_true htest' hw)))).mono ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp [t, s, size_condLt, size_lit, size_var]
      omega
    · have hp' : (selectTrace 0 xs).1 < 2 := by simpa [hphase, t, s, Env.setVar] using he
      simp [u, hout, selectPacked, selectFinish, hp', t, s, σ, Env.setVar, initEnv]
  · have htest' : (Cond.lt (.var "p") (.lit 2)).evalB B τ = some false := by simpa [he] using htest
    refine ⟨fun _ => 0, τ, (hr.seq (hinit.seq (ht.seq (Run.ite_false htest' Run.skip)))).mono ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      simp [t, s, size_condLt, size_lit, size_var]
      omega
    · have hp' : ¬ (selectTrace 0 xs).1 < 2 := by simpa [hphase, t, s, Env.setVar] using he
      simp [hout, selectPacked, selectFinish, hp', t, s, σ, Env.setVar, initEnv]

theorem selectPacked_turingPolytime : TuringPolytime selectPacked :=
  Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime selectPacked_ramPolytime

#print axioms selectPacked_turingPolytime

end EvenTI.P12Compare
