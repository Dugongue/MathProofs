import EvenP13SpectralAnchorDigits
import EvenP10TrialPayloadDecode

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.P10Scan

def shapeSide : String := "even.anchor.shape.side"
def nonemptyAnchor : Cond := .lt (.lit 0) (.var anchorLength)
def positiveSide : Cond := .lt (.lit 0) (.var shapeSide)
def smallSide : Cond := .lt (.var shapeSide) (.add (.var anchorLength) (.lit 1))
def squareLength : Cond :=
  .eq (.add (squareE (.var shapeSide)) (.lit 1)) (.var anchorLength)

def markShapeBody (input : String) : Com :=
  .seq (.assign shapeSide (.get input (.lit 0)))
    (.ite positiveSide
      (.ite smallSide (.ite squareLength (.assign digitGood (.lit 1)) .skip) .skip)
      .skip)

def markShape (input : String) : Com :=
  .seq (.assign digitGood (.lit 0)) (.ite nonemptyAnchor (markShapeBody input) .skip)

def anchorShape : List Nat → Prop
  | n :: xs => 0 < n ∧ xs.length = n*n
  | [] => False

theorem markShape_run (input : String) (ws : List Nat) {B : Nat} {σ : Env}
    (hArr : σ.arrs input = ws) (hLen : σ.vars anchorLength = ws.length)
    (hFit : ws.length*ws.length+2 < B)
    (hWords : ∀ w ∈ ws, w < B) :
    ∃ τ, Run B (markShape input) σ τ 45 ∧
      (τ.vars digitGood = 1 ↔ anchorShape ws) ∧ τ.vars digitGood ≤ 1 ∧ Frame (markShape input) σ τ := by
  let s := σ.setVar digitGood 0
  have ho : 1 < B := by omega
  have hr : Run B (.assign digitGood (.lit 0)) σ s 2 :=
    Run.assign (evalB_lit (by omega))
  have hL : s.vars anchorLength = ws.length := by
    simp only [s,vars_setVar,show anchorLength ≠ digitGood by decide,if_false]
    exact hLen
  have hLb : ws.length < B := (Nat.le_mul_self _).trans_lt (by omega)
  have hG : nonemptyAnchor.evalB B s = some (decide (0 < ws.length)) := by
    have e := evalB_condLt (B := B) (σ := s) (e := .lit 0) (f := .var anchorLength)
      (evalB_lit (by omega)) (evalB_var (by rw [hL]; exact hLb))
    simpa only [nonemptyAnchor,hL] using e
  cases ws with
  | nil =>
    have g' : nonemptyAnchor.evalB B s = some false := by rw [hG]; rfl
    have run : Run B (markShape input) σ s 45 :=
      (hr.seq (Run.ite_false g' Run.skip)).mono (by decide)
    exact ⟨s,run,by simp [s,vars_setVar,anchorShape],by simp [s,vars_setVar],Frame.of_run run⟩
  | cons n xs =>
    have hG' : nonemptyAnchor.evalB B s = some true := by rw [hG]; simp
    let t := s.setVar shapeSide n
    have hn := hWords n (by simp)
    have eN : (Expr.get input (.lit 0)).evalB B s = some n :=
      evalB_get (evalB_lit (by omega)) (by simp [s,hArr]) hn
    have rN : Run B (.assign shapeSide (.get input (.lit 0))) s t 3 := Run.assign eN
    have hN : t.vars shapeSide = n := by simp [t,vars_setVar]
    have hLt : t.vars anchorLength = (n::xs).length := by
      simpa [t,shapeSide,anchorLength,vars_setVar] using hL
    have hnE : (Expr.var shapeSide).evalB B t = some n := by
      rw [← hN]; exact evalB_var (hN ▸ hn)
    have eP : positiveSide.evalB B t = some (decide (0 < n)) :=
      evalB_condLt (evalB_lit (by omega)) hnE
    have wrap (u : Env) (ru : Run B
        (.ite positiveSide
          (.ite smallSide (.ite squareLength (.assign digitGood (.lit 1)) .skip) .skip)
          .skip) t u 32) (hu : (u.vars digitGood = 1 ↔ anchorShape (n::xs)) ∧ u.vars digitGood ≤ 1) :
        ∃ τ, Run B (markShape input) σ τ 45 ∧
          (τ.vars digitGood = 1 ↔ anchorShape (n::xs)) ∧ τ.vars digitGood ≤ 1 ∧ Frame (markShape input) σ τ := by
      have run : Run B (markShape input) σ u 45 := (hr.seq (Run.ite_true hG' (rN.seq ru))).mono
        (by decide)
      exact ⟨u,run,hu.1,hu.2,Frame.of_run run⟩
    by_cases hp : 0 < n
    · have eP' : positiveSide.evalB B t = some true := by rw [eP]; simp [hp]
      have hplus : (n::xs).length+1 < B := by
        have hm := Nat.le_mul_self (n::xs).length
        omega
      have el : (Expr.var anchorLength).evalB B t = some (n::xs).length := by
        rw [← hLt]; exact evalB_var (hLt ▸ hLb)
      have eL : (Expr.add (.var anchorLength) (.lit 1)).evalB B t =
          some ((n::xs).length+1) := evalB_bin el (evalB_lit ho) hplus
      have es : smallSide.evalB B t = some (decide (n < (n::xs).length+1)) :=
        evalB_condLt hnE eL
      by_cases hnL : n < (n::xs).length+1
      · have es' : smallSide.evalB B t = some true := by rw [es]; exact congrArg some (decide_eq_true hnL)
        have hh : n*n+1 < B := by
          have hsmall : n ≤ (n::xs).length := Nat.le_of_lt_succ hnL
          have hm := Nat.mul_le_mul hsmall hsmall
          omega
        have en : (squareE (.var shapeSide)).evalB B t = some (n*n) :=
          evalB_bin hnE hnE (by change n*n < B; omega)
        have elev : (Expr.add (squareE (.var shapeSide)) (.lit 1)).evalB B t =
            some (n*n+1) := evalB_bin en (evalB_lit ho) hh
        have eq : squareLength.evalB B t = some (decide (n*n+1 = (n::xs).length)) :=
          evalB_condEq elev el
        by_cases hl : n*n+1 = (n::xs).length
        · have eq' : squareLength.evalB B t = some true := by rw [eq]; simp [hl]
          apply wrap (t.setVar digitGood 1)
          · exact (Run.ite_true eP' (Run.ite_true es'
              (Run.ite_true eq' (Run.assign (evalB_lit ho))))).mono
              (by norm_num [positiveSide,smallSide,squareLength,squareE,Cond.size,Expr.size])
          · simp [anchorShape,vars_setVar,hp]
            simp only [List.length_cons] at hl
            omega
        · have eq' : squareLength.evalB B t = some false := by rw [eq]; exact congrArg some (decide_eq_false hl)
          apply wrap t
          · exact (Run.ite_true eP' (Run.ite_true es' (Run.ite_false eq' Run.skip))).mono
              (by norm_num [positiveSide,smallSide,squareLength,squareE,Cond.size,Expr.size])
          · simp only [List.length_cons] at hl
            have hx : xs.length ≠ n*n := by omega
            simp [t,s,vars_setVar,digitGood,shapeSide,anchorShape,hp,hx,Ne.symm hx]
      · have es' : smallSide.evalB B t = some false := by rw [es]; exact congrArg some (decide_eq_false hnL)
        apply wrap t
        · exact (Run.ite_true eP' (Run.ite_false es' Run.skip)).mono
            (by norm_num [positiveSide,smallSide,Cond.size,Expr.size])
        · have hfalse : xs.length ≠ n*n := by
            intro h
            have hn₂ := Nat.le_mul_self n
            simp only [List.length_cons] at hnL
            omega
          simp [t,s,vars_setVar,digitGood,shapeSide,anchorShape,hfalse,Ne.symm hfalse]
    · have eP' : positiveSide.evalB B t = some false := by rw [eP]; simp [hp]
      apply wrap t
      · exact (Run.ite_false eP' Run.skip).mono
          (by norm_num [positiveSide,Cond.size,Expr.size])
      · simp [t,s,vars_setVar,digitGood,shapeSide,anchorShape,hp]

#print axioms markShape_run
end EvenTI.P13Spectral
