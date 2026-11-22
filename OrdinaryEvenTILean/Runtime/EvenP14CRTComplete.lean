import EvenP14CRTLoop
import EvenP14CRTPositive
import EvenP14CRTEmpty

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open EvenTI.P12Compare (crtActive coordinateBank crtRhsBank fixedCoordinateRhs recoverLinear smithRecoverAndCommitCost smithRecoverAndCommitCost_le)
open EvenTI.P12ComparePrep (cutNonzero)

private def emptyRecovery : Com :=
  .seq emptyCoordinateVerdict (.assign crtActive (.sub (.lit 1) (.var cutNonzero)))

def completeCoordinateRecovery : Com :=
  .ite (.eq (.var inputColsR) (.lit 0)) emptyRecovery recoverAllCoordinates

def completeCoordinateRecoveryCost (M m n : ℕ) : ℕ :=
  recoverAllCoordinatesCost M m n+44*m+36

/-- Executable coordinate recovery agrees with the original linear solver,
including the empty-coordinate right-hand-side verification. -/
theorem completeCoordinateRecovery_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hInit : ConstraintBanks A b 0 0 s)
    (hScratch : n = 0 → m ≤ (s.arrs EvenTI.P12ComparePrep.coefficientBank).length) :
    ∃ t, Run W completeCoordinateRecovery s t (completeCoordinateRecoveryCost M m n) ∧
      Frame completeCoordinateRecovery s t ∧
      match recoverLinear A b with
      | some v => t.vars crtActive = 1 ∧ ∀ i, (t.arrs coordinateBank).getD i.val 0 = (v i).val
      | none => t.vars crtActive = 0 := by
  let g : Cond := .eq (.var inputColsR) (.lit 0)
  have h1 : 1 < W := by omega
  have hnW : n < W := by omega
  have eg : g.evalB W s = some (decide (n = 0)) :=
    evalB_condEq (evalB_var_iff.mpr ⟨hs.cols.symm,hs.cols ▸ hnW⟩) (evalB_lit (by omega))
  by_cases h0 : n = 0
  · subst n
    have hRhs : s.arrs crtRhsBank = List.ofFn fun j => (b j).val := by
      rw [hInit.rhs]
      congr 1
      funext j
      simp [fixedCoordinateRhs,j.isLt]
    obtain ⟨u,ru,hBit,hResult,_⟩ := emptyCoordinateVerdict_run A b (by omega) h1 (by omega)
      hs.base hRhs (hScratch rfl)
    let t := u.setVar crtActive (1-u.vars cutNonzero)
    have et : (Expr.sub (.lit 1) (.var cutNonzero)).evalB W u = some (1-u.vars cutNonzero) :=
      evalB_bin (op:=.sub) (evalB_lit h1) (evalB_var (by omega)) (by change 1-u.vars cutNonzero < W; omega)
    have rt : Run W (.assign crtActive (.sub (.lit 1) (.var cutNonzero))) u t 4 := Run.assign et
    have eg' : g.evalB W s = some true := by simpa using eg
    have hr : Run W completeCoordinateRecovery s t (completeCoordinateRecoveryCost M m 0) :=
      (Run.ite_true (d:=recoverAllCoordinates) eg' (ru.seq rt)).mono (by
        simp [completeCoordinateRecoveryCost,recoverAllCoordinatesCost,g,Cond.size,Expr.size] <;> omega)
    refine ⟨t,hr,Frame.of_run hr,?_⟩
    cases hx : recoverLinear A b with
    | none =>
      have hOut : u.vars cutNonzero ≠ 0 := by
        intro h
        simpa [hx] using hResult.mp h
      have hu : 1-u.vars cutNonzero = 0 := by omega
      simp [t,hu]
    | some v =>
      have hu : u.vars cutNonzero = 0 := hResult.mpr (by simp [hx])
      exact ⟨by simp [t,hu],fun i => Fin.elim0 i⟩
  · have eg' : g.evalB W s = some false := by simpa [h0] using eg
    obtain ⟨t,rt,_,_,_,hout⟩ := recoverAllCoordinates_run A b hW hL hs hInit
    have hr : Run W completeCoordinateRecovery s t (completeCoordinateRecoveryCost M m n) :=
      (Run.ite_false (c:=emptyRecovery) eg' rt).mono (by
        simp [completeCoordinateRecoveryCost,g,Cond.size,Expr.size] <;> omega)
    refine ⟨t,hr,Frame.of_run hr,?_⟩
    rw [fixPaddedCoordinates_eq_recoverLinear A b (Nat.pos_of_ne_zero h0)] at hout
    cases h : recoverLinear A b <;> simpa only [h] using hout

/-- A single polynomial covers the replay, Smith and CRT calls, coordinate
writes, controller, and the separate zero-column scan. -/
theorem completeCoordinateRecoveryCost_le (M m n : ℕ) :
    completeCoordinateRecoveryCost M m n ≤ 833000*(Nat.size M+m+n+2)^5 := by
  let X := Nat.size M+m+n+2
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hmn : m+n+1 ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hm : m ≤ X := by dsimp [X]; omega
  have hS := (smithRecoverAndCommitCost_le M (m+n) n).trans
    (Nat.mul_le_mul_left 52000 (Nat.pow_le_pow_left (show Nat.size M+(m+n)+n+2 ≤ 2*X by dsimp [X]; omega) 4))
  rw [show 52000*(2*X)^4=832000*X^4 by ring] at hS
  have hT : (m+n+1)*n ≤ X^2 := by simpa only [pow_two] using Nat.mul_le_mul hmn hn
  have h24 : X^2 ≤ X^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h14 : 1 ≤ X^4 := one_le_pow₀ hx
  have hRound : recoverRoundCost M m n+54 ≤ 832104*X^4 := by
    unfold recoverRoundCost
    omega
  have hLoop := Nat.mul_le_mul hRound hn
  rw [show 832104*X^4*X = 832104*X^5 by ring] at hLoop
  have h15 : 1 ≤ X^5 := one_le_pow₀ hx
  have hX5 : X ≤ X^5 := by simpa using (Nat.pow_le_pow_right hx (show 1 ≤ 5 by decide))
  unfold completeCoordinateRecoveryCost recoverAllCoordinatesCost
  change (recoverRoundCost M m n+54)*n+10+44*m+36 ≤ 833000*X^5
  omega

#print axioms completeCoordinateRecoveryCost_le
#print axioms completeCoordinateRecovery_run
end EvenTI.P14Recovery