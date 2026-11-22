import Mathproof.Meta.P15DecideIMPSolve20261007
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace EvenTI.P18Scalar

open scoped BigOperators
open Matrix Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT KBLay XBs)
open Mathproof.P15DecideIMPRowKer20261007 (tRB)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC svLB svW svY svOK solveProg solveCost solve_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure InverseChartPorts (s : Env) (n CB RB AM OUT LB work YB Z : ℕ) : Prop where
  m : s.vars svM=n
  dim : s.vars svL=n
  cb : s.vars svC=CB
  rb : s.vars tRB=RB
  am : s.vars kAM=AM
  out : s.vars kOUT=OUT
  lb : s.vars svLB=LB
  work : s.vars svW=work
  y : s.vars svY=YB
  zero : s.vars dZ=Z
  one : s.vars rOs=Z+1
  first : s.vars dT=Z+2
  second : s.vars dU=Z+3

structure InverseChartGeometry (n CB RB AM OUT LB work YB Z S W : ℕ) : Prop where
  kernel : KBLay n (n+1) AM OUT Z S W
  start : (n+1+1)*XBs n (n+1) ≤ CB
  columns : CB+(n+1)*n ≤ RB
  transpose : RB+n*(n+1) ≤ AM
  out : OUT+(n+1)*(n+1) ≤ LB
  labels : LB+n+2 ≤ work
  work : work+2 ≤ YB
  y : YB+n ≤ Z

/-- One actual solve in the installed invertible chart computes the inverse
coordinates of an actual RHS column. Standard padding columns give U⁻¹P
without constructing a new action matrix for any CRT probe. -/
theorem inverseChartColumn_run (F : FieldPresentation K) {n : ℕ}
    (U : (Matrix (Fin n) (Fin n) K)ˣ) (rhs : Fin n → K)
    {CB RB AM OUT LB work YB Z S W : ℕ} {s : Env}
    (hSlots : Slots F canonical qN.WS S W s)
    (ports : InverseChartPorts s n CB RB AM OUT LB work YB Z)
    (geo : InverseChartGeometry n CB RB AM OUT LB work YB Z S W)
    (hWorkspace : s.vars qN.WS=F.e+1)
    (hChart : ∀ (i k : Fin n),
      val F canonical qN.WS s (CB+(i.val*n+k.val))=U.val k i)
    (hRhs : ∀ k : Fin n, val F canonical qN.WS s (CB+(n*n+k.val))=rhs k)
    (hZero : val F canonical qN.WS s Z=0)
    (hOne : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run W solveProg s t (solveCost F n n) ∧
      Slots F canonical qN.WS S W t ∧ t.vars svOK=1 ∧
      (∀ i : Fin n, val F canonical qN.WS t (YB+i.val)=(U.inv.mulVec rhs) i) ∧
      Frame solveProg s t ∧
      (∀ j < S, (n+1+1)*XBs n (n+1) ≤ j →
        (j < RB ∨ YB+n ≤ j) → j ≠ Z+2 → j ≠ Z+3 →
        val F canonical qN.WS t j=val F canonical qN.WS s j) := by
  let cols : Fin n → Fin n → K := fun i k => U.val k i
  let C : Fin (n+1) → Fin n → K := Fin.lastCases rhs cols
  have hData : ∀ (i : Fin (n+1)) (k : Fin n),
      val F canonical qN.WS s (CB+(i.val*n+k.val))=C i k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro k
      simpa [C] using hRhs k
    · intro k
      simpa [C,cols] using hChart j k
  have hSum (x : Fin n → K) : (∑ i, x i • cols i)=U.val.mulVec x := by
    ext k
    simp [cols,Matrix.mulVec,dotProduct,mul_comm]
  have hExists : ∃ x : Fin n → K, ∑ i, x i • C i.castSucc=C (Fin.last n) := by
    refine ⟨U.inv.mulVec rhs,?_⟩
    simp only [C,Fin.lastCases_castSucc,Fin.lastCases_last]
    rw [hSum,Matrix.mulVec_mulVec,U.val_inv,Matrix.one_mulVec]
  obtain ⟨t,rt,ht,hResult,hStable,hRegisters,hIn,hOut⟩ :=
    solve_run F geo.kernel C hSlots
      ports.m ports.dim ports.cb ports.rb ports.am ports.out ports.lb ports.work ports.y
      ports.zero ports.one ports.first ports.second hWorkspace hData hZero hOne
      geo.start geo.columns geo.transpose geo.out geo.labels geo.work geo.y
  rcases hResult with ⟨hOK,hAnswer⟩ | ⟨_,hNone⟩
  · let x : Fin n → K := fun i => val F canonical qN.WS t (YB+i.val)
    have hx : U.val.mulVec x=rhs := by
      rw [←hSum]
      simpa only [C,Fin.lastCases_castSucc,Fin.lastCases_last] using hAnswer
    have he : x=U.inv.mulVec rhs := by
      calc
        x = U.inv.mulVec (U.val.mulVec x) := by
          rw [Matrix.mulVec_mulVec,U.inv_val,Matrix.one_mulVec]
        _ = U.inv.mulVec rhs := congrArg U.inv.mulVec hx
    exact ⟨t,rt,ht,hOK,fun i => congrFun he i,Frame.of_run rt,hStable⟩
  · exact False.elim (hNone hExists)

#print axioms inverseChartColumn_run
end EvenTI.P18Scalar
