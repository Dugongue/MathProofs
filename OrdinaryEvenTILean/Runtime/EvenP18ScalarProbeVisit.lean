import EvenP15ScalarProbeDriver


set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 25000

namespace EvenTI.P18Scalar

open EvenTI.P15Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)

private def usableProbe : Cond := .eq (.var crtActive) (.lit 1)

def runScalarProbeWith (consume : Com) (answer : String) : Com :=
  .seq runScalarKernelProbe (.ite usableProbe consume (.assign answer (.lit 1)))

/-- Feed the recovered modular assignment to the live consumer. Infeasible
probes contribute the identity. Each successful probe carries a feasible
prefix and exposes exactly the consumer's bit about that assignment. -/
theorem runScalarProbeWith_run {M W m n C : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (i : Fin n) (a : ZMod M) (consume : Com) (answer : String)
    (test : (Fin n → ZMod M) → Bool) (hId : test 0 = true)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hSrc : IncidenceInput s src)
    (hCanonical : Canonical M (s.arrs constraintMatrix))
    (hCap : (s.arrs constraintMatrix).length < W) (hRhs : (s.arrs crtRhsBank).length = m+n)
    (hIndex : s.vars probeIndex = i.val) (hValue : s.vars probeValue = a.val)
    (hUse : ∀ (u : Env) (x : Fin n → ZMod M),
      Run W runScalarKernelProbe s u (runScalarKernelProbeCost M m n) →
      Frame runScalarKernelProbe s u →
      RecoveryLayout M m n u → Canonical M (u.arrs constraintMatrix) →
      u.vars crtActive = 1 →
      (∀ j, (u.arrs coordinateBank).getD j.val 0 = (x j).val) →
      ∃ v, Run W consume u v C ∧ v.vars answer ≤ 1 ∧
        (v.vars answer = 1 ↔ test x = true)) :
    let A := incidenceMatrix M src
    let B := fixedCoordinateMatrix A (i.val+1)
    let b := fixedCoordinateRhs (0 : Fin m → ZMod M) (Function.update 0 i a) (i.val+1)
    ∃ t selection, Run W (runScalarProbeWith consume answer) s t
      (runScalarKernelProbeCost M m n+C+6) ∧
      Frame (runScalarProbeWith consume answer) s t ∧
      t.vars answer ≤ 1 ∧ (t.vars answer = 1 ↔ test (selection.getD 0) = true) ∧
      (selection.isSome = true ↔ ∃ x, B.mulVec x = b) ∧
      (∀ x, selection = some x → B.mulVec x = b) := by
  obtain ⟨u,r0,f0,hu,hCan,hActive,hExact,hPayload⟩ := runScalarKernelProbe_run
    src i a hW hRows hL hs hSrc hCanonical hCap hRhs hIndex hValue
  have h1 : 1 < W := by omega
  by_cases h : u.vars crtActive = 1
  · obtain ⟨x,hSol,hWords⟩ := hPayload h
    obtain ⟨v,r1,hBit,hVerdict⟩ := hUse u x r0 f0 hu hCan h hWords
    have hEval : usableProbe.evalB W u = some true :=
      evalB_condEq (ev_var h h1) (evalB_lit h1)
    have rr : Run W (runScalarProbeWith consume answer) s v
        (runScalarKernelProbeCost M m n+C+6) :=
      (r0.seq (Run.ite_true (d:=.assign answer (.lit 1)) hEval r1)).mono (by
        simp [usableProbe,Cond.size,Expr.size] <;> omega)
    refine ⟨v,some x,rr,Frame.of_run rr,hBit,hVerdict,⟨fun _ => ⟨x,hSol⟩,fun _ => rfl⟩,?_⟩
    intro y hy
    exact (Option.some.inj hy) ▸ hSol
  · have hZ : u.vars crtActive = 0 := by omega
    have hEval : usableProbe.evalB W u = some false :=
      evalB_condEq (ev_var hZ (by omega)) (evalB_lit (n:=1) h1)
    let v := u.setVar answer 1
    have r1 : Run W (.assign answer (.lit 1)) u v 2 := Run.assign (evalB_lit h1)
    have rr : Run W (runScalarProbeWith consume answer) s v
        (runScalarKernelProbeCost M m n+C+6) :=
      (r0.seq (Run.ite_false (c:=consume) hEval r1)).mono (by
        simp [usableProbe,Cond.size,Expr.size] <;> omega)
    refine ⟨v,none,rr,Frame.of_run rr,by simp [v],by simp [v,hId],?_,?_⟩
    · constructor
      · simp
      · intro hSolution
        exact False.elim (h (hExact.mpr hSolution))
    · intro x hx
      cases hx

#print axioms runScalarProbeWith_run
end EvenTI.P18Scalar