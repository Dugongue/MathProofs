import EvenP15ScalarKernelProbe
import EvenP14CRTComplete

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery Matrix

/-- Invoke the checked CRT driver directly on one installed homogeneous
prefix probe. Its actual coordinate bank carries the exact probe selected
by the generator theorem; a failed query is tracked separately. -/
theorem recoveryKernelProbe_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) (a : ZMod M)
    (hW : 4*M*M+4*M+10 < W)
    (hSize : (m+n+n+1)+n+(m+n+n+1)*n+(m+n+n+1)*(m+n+n+1)+4 < W)
    (hLayout : RecoveryLayout M (m+n) n s)
    (hData : ConstraintBanks (fixedCoordinateMatrix A (i.val+1))
      (fixedCoordinateRhs 0 (Function.update 0 i a) (i.val+1)) 0 0 s) :
    ∃ t, Run W completeCoordinateRecovery s t (completeCoordinateRecoveryCost M (m+n) n) ∧
      Frame completeCoordinateRecovery s t ∧
      (t.vars crtActive = 1 →
        ∀ j, (t.arrs coordinateBank).getD j.val 0 = (recoveryKernelProbe A i a j).val) ∧
      (t.vars crtActive ≠ 1 → recoveryKernelProbe A i a = 0) ∧
      t.vars crtActive ≤ 1 := by
  let C := fixedCoordinateMatrix A (i.val+1)
  let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M) (Function.update 0 i a) (i.val+1)
  have hScratch : n=0 → m+n ≤ (s.arrs EvenTI.P12ComparePrep.coefficientBank).length := by
    intro hz
    subst n
    exact Fin.elim0 i
  obtain ⟨t,hr,hFrame,hResult⟩ :=
    completeCoordinateRecovery_run C rhs hW hSize hLayout hData hScratch
  refine ⟨t,hr,hFrame,?_,?_,?_⟩
  all_goals
    cases h : recoverLinear C rhs with
    | none =>
      have hz : t.vars crtActive = 0 := by simpa only [h] using hResult
      simp [hz,recoveryKernelProbe,show recoverLinear (fixedCoordinateMatrix A (i.val+1))
        (fixedCoordinateRhs 0 (Function.update 0 i a) (i.val+1)) = none from h]
    | some v =>
      have hp : t.vars crtActive = 1 ∧ ∀ j, (t.arrs coordinateBank).getD j.val 0 = (v j).val := by
        simpa only [h] using hResult
      simp [hp.1,recoveryKernelProbe,show recoverLinear (fixedCoordinateMatrix A (i.val+1))
        (fixedCoordinateRhs 0 (Function.update 0 i a) (i.val+1)) = some v from h] <;> exact hp.2

#print axioms recoveryKernelProbe_run
end EvenTI.P15Scalar