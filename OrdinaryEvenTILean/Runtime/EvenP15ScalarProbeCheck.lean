import EvenP15ScalarProbeRows

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 45000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P12Compare EvenTI.P14Recovery
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

local macro "restoreProbeCheckLayout" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.RecoveryLayout.fromFrame))

private def targetLastProbe : Com := .assign coordinateSlot (.var probeIndex)
private def restoreNextCoordinate : Com := .assign coordinateSlot (.add (.var probeIndex) (.lit 1))

def checkScalarProbeFeasibility : Com :=
  .seq targetLastProbe (.seq recoverStoredCoordinate restoreNextCoordinate)

def checkScalarProbeCost (M m n : ℕ) : ℕ :=
  20*((m+n+1)*n)+36+smithRecoverAndCommitCost M (m+n) n

/-- Check that the installed coordinate prefix is consistent, restore the
next slot and preserve all committed prefix words, including for an empty
suffix. -/
theorem checkScalarProbeFeasibility_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) (a : ZMod M)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s)
    (hData : ConstraintBanks A 0 (Function.update 0 i a) (i.val+1) s)
    (hPrefix : CoordinatePrefix (Function.update 0 i a) (i.val+1) s)
    (hIndex : s.vars probeIndex = i.val) :
    let f := Function.update (0 : Fin n → ZMod M) i a
    ∃ t, Run W checkScalarProbeFeasibility s t (checkScalarProbeCost M m n) ∧
      Frame checkScalarProbeFeasibility s t ∧ RecoveryLayout M m n t ∧
      ConstraintBanks A 0 f (i.val+1) t ∧ CoordinatePrefix f (i.val+1) t ∧
      t.vars coordinateSlot = i.val+1 ∧ t.vars crtActive ≤ 1 ∧
      (t.vars crtActive = 1 ↔
        ∃ x, (fixedCoordinateMatrix A (i.val+1)).mulVec x = fixedCoordinateRhs 0 f (i.val+1)) := by
  let f := Function.update (0 : Fin n → ZMod M) i a
  let p := i.val+1
  let C := fixedCoordinateMatrix A p
  let rhs := fixedCoordinateRhs (0 : Fin m → ZMod M) f p
  let u := s.setVar coordinateSlot i.val
  have hi := i.isLt
  have hiW : i.val < W := by omega
  have hpW : p < W := by omega
  have h1 : 1 < W := by omega
  have e0 : (Expr.var probeIndex).evalB W s = some i.val := ev_var hIndex hiW
  have r0 : Run W targetLastProbe s u 2 := Run.assign e0
  have f0 := Frame.of_run r0
  have hu : RecoveryLayout M m n u := restoreProbeCheckLayout hs f0
    (by decide) (by decide) (by decide) (by decide) (by
      rw [f0.arrs matrixR (by decide)]
      exact hs.workCanon)
  have huSlot : u.vars coordinateSlot = i.val := by simp [u]
  have huData : ConstraintBanks A 0 f p u :=
    hData.congr_env (f0.arrs _ (by decide)) (f0.arrs _ (by decide))
  have huPrefix : CoordinatePrefix f p u := by
    intro j hj
    rw [f0.arrs coordinateBank (by decide)]
    exact hPrefix j hj
  obtain ⟨v,r1,f1,hCan,hOutput⟩ :=
    recoverStoredCoordinate_run C rhs i hW hL hu.rows hu.cols huSlot hu.modWord
      hu.sourceLen hu.workLen huData.canonical hu.workCanon huData.coefficient
      huData.probe huData.rhs hu.coLen hu.tgLen hu.modLen (hi.trans_le hu.destLen)
  have hvIndex : v.vars probeIndex = i.val :=
    ((f1.vars _ (by decide)).trans (f0.vars _ (by decide))).trans hIndex
  let t := v.setVar coordinateSlot p
  have e2 : (Expr.add (.var probeIndex) (.lit 1)).evalB W v = some p :=
    ev_add (ev_var hvIndex hiW) (evalB_lit h1) hpW
  have r2 : Run W restoreNextCoordinate v t 4 := Run.assign e2
  have f2 := Frame.of_run r2
  have r : Run W checkScalarProbeFeasibility s t (checkScalarProbeCost M m n) :=
    (r0.seq (r1.seq r2)).mono (by unfold checkScalarProbeCost; omega)
  have ft := Frame.of_run r
  have hWork : Mathproof.P15GSSSmithSweep20261007.Canonical M (t.arrs matrixR) := by
    rw [f2.arrs matrixR (by decide)]
    exact hCan
  have ht : RecoveryLayout M m n t := restoreProbeCheckLayout hs ft
    (by decide) (by decide) (by decide) (by decide) hWork
  have htData : ConstraintBanks A 0 f p t :=
    hData.congr_env (ft.arrs _ (by decide)) (ft.arrs _ (by decide))
  have hSlot : t.vars coordinateSlot = p := by simp [t]
  have hBit : t.vars crtActive = v.vars crtActive := f2.vars _ (by decide)
  have hCoord : t.arrs coordinateBank = v.arrs coordinateBank := f2.arrs _ (by decide)
  have hResult : CoordinatePrefix f p t ∧ t.vars crtActive ≤ 1 ∧
      (t.vars crtActive = 1 ↔ ∃ x, C.mulVec x = rhs) := by
    cases h : recoverCoordinate C rhs i with
    | none =>
      have hFalse : v.vars crtActive=0 ∧ v.arrs coordinateBank=u.arrs coordinateBank := by
        simpa only [h] using hOutput
      refine ⟨?_,by omega,?_⟩
      · intro j hj
        rw [hCoord,hFalse.2]
        exact huPrefix j hj
      · constructor
        · intro hh
          omega
        · rintro ⟨x,hx⟩
          have hSome := recoverCoordinate_complete C rhs i hx
          simp [h] at hSome
    | some z =>
      have hTrue : v.vars crtActive=1 ∧
          v.arrs coordinateBank=(u.arrs coordinateBank).set i.val z.val := by
        simpa only [h] using hOutput
      obtain ⟨x,hx,hiX⟩ := recoverCoordinate_sound C rhs i h
      refine ⟨?_,by omega,⟨fun _ => ⟨x,hx⟩,fun _ => hBit.trans hTrue.1⟩⟩
      intro j hj
      have him : i.val < p := by dsimp [p]; omega
      have hxi : x i = f i := ((fixedCoordinate_solutions A 0 f x p).mp hx).2 i him
      have he : z = f i := hiX.symm.trans hxi
      rw [hCoord,hTrue.2]
      by_cases hij : j = i
      · subst j
        exact (getD_set_self' (hi.trans_le hu.destLen)).trans (congrArg ZMod.val he)
      · have hne : i.val ≠ j.val := fun hh => hij (Fin.ext hh.symm)
        exact (getD_set_ne' hne).trans (huPrefix j hj)
  exact ⟨t,r,ft,ht,htData,hResult.1,hSlot,hResult.2.1,hResult.2.2⟩

#print axioms checkScalarProbeFeasibility_run
end EvenTI.P15Scalar