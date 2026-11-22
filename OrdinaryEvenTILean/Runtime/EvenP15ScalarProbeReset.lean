import EvenP15RecoverIncidenceBuild

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 28000

namespace EvenTI.P15Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairLargeBank20261004 (zeroBlock zeroBlock_run Clean)
open Mathproof.Problem18PairLargeWords20261004 (wcSrc wcDst wcCnt)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover

private def probeRhsLength : Expr := .add (.var baseRows) (.var inputColsR)
private def clearProbeRhs : Com := zeroBlock crtRhsBank (.lit 0) probeRhsLength
private def retargetInitialCoordinate : Com := .assign coordinateSlot (.lit 0)

def resetScalarProbeBank : Com :=
  .seq clearProbeRhs (.seq buildIncidenceMatrix retargetInitialCoordinate)

def resetScalarProbeCost (m n : ℕ) : ℕ :=
  20*(m+n)+18+buildIncidenceCost m n

/-- Reset and construct the homogeneous modular system for one scalar
probe from the immutable signed-incidence words. Prior probes may have
written arbitrary canonical values in the coefficient and RHS banks. -/
theorem resetScalarProbeBank_run {M W m n : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n)
    (hW : 2*M+4 < W) (hThree : 3*m < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hLayout : RecoveryLayout M m n s) (hData : IncidenceInput s src)
    (hCan : Canonical M (s.arrs constraintMatrix)) (hCap : (s.arrs constraintMatrix).length < W)
    (hRhs : (s.arrs crtRhsBank).length = m+n) :
    ∃ t, Run W resetScalarProbeBank s t (resetScalarProbeCost m n) ∧
      Frame resetScalarProbeBank s t ∧ RecoveryLayout M m n t ∧
      ConstraintBanks (incidenceMatrix M src) 0 0 0 t ∧ t.vars coordinateSlot = 0 := by
  have hm : m < W := by omega
  have hn : n < W := by omega
  have hmn : m+n < W := by omega
  have h1 : 1 < W := by omega
  have hz : 0 < W := by omega
  have e : probeRhsLength.evalB W s = some (m+n) :=
    ev_add (ev_var hLayout.base hm) (ev_var hLayout.cols hn) hmn
  obtain ⟨u,r₀,_,_,hLen,hZeros,_,_⟩ :=
    zeroBlock_run crtRhsBank s (d:=.lit 0) (n:=probeRhsLength)
      (by simp [Clean,probeRhsLength,NoVar,wcSrc,wcDst,wcCnt,baseRows,inputColsR] : Clean probeRhsLength)
      (evalB_lit hz) e (by simp [hRhs]) (by rwa [hRhs]) h1
  have rr₀ : Run W clearProbeRhs s u (20*(m+n)+16) := r₀
  have f₀ := Frame.of_run rr₀
  have hRhs' : u.arrs crtRhsBank =
      List.ofFn (fun r => (fixedCoordinateRhs (n:=n) (0 : Fin m → ZMod M) 0 0 r).val) := by
    have hlen : (u.arrs crtRhsBank).length = m+n := hLen.trans hRhs
    apply List.ext_getElem (by rw [hlen,List.length_ofFn])
    intro k hk _
    have hk' : k < m+n := by rwa [hlen] at hk
    have hget : (u.arrs crtRhsBank).getD k 0 = 0 := by
      simpa [hk'] using hZeros k
    rw [List.getD_eq_getElem _ _ hk] at hget
    rw [hget,List.getElem_ofFn]
    simp [fixedCoordinateRhs]
  obtain ⟨v,r₁,hCoeffsCan,hCoeffs,hPad,f₁⟩ := buildIncidenceMatrix_run src hW hThree hn
    (by omega) (by omega) (hData.congr_env (f₀.arrs _ (by decide)))
    (by rw [f₀.arrs constraintMatrix (by decide)]; exact hCan)
    (by rw [f₀.len _]; exact hLayout.sourceLen) (by rw [f₀.len _]; exact hCap)
    ((f₀.vars _ (by decide)).trans hLayout.rows) ((f₀.vars _ (by decide)).trans hLayout.base)
    ((f₀.vars _ (by decide)).trans hLayout.cols) ((f₀.vars _ (by decide)).trans hLayout.modWord)
  let t := v.setVar coordinateSlot 0
  have r₂ : Run W retargetInitialCoordinate v t 2 := Run.assign (evalB_lit hz)
  have f₂ := Frame.of_run r₂
  have r : Run W resetScalarProbeBank s t (resetScalarProbeCost m n) :=
    (rr₀.seq (r₁.seq r₂)).mono (by unfold resetScalarProbeCost; omega)
  have ft := Frame.of_run r
  have hwork : Canonical M (t.arrs matrixR) := by
    rw [ft.arrs matrixR (by decide)]
    exact hLayout.workCanon
  have hLayout' : RecoveryLayout M m n t := by
    refine ⟨(ft.vars _ (by decide)).trans hLayout.rows,(ft.vars _ (by decide)).trans hLayout.cols,
      (ft.vars _ (by decide)).trans hLayout.modWord,(ft.vars _ (by decide)).trans hLayout.base,
      by rw [ft.len _]; exact hLayout.sourceLen,by rw [ft.len _]; exact hLayout.workLen,hwork,
      (ft.len _).trans hLayout.coLen,(ft.len _).trans hLayout.tgLen,
      (ft.len _).trans hLayout.modLen,by rw [ft.len _]; exact hLayout.destLen⟩
  have hBanks : ConstraintBanks (incidenceMatrix M src) 0 0 0 v := by
    refine ⟨hCoeffsCan,?_,?_,(f₁.arrs _ (by decide)).trans hRhs'⟩
    · intro r j
      by_cases hr : r.val < m
      · rw [fixedCoordinateMatrix,dif_pos hr]
        exact hCoeffs ⟨r.val,hr⟩ j
      · simp only [fixedCoordinateMatrix,dif_neg hr,Nat.not_lt_zero,if_false]
        have hb := Nat.mul_le_mul_right n (Nat.le_of_not_gt hr)
        have hm' : m*n ≤ r.val*n+j.val := by omega
        have hi : r.val*n+j.val < (m+n+1)*n :=
          (packed_lt r j).trans_le (Nat.mul_le_mul_right n (by omega))
        unfold decode
        rw [hPad _ hm' hi,Nat.cast_zero]
    · intro j
      have hLe : m ≤ m+n := by omega
      have hAddr : m*n ≤ (m+n)*n+j.val := (Nat.mul_le_mul_right n hLe).trans (Nat.le_add_right _ _)
      exact hPad _ hAddr (packed_lt (Fin.last (m+n)) j)
  exact ⟨t,r,ft,hLayout',hBanks.congr_env (f₂.arrs _ (by decide)) (f₂.arrs _ (by decide)),by simp [t]⟩

#print axioms resetScalarProbeBank_run
end EvenTI.P15Scalar