import EvenP15ScalarProbeRows

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 25000

namespace EvenTI.P17Scalar

open EvenTI.P15Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)

def scalarProbeCursor : String := "even.scalar.probe.cursor"
def scalarProbeLimit : String := "even.scalar.probe.limit"

def populateScalarProbe : Com :=
  .seq (.assign probeIndex (.div (.var scalarProbeCursor) (.var modR)))
    (.assign probeValue (.sub (.var scalarProbeCursor) (.mul (.var probeIndex) (.var modR))))

def scalarProbeAdvance : Com :=
  .assign scalarProbeCursor (.add (.var scalarProbeCursor) (.lit 1))

def scalarProbeLoopBody (visit : Com) : Com :=
  .seq populateScalarProbe (.seq visit scalarProbeAdvance)

def scalarProbeLoopGuard : Cond := .lt (.var scalarProbeCursor) (.var scalarProbeLimit)

def scalarProbeLoop (visit : Com) : Com :=
  .seq (.assign scalarProbeCursor (.lit 0)) (.while scalarProbeLoopGuard (scalarProbeLoopBody visit))

def probeCursorInput (s : Env) (M k : ℕ) : Env :=
  (s.setVar probeIndex (k/M)).setVar probeValue (k%M)

theorem populateScalarProbe_run {M k W : ℕ} {s : Env}
    (hc : s.vars scalarProbeCursor=k) (hM : s.vars modR=M)
    (hk : k < W) (hMW : M < W) :
    Run W populateScalarProbe s (probeCursorInput s M k) 10 := by
  have ex : (Expr.var scalarProbeCursor).evalB W s = some k := ev_var hc hk
  have em : (Expr.var modR).evalB W s = some M := ev_var hM hMW
  have hQuot : k/M < W := (Nat.div_le_self _ _).trans_lt hk
  have hProd : k/M*M < W := (Nat.div_mul_le_self _ _).trans_lt hk
  have eq : (Expr.div (.var scalarProbeCursor) (.var modR)).evalB W s = some (k/M) :=
    evalB_bin (op:=.div) ex em hQuot
  let u := s.setVar probeIndex (k/M)
  have r0 : Run W (.assign probeIndex (.div (.var scalarProbeCursor) (.var modR))) s u 4 :=
    Run.assign eq
  have xu : (Expr.var scalarProbeCursor).evalB W u = some k :=
    ev_var (by simp [u,show scalarProbeCursor ≠ probeIndex by decide,hc]) hk
  have mu : (Expr.var modR).evalB W u = some M :=
    ev_var (by simp [u,show modR ≠ probeIndex by decide,hM]) hMW
  have qu : (Expr.var probeIndex).evalB W u = some (k/M) :=
    ev_var (by simp [u]) hQuot
  have eu : (Expr.sub (.var scalarProbeCursor) (.mul (.var probeIndex) (.var modR))).evalB W u =
      some (k%M) := by
    rw [Nat.mod_def, Nat.mul_comm M (k/M)]
    exact evalB_bin (op:=.sub) xu (evalB_bin (op:=.mul) qu mu hProd)
      ((Nat.sub_le _ _).trans_lt hk)
  exact r0.seq (Run.assign eu)

/-- Execute one visit for every pair of a coordinate and a base residue,
in the fixed row-major order. The caller's invariant can retain the
symbolic probe result while this loop performs the real address arithmetic. -/
theorem scalarProbeLoop_run {M n W C : ℕ} {s : Env}
    (visit : Com) (I : ℕ → Env → Prop)
    (hSize : n*M < W) (hMW : M < W) (hOne : 1 < W)
    (hLimit : s.vars scalarProbeLimit=n*M) (hM : s.vars modR=M)
    (hInit : I 0 (s.setVar scalarProbeCursor 0))
    (hVisit : ∀ k < n*M, ∀ u, I k u → u.vars scalarProbeCursor=k →
      u.vars scalarProbeLimit=n*M → u.vars modR=M →
      ∃ v, Run W visit (probeCursorInput u M k) v C ∧
        v.vars scalarProbeCursor=k ∧ v.vars scalarProbeLimit=n*M ∧ v.vars modR=M ∧
        I (k+1) (v.setVar scalarProbeCursor (k+1))) :
    ∃ t, Run W (scalarProbeLoop visit) s t ((C+18)*(n*M)+6) ∧
      I (n*M) t ∧ t.vars scalarProbeCursor=n*M ∧
      t.vars scalarProbeLimit=n*M ∧ t.vars modR=M := by
  let N := n*M
  let P (u : Env) := u.vars scalarProbeCursor ≤ N ∧ u.vars scalarProbeLimit=N ∧
    u.vars modR=M ∧ I (u.vars scalarProbeCursor) u
  let potential (u : Env) := N-u.vars scalarProbeCursor
  let u₀ := s.setVar scalarProbeCursor 0
  have r0 : Run W (.assign scalarProbeCursor (.lit 0)) s u₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hxL : scalarProbeLimit ≠ scalarProbeCursor := by decide
  have hxM : modR ≠ scalarProbeCursor := by decide
  have p0 : P u₀ := by
    exact ⟨by simp [u₀],by simpa [u₀,hxL] using hLimit,by simpa [u₀,hxM] using hM,
      by simpa [u₀] using hInit⟩
  have grd (u : Env) (h : P u) : scalarProbeLoopGuard.evalB W u =
      some (decide (u.vars scalarProbeCursor < N)) :=
    evalB_condLt (evalB_var (h.1.trans_lt hSize)) (ev_var h.2.1 hSize)
  have step (u : Env) (h : P u) (he : scalarProbeLoopGuard.evalB W u = some true) :
      ∃ v, Run W (scalarProbeLoopBody visit) u v (C+14) ∧ P v ∧ potential v < potential u := by
    rw [grd u h] at he
    have hk : u.vars scalarProbeCursor < N := by simpa using he
    let k := u.vars scalarProbeCursor
    have ra := populateScalarProbe_run (k:=k) (M:=M) (W:=W) rfl h.2.2.1 (hk.trans hSize) hMW
    obtain ⟨v,rv,hV,hN,hM',hNext⟩ := hVisit k hk u h.2.2.2 rfl h.2.1 h.2.2.1
    let w := v.setVar scalarProbeCursor (k+1)
    have hK : k+1 < W := (Nat.succ_le_of_lt hk).trans_lt hSize
    have rb : Run W scalarProbeAdvance v w 4 :=
      Run.assign (ev_add (ev_var hV (hk.trans hSize)) (evalB_lit hOne) hK)
    have hRun : Run W (scalarProbeLoopBody visit) u w (C+14) :=
      (ra.seq (rv.seq rb)).mono (by omega)
    refine ⟨w,hRun,⟨by simp [w]; omega,by simpa [w,hxL] using hN,
      by simpa [w,hxM] using hM',by simpa [w] using hNext⟩,?_⟩
    simp only [potential,w,vars_setVar,if_true]
    change N-(k+1) < N-k
    omega
  obtain ⟨t,r,ht,hS⟩ := Run.while_count P potential (C+14) (fun u h => ⟨_,grd u h⟩) step p0
  rw [grd t ht] at hS
  have hDone : t.vars scalarProbeCursor=N :=
    le_antisymm ht.1 (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hS)))
  have hr : Run W (scalarProbeLoop visit) s t ((C+18)*N+6) :=
    (r0.seq r).mono (by simp [potential,u₀,scalarProbeLoopGuard,Cond.size,Expr.size,
      show 4+(C+14)=C+18 by omega] <;> omega)
  exact ⟨t,hr,by simpa only [hDone] using ht.2.2.2,hDone,ht.2.1,ht.2.2.1⟩

#print axioms populateScalarProbe_run
#print axioms scalarProbeLoop_run
end EvenTI.P17Scalar