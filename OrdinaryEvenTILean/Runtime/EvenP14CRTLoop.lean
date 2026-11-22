import EvenP14CRTLoopStore
import EvenP14CRTCoordinate
import EvenP14CRTReference

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)
open EvenTI.P12Compare

set_option maxHeartbeats 9000000
set_option maxRecDepth 50000

structure RecoveryLayout (M m n : ℕ) (s : Env) : Prop where
  rows : s.vars rowsR = m+n+1
  cols : s.vars inputColsR = n
  modWord : s.vars modR = M
  base : s.vars baseRows = m
  sourceLen : (m+n+1)*n ≤ (s.arrs constraintMatrix).length
  workLen : (m+n+1)*n+(m+n+1)*(m+n+1)+n ≤ (s.arrs matrixR).length
  workCanon : Canonical M (s.arrs matrixR)
  coLen : (s.arrs coefficientBank).length = m+n+1
  tgLen : (s.arrs targetBank).length = m+n+1
  modLen : (s.arrs modulusBank).length = m+n+1
  destLen : n ≤ (s.arrs coordinateBank).length

private theorem RecoveryLayout.fromFrame {M m n : ℕ} {s t : Env} {c : Com}
    (h : RecoveryLayout M m n s) (f : Frame c s t)
    (hr : rowsR ∉ scalarWrites c) (hc : inputColsR ∉ scalarWrites c)
    (hm : modR ∉ scalarWrites c) (hb : baseRows ∉ scalarWrites c)
    (hCan : Canonical M (t.arrs matrixR)) :
    RecoveryLayout M m n t :=
  ⟨(f.vars _ hr).trans h.rows,(f.vars _ hc).trans h.cols,(f.vars _ hm).trans h.modWord,
    (f.vars _ hb).trans h.base,by rw [f.len _]; exact h.sourceLen,
    by rw [f.len _]; exact h.workLen,hCan,(f.len _).trans h.coLen,
    (f.len _).trans h.tgLen,(f.len _).trans h.modLen,by rw [f.len _]; exact h.destLen⟩

private def loadCommitted : Com :=
  .assign crtRepresentative (.get coordinateBank (.var coordinateSlot))
private def commitReady : Com := .seq loadCommitted installConstraint
private def activeTest : Cond := .eq (.var crtActive) (.lit 1)
private def recoverAndAdvance : Com :=
  .seq recoverStoredCoordinate (.ite activeTest commitReady .skip)
private def advanceSlot : Com :=
  .assign coordinateSlot (.add (.var coordinateSlot) (.lit 1))
private def recoverOuterStep : Com :=
  .seq (.ite activeTest recoverAndAdvance .skip) advanceSlot
private def recoverOuterGuard : Cond := .lt (.var coordinateSlot) (.var inputColsR)
private def initializeOuter : Com :=
  .seq (.assign coordinateSlot (.lit 0)) (.assign crtActive (.lit 1))
def recoverAllCoordinates : Com := .seq initializeOuter (.while recoverOuterGuard recoverOuterStep)

def recoverRoundCost (M m n : ℕ) : ℕ :=
  20*((m+n+1)*n)+30+smithRecoverAndCommitCost M (m+n) n

def recoverAllCoordinatesCost (M m n : ℕ) : ℕ :=
  (recoverRoundCost M m n+54)*n+10

private def Progress {M m n : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (result : Option (Fin n → ZMod M)) (p : ℕ) (s : Env) : Prop :=
  (s.vars crtActive = 1 ∧ ∃ w,
    ConstraintBanks A b w p s ∧ CoordinatePrefix w p s ∧
    fixPaddedCoordinates A b ((List.finRange n).drop p) w p = result) ∨
  (s.vars crtActive = 0 ∧ result = none)

private theorem Progress.congr_env {M m n : ℕ} [NeZero M]
    {A : Matrix (Fin m) (Fin n) (ZMod M)} {b : Fin m → ZMod M}
    {result : Option (Fin n → ZMod M)} {p : ℕ} {s t : Env}
    (h : Progress A b result p s)
    (ha : t.vars crtActive = s.vars crtActive)
    (hA : t.arrs constraintMatrix = s.arrs constraintMatrix)
    (hb : t.arrs crtRhsBank = s.arrs crtRhsBank)
    (hw : t.arrs coordinateBank = s.arrs coordinateBank) : Progress A b result p t := by
  rcases h with ⟨hv,w,hB,hP,hR⟩ | ⟨hv,hR⟩
  · exact Or.inl ⟨ha.trans hv,w,hB.congr_env hA hb,by rw [CoordinatePrefix,hw]; exact hP,hR⟩
  · exact Or.inr ⟨ha.trans hv,hR⟩

private theorem commitReady_run {M m n W : ℕ} [NeZero M] {s u : Env}
    {A : Matrix (Fin m) (Fin n) (ZMod M)} {b : Fin m → ZMod M} {w : Fin n → ZMod M}
    (i : Fin n) (v : ZMod M)
    (hs : RecoveryLayout M m n s) (hu : RecoveryLayout M m n u)
    (hData : ConstraintBanks A b w i.val u)
    (hSlot : u.vars coordinateSlot = i.val)
    (hNew : u.arrs coordinateBank = (s.arrs coordinateBank).set i.val v.val)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W) :
    ∃ t, Run W commitReady u t 29 ∧
      ConstraintBanks A b (Function.update w i v) (i.val+1) t ∧
      RecoveryLayout M m n t ∧ Frame commitReady u t := by
  have hiW : i.val < W := i.isLt.trans (by omega)
  have hi : i.val < (s.arrs coordinateBank).length := i.isLt.trans_le hs.destLen
  have hx : (u.arrs coordinateBank)[i.val]? = some v.val := by
    rw [hNew,List.getElem?_set_self hi]
  let y := u.setVar crtRepresentative v.val
  have hValW : v.val < W := (ZMod.val_lt _).trans (by omega)
  have r0 : Run W loadCommitted u y 3 :=
    Run.assign (evalB_get (ev_var hSlot hiW) hx hValW)
  have f0 := Frame.of_run r0
  have hDataY := hData.congr_env (f0.arrs _ (by decide)) (f0.arrs _ (by decide))
  have hCanY : Canonical M (y.arrs matrixR) := by rw [f0.arrs matrixR (by decide)]; exact hu.workCanon
  have hY : RecoveryLayout M m n y :=
    hu.fromFrame f0 (by decide) (by decide) (by decide) (by decide) hCanY
  let row : Fin (m+n) := ⟨m+i.val,Nat.add_lt_add_left i.isLt m⟩
  have hEntry : (m+i.val)*n+i.val < (m+n)*n := packed_lt row i
  have hBefore : (m+n)*n ≤ (m+n+1)*n := Nat.mul_le_mul_right n (by omega)
  have hRow : m+i.val < (y.arrs crtRhsBank).length := by
    rw [hDataY.rhs,List.length_ofFn]
    exact row.isLt
  have hEntryW := (hEntry.trans_le hBefore).trans (show (m+n+1)*n < W by omega)
  obtain ⟨t,r1,hA,hb,f1⟩ := installConstraint_run (s:=y) (B:=W) (M:=M) (m:=m) (n:=n)
    (i:=i.val) (r:=v.val) (by omega) (by omega) hValW (by have := row.isLt; omega)
    hiW (by omega) (by omega) hEntryW
    hY.base hY.cols ((f0.vars _ (by decide)).trans hSlot) hY.modWord (by simp [y])
    hRow ((hEntry.trans_le hBefore).trans_le hY.sourceLen)
  have hTcan : Canonical M (t.arrs matrixR) := by rw [f1.arrs matrixR (by decide)]; exact hY.workCanon
  exact ⟨t,r0.seq r1,hDataY.advance i v hY.sourceLen hA hb,
    hY.fromFrame f1 (by decide) (by decide) (by decide) (by decide) hTcan,Frame.of_run (r0.seq r1)⟩

private theorem dropFinRange (i : Fin n) :
    (List.finRange n).drop i.val = i :: (List.finRange n).drop (i.val+1) := by
  rw [List.drop_eq_getElem_cons (by simpa using i.isLt),List.getElem_finRange]
  congr 1 <;> apply Fin.ext <;> rfl

private theorem recoverAndAdvance_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    (w : Fin n → ZMod M) (result : Option (Fin n → ZMod M))
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hSlot : s.vars coordinateSlot = i.val)
    (hData : ConstraintBanks A b w i.val s) (hPrefix : CoordinatePrefix w i.val s)
    (hRef : fixPaddedCoordinates A b ((List.finRange n).drop i.val) w i.val = result) :
    ∃ t, Run W recoverAndAdvance s t (recoverRoundCost M m n+34) ∧
      RecoveryLayout M m n t ∧ Progress A b result (i.val+1) t := by
  let A' := fixedCoordinateMatrix A i.val
  let b' := fixedCoordinateRhs b w i.val
  have hi : i.val < (s.arrs coordinateBank).length := i.isLt.trans_le hs.destLen
  obtain ⟨u,r0,f0,hCan,he⟩ := recoverStoredCoordinate_run A' b' i hW hL hs.rows hs.cols hSlot
    hs.modWord hs.sourceLen hs.workLen hData.canonical hs.workCanon hData.coefficient
    hData.probe hData.rhs hs.coLen hs.tgLen hs.modLen hi
  have rr0 : Run W recoverStoredCoordinate s u (recoverRoundCost M m n) := r0
  have hu := hs.fromFrame f0 (by decide) (by decide) (by decide) (by decide) hCan
  have hAt : u.vars coordinateSlot = i.val := (f0.vars _ (by decide)).trans hSlot
  rw [dropFinRange i] at hRef
  cases ha : recoverCoordinate A' b' i with
  | none =>
    have hs' : u.vars crtActive = 0 ∧ u.arrs coordinateBank = s.arrs coordinateBank := by
      simpa only [ha] using he
    have hFalse : activeTest.evalB W u = some false :=
      evalB_condEq (ev_var hs'.1 (by omega)) (evalB_lit (n:=1) (by omega))
    have hNone : result = none := by
      symm
      simpa [fixPaddedCoordinates,show recoverCoordinate (fixedCoordinateMatrix A i.val)
        (fixedCoordinateRhs b w i.val) i = none from ha] using hRef
    exact ⟨u,(rr0.seq (Run.ite_false (c:=commitReady) hFalse Run.skip)).mono
      (by simp [activeTest,Cond.size,Expr.size] <;> omega),hu,Or.inr ⟨hs'.1,hNone⟩⟩
  | some v =>
    have hSome : u.vars crtActive = 1 ∧
        u.arrs coordinateBank = (s.arrs coordinateBank).set i.val v.val := by simpa only [ha] using he
    have hDataU := hData.congr_env (f0.arrs _ (by decide)) (f0.arrs _ (by decide))
    obtain ⟨t,r1,hDataT,ht,f1⟩ := commitReady_run i v hs hu hDataU hAt hSome.2 hW hL
    have hActive : t.vars crtActive = 1 := (f1.vars _ (by decide)).trans hSome.1
    have hTrue : activeTest.evalB W u = some true :=
      evalB_condEq (ev_var hSome.1 (by omega)) (evalB_lit (n:=1) (by omega))
    have hStore : t.arrs coordinateBank = (s.arrs coordinateBank).set i.val v.val :=
      (f1.arrs _ (by decide)).trans hSome.2
    have hRest : fixPaddedCoordinates A b ((List.finRange n).drop (i.val+1))
        (Function.update w i v) (i.val+1) = result := by
      simpa [fixPaddedCoordinates,show recoverCoordinate (fixedCoordinateMatrix A i.val)
        (fixedCoordinateRhs b w i.val) i = some v from ha] using hRef
    exact ⟨t,(rr0.seq (Run.ite_true (d:=.skip) hTrue r1)).mono
      (by simp [activeTest,Cond.size,Expr.size] <;> omega),ht,
      Or.inl ⟨hActive,Function.update w i v,hDataT,hPrefix.advance i v hi hStore,hRest⟩⟩

private theorem recoverOuterStep_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    (out : Option (Fin n → ZMod M))
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hSlot : s.vars coordinateSlot = i.val)
    (hState : Progress A b out i.val s) :
    ∃ t, Run W recoverOuterStep s t (recoverRoundCost M m n+50) ∧
      RecoveryLayout M m n t ∧ t.vars coordinateSlot = i.val+1 ∧ Progress A b out (i.val+1) t := by
  have hOne : 1 < W := by omega
  let cmd := Com.ite activeTest recoverAndAdvance .skip
  have hex : ∃ u, Run W cmd s u (recoverRoundCost M m n+40) ∧
      RecoveryLayout M m n u ∧ Progress A b out (i.val+1) u := by
    rcases hState with ⟨ha,w,hData,hP,hR⟩ | ⟨ha,hR⟩
    · obtain ⟨u,hRun,hu,hP⟩ := recoverAndAdvance_run A b i w out hW hL hs hSlot hData hP hR
      have ht : activeTest.evalB W s = some true := evalB_condEq (ev_var ha hOne) (evalB_lit hOne)
      exact ⟨u,(Run.ite_true (d:=.skip) ht hRun).mono
        (by simp [activeTest,Cond.size,Expr.size] <;> omega),hu,hP⟩
    · have ht : activeTest.evalB W s = some false :=
        evalB_condEq (ev_var ha (by omega)) (evalB_lit (n:=1) hOne)
      exact ⟨s,(Run.ite_false (c:=recoverAndAdvance) ht Run.skip).mono
        (by simp [activeTest,Cond.size,Expr.size] <;> omega),hs,Or.inr ⟨ha,hR⟩⟩
  obtain ⟨u,r0,hu,hP⟩ := hex
  have f0 := Frame.of_run r0
  have hiU : u.vars coordinateSlot = i.val := (f0.vars _ (by decide)).trans hSlot
  have hiW : i.val < W := i.isLt.trans (by omega)
  have hjW : i.val+1 < W := (Nat.succ_le_of_lt i.isLt).trans_lt (by omega)
  let t := u.setVar coordinateSlot (i.val+1)
  have r1 : Run W advanceSlot u t 4 := Run.assign (ev_add (ev_var hiU hiW) (evalB_lit hOne) hjW)
  have f1 := Frame.of_run r1
  have hCan : Canonical M (t.arrs matrixR) := by rw [f1.arrs matrixR (by decide)]; exact hu.workCanon
  exact ⟨t,(r0.seq r1).mono (by omega),
    hu.fromFrame f1 (by decide) (by decide) (by decide) (by decide) hCan,by simp [t],
    hP.congr_env (f1.vars _ (by decide)) (f1.arrs _ (by decide)) (f1.arrs _ (by decide))
      (f1.arrs _ (by decide))⟩

/-- Execute every coordinate of one resident fixed-height constraint system.
The bank contents agree with the exact padded reference recovery. -/
theorem recoverAllCoordinates_run {M m n W : ℕ} [NeZero M] {s : Env}
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (hW : 4*M*M+4*M+10 < W)
    (hL : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hs : RecoveryLayout M m n s) (hInit : ConstraintBanks A b 0 0 s) :
    ∃ t, Run W recoverAllCoordinates s t (recoverAllCoordinatesCost M m n) ∧
      RecoveryLayout M m n t ∧ t.vars coordinateSlot = n ∧
      Frame recoverAllCoordinates s t ∧
      (match fixPaddedCoordinates A b (List.finRange n) 0 0 with
       | some w => t.vars crtActive = 1 ∧ ∀ i : Fin n, (t.arrs coordinateBank).getD i.val 0 = (w i).val
       | none => t.vars crtActive = 0) := by
  let result := fixPaddedCoordinates A b (List.finRange n) 0 0
  let u := (s.setVar coordinateSlot 0).setVar crtActive 1
  have hz : 0 < W := by omega
  have ho : 1 < W := by omega
  have r0 : Run W initializeOuter s u 4 := (Run.assign (evalB_lit hz)).seq (Run.assign (evalB_lit ho))
  have f0 := Frame.of_run r0
  have hCan : Canonical M (u.arrs matrixR) := by rw [f0.arrs matrixR (by decide)]; exact hs.workCanon
  have hSlot : u.vars coordinateSlot = 0 := by
    simp [u,vars_setVar,show coordinateSlot ≠ crtActive by decide]
  let I (t : Env) := RecoveryLayout M m n t ∧ t.vars coordinateSlot ≤ n ∧
    Progress A b result (t.vars coordinateSlot) t
  let V (t : Env) := n-t.vars coordinateSlot
  have hI : I u :=
    ⟨hs.fromFrame f0 (by decide) (by decide) (by decide) (by decide) hCan,by simp [hSlot],by
      rw [hSlot]
      exact Or.inl ⟨by simp [u],0,hInit.congr_env (f0.arrs _ (by decide)) (f0.arrs _ (by decide)),
        fun j hj => False.elim (Nat.not_lt_zero j.val hj),by simp [result]⟩⟩
  have hg (t : Env) (ht : I t) : recoverOuterGuard.evalB W t =
      some (decide (t.vars coordinateSlot < n)) :=
    evalB_condLt (ev_var rfl (ht.2.1.trans_lt (by omega))) (ev_var ht.1.cols (by omega))
  have hStep (t : Env) (ht : I t) (hp : recoverOuterGuard.evalB W t = some true) :
      ∃ q, Run W recoverOuterStep t q (recoverRoundCost M m n+50) ∧ I q ∧ V q < V t := by
    rw [hg t ht] at hp
    have hi : t.vars coordinateSlot < n := by simpa using hp
    let i : Fin n := ⟨_,hi⟩
    obtain ⟨q,rr,hLq,hq,hP⟩ := recoverOuterStep_run A b i result hW hL ht.1 rfl ht.2.2
    refine ⟨q,rr,⟨hLq,by rw [hq]; exact Nat.succ_le_of_lt hi,by rw [hq]; exact hP⟩,?_⟩
    simp only [V,hq,i]
    omega
  obtain ⟨t,r1,hT,hStop⟩ := Run.while_count I V (recoverRoundCost M m n+50)
    (fun q hq => ⟨_,hg q hq⟩) hStep hI
  rw [hg t hT] at hStop
  have hDone : t.vars coordinateSlot = n := by
    have hge : ¬ t.vars coordinateSlot < n := by simpa using hStop
    have := hT.2.1
    omega
  have rr : Run W recoverAllCoordinates s t (recoverAllCoordinatesCost M m n) :=
    (r0.seq r1).mono (by simp [recoverAllCoordinatesCost,recoverOuterGuard,Cond.size,Expr.size,V,hSlot,
      show 4+(recoverRoundCost M m n+50)=recoverRoundCost M m n+54 by omega] <;> omega)
  have hFinal : Progress A b result n t := by simpa only [hDone] using hT.2.2
  refine ⟨t,rr,hT.1,hDone,Frame.of_run rr,?_⟩
  have hResult : fixPaddedCoordinates A b (List.finRange n) 0 0 = result := rfl
  rw [hResult]
  rcases hFinal with ⟨ha,w,_,hP,hR⟩ | ⟨ha,hR⟩
  · have hDrop : (List.finRange n).drop n = [] := by simp
    have hw : some w = result := by rw [hDrop] at hR; exact hR
    rw [← hw]
    exact ⟨ha,fun j => hP j j.isLt⟩
  · rw [hR]
    exact ha

#print axioms recoverAllCoordinates_run

end EvenTI.P14Recovery
