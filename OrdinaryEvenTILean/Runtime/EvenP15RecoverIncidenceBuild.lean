import EvenP15RecoverIncidenceTriple
import Mathproof.Meta.Problem18PairLargeBank20261004

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)
open Mathproof.Problem18PairLargeBank20261004 (zeroBlock zeroBlock_run Clean)
open Mathproof.Problem18PairLargeWords20261004 (wcSrc wcDst wcCnt)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)
open EvenTI.P14Recovery (constraintMatrix baseRows)
open EvenTI.P12Compare (fixedCoordinateMatrix)

set_option maxRecDepth 25000
set_option maxHeartbeats 4500000

private def clearShape : Expr := .mul (.var rowsR) (.var inputColsR)
private def clearConstraints : Com := zeroBlock constraintMatrix (.lit 0) clearShape
private def startRows : Com := .assign incidenceRow (.lit 0)
private def advanceRow : Com := .assign incidenceRow (.add (.var incidenceRow) (.lit 1))
private def installStep : Com := .seq writeTriple advanceRow
private def installGuard : Cond := .lt (.var incidenceRow) (.var baseRows)
def buildIncidenceMatrix : Com := .seq clearConstraints (.seq startRows (.while installGuard installStep))
def buildIncidenceCost (m n : ℕ) : ℕ := 20*((m+n+1)*n)+143*m+24

private def BankPrefix {m n : ℕ} (M : ℕ) (src : Fin m → Fin 3 → Fin n) (p : ℕ) (s : Env) : Prop :=
  ∀ (q : Fin m) (j : Fin n), decode M (s.arrs constraintMatrix) (q.val*n+j.val) =
    if q.val < p then incidenceMatrix M src q j else 0

private def PaddingZero (m n : ℕ) (s : Env) : Prop :=
  ∀ i, m*n ≤ i → i < (m+n+1)*n → (s.arrs constraintMatrix).getD i 0 = 0

private structure FillState {m n : ℕ} (M : ℕ) (src : Fin m → Fin 3 → Fin n) (p : ℕ) (s : Env) : Prop where
  source : IncidenceInput s src
  length : (m+n+1)*n ≤ (s.arrs constraintMatrix).length
  canonical : Canonical M (s.arrs constraintMatrix)
  count : s.vars baseRows = m
  width : s.vars inputColsR = n
  modWord : s.vars modR = M
  data : BankPrefix M src p s
  pad : PaddingZero m n s

private theorem installStep_run {m n M W : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (r : Fin m)
    (hW : 2*M+4 < W) (hRows : 3*m < W) (hCols : n < W) (hWords : m*n < W)
    (hS : FillState M src r.val s) (hR : s.vars incidenceRow = r.val) :
    ∃ t, Run W installStep s t 139 ∧ t.vars incidenceRow = r.val+1 ∧
      FillState M src (r.val+1) t := by
  have hP : m*n ≤ (m+n+1)*n := Nat.mul_le_mul_right n (by omega)
  obtain ⟨u,r0,hCan,hD,hPad,hF⟩ := writeTriple_run src r hW hRows hCols hWords
    (hP.trans hS.length) hS.source hS.canonical hR hS.width hS.modWord
  have hR' : u.vars incidenceRow = r.val := (hF.vars _ (by decide)).trans hR
  let t := u.setVar incidenceRow (r.val+1)
  have r1 : Run W advanceRow u t 4 := Run.assign
    (ev_add (ev_var hR' (by have := r.isLt; omega)) (evalB_lit (by omega))
      (by have := r.isLt; omega))
  have rr : Run W installStep s t 139 := r0.seq r1
  have hf := Frame.of_run rr
  refine ⟨t,rr,by simp [t],⟨hS.source.congr_env (hf.arrs _ (by decide)),
    by rw [hf.len _]; exact hS.length,hCan,(hf.vars _ (by decide)).trans hS.count,
    (hf.vars _ (by decide)).trans hS.width,(hf.vars _ (by decide)).trans hS.modWord,?_,?_⟩⟩
  · intro q j
    change decode M (u.arrs constraintMatrix) _ = _
    rw [hD q j,hS.data q j]
    by_cases h : q = r
    · subst q
      simp
    · have neq : q.val ≠ r.val := fun hEq => h (Fin.ext hEq)
      have iff' : q.val < r.val+1 ↔ q.val < r.val := by omega
      simp [h,iff']
  · intro i hi hj
    change (u.arrs constraintMatrix).getD i 0 = 0
    rw [hPad i hi]
    exact hS.pad i hi hj

/-- Clear the durable fixed constraint bank and install all three live
incidences per row. The symbolic probe and unused unit rows stay zero. -/
theorem buildIncidenceMatrix_run {m n M W : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n)
    (hW : 2*M+4 < W) (hRows : 3*m < W) (hCols : n < W) (hTotal : (m+n+1)*n < W)
    (hHeight : m+n+1 < W)
    (hData : IncidenceInput s src) (hCan : Canonical M (s.arrs constraintMatrix))
    (hCap : (m+n+1)*n ≤ (s.arrs constraintMatrix).length)
    (hCapW : (s.arrs constraintMatrix).length < W)
    (hR : s.vars rowsR = m+n+1) (hB : s.vars baseRows = m) (hN : s.vars inputColsR = n)
    (hMod : s.vars modR = M) :
    ∃ t, Run W buildIncidenceMatrix s t (buildIncidenceCost m n) ∧
      Canonical M (t.arrs constraintMatrix) ∧
      (∀ (q : Fin m) (j : Fin n),
        decode M (t.arrs constraintMatrix) (q.val*n+j.val) = incidenceMatrix M src q j) ∧
      PaddingZero m n t ∧ Frame buildIncidenceMatrix s t := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hParentSize : m*n ≤ (m+n+1)*n := Nat.mul_le_mul_right n (by omega)
  have hW1 : 1 < W := by omega
  have eCount : clearShape.evalB W s = some ((m+n+1)*n) :=
    ev_mul (ev_var hR hHeight) (ev_var hN hCols) hTotal
  obtain ⟨u,r0,_,_,hLen,hFill,_,_⟩ := zeroBlock_run constraintMatrix s (d:=.lit 0)
    (n:=clearShape) (by simp [Clean,clearShape,NoVar,wcSrc,wcDst,wcCnt,rowsR,inputColsR] : Clean clearShape)
    (evalB_lit (by omega)) eCount (by simpa using hCap) hCapW hW1
  have rr0 : Run W clearConstraints s u (20*((m+n+1)*n)+16) := r0
  have h0 := Frame.of_run rr0
  let v := u.setVar incidenceRow 0
  have rr1 : Run W startRows u v 2 := Run.assign (evalB_lit (by omega))
  have hvCursor : v.vars incidenceRow = 0 := by simp [v]
  have f := Frame.of_run (rr0.seq rr1)
  have hv : FillState M src 0 v := by
    refine ⟨hData.congr_env (f.arrs _ (by decide)),by rw [f.len _]; exact hCap,?_,
      (f.vars _ (by decide)).trans hB,(f.vars _ (by decide)).trans hN,
      (f.vars _ (by decide)).trans hMod,?_,?_⟩
    · intro j
      change (u.arrs constraintMatrix).getD j 0 < M
      rw [hFill j]
      split
      · exact hM
      · exact hCan j
    · intro q j
      have hj := (packed_lt q j).trans_le hParentSize
      change decode M (u.arrs constraintMatrix) (q.val*n+j.val) = _
      simp only [decode,hFill,Nat.zero_add,Nat.zero_le,true_and,if_pos hj,Nat.cast_zero,
        Nat.not_lt_zero,if_false]
    · intro i hi hj
      change (u.arrs constraintMatrix).getD i 0 = 0
      simpa [hj] using hFill i
  let I (s : Env) := s.vars incidenceRow ≤ m ∧ FillState M src (s.vars incidenceRow) s
  let potential (s : Env) := m-s.vars incidenceRow
  have hg (u : Env) (hu : I u) : installGuard.evalB W u =
      some (decide (u.vars incidenceRow < m)) :=
    evalB_condLt (ev_var rfl (by have := hu.1; omega)) (ev_var hu.2.count (by omega))
  have hStep (u : Env) (hu : I u) (hStep : installGuard.evalB W u = some true) :
      ∃ v, Run W installStep u v 139 ∧ I v ∧ potential v < potential u := by
    rw [hg u hu] at hStep
    have hLt : u.vars incidenceRow < m := by simpa using hStep
    let r : Fin m := ⟨_,hLt⟩
    obtain ⟨v,rr,hNext,hv⟩ := installStep_run src r hW hRows hCols
      (hParentSize.trans_lt hTotal) hu.2 rfl
    refine ⟨v,rr,⟨by rw [hNext]; exact Nat.succ_le_of_lt hLt,by rw [hNext]; exact hv⟩,?_⟩
    simp only [potential,hNext,r]
    omega
  have hi0 : I v := ⟨by simp [hvCursor],by rwa [hvCursor]⟩
  obtain ⟨t,rr2,ht,hStop⟩ := Run.while_count I potential 139
    (fun u hu => ⟨_,hg u hu⟩) hStep hi0
  rw [hg t ht] at hStop
  have hd : t.vars incidenceRow = m := by
    have hGe : ¬ t.vars incidenceRow < m := by simpa using hStop
    have := ht.1
    omega
  have result : Run W buildIncidenceMatrix s t (buildIncidenceCost m n) :=
    (rr0.seq (rr1.seq rr2)).mono (by
      simp [buildIncidenceCost,potential,hvCursor,installGuard,Cond.size,Expr.size] <;> omega)
  refine ⟨t,result,ht.2.canonical,?_,ht.2.pad,Frame.of_run result⟩
  intro q j
  simpa [hd,q.isLt] using ht.2.data q j

#print axioms buildIncidenceMatrix_run

end EvenTI.P15Recover
