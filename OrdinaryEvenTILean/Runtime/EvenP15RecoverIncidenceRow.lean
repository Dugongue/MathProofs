import EvenP15RecoverResidueStore

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)
open EvenTI.P14Recovery (constraintMatrix)

set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def incidenceBank : String := "even.recovery.incidence.source"
def incidenceRow : String := "even.recovery.incidence.row"

def IncidenceInput {m n : ℕ} (s : Env) (src : Fin m → Fin 3 → Fin n) : Prop :=
  3*m ≤ (s.arrs incidenceBank).length ∧
  ∀ (r : Fin m) (e : Fin 3), (s.arrs incidenceBank).getD (3*r.val+e.val) 0 = (src r e).val

theorem IncidenceInput.congr_env {m n : ℕ} {s t : Env} {src : Fin m → Fin 3 → Fin n}
    (h : IncidenceInput s src) (ha : t.arrs incidenceBank = s.arrs incidenceBank) :
    IncidenceInput t src := by
  simpa only [IncidenceInput,ha] using h

private def incidenceIndex (e : Fin 3) : Expr :=
  .add (.mul (.lit 3) (.var incidenceRow)) (.lit e.val)

private def targetIndex (e : Fin 3) : Expr :=
  .add (.mul (.var incidenceRow) (.var inputColsR)) (.get incidenceBank (incidenceIndex e))

private def signedIncrement (e : Fin 3) : Expr :=
  if e.val = 0 then .lit 1 else .sub (.var modR) (.lit 1)

def writeIncidence (e : Fin 3) : Com :=
  .seq (.assign entryAddress (targetIndex e))
    (.seq (.assign entryIncrement (signedIncrement e)) updateResidue)

def ternarySign (M : ℕ) (e : Fin 3) : ZMod M :=
  if e.val = 0 then 1 else -1

theorem writeIncidence_run {M W m n : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (r : Fin m) (e : Fin 3)
    (hW : 2*M+4 < W) (hRows : 3*m < W) (hCols : n < W) (hWords : m*n < W)
    (hLen : m*n ≤ (s.arrs constraintMatrix).length)
    (hData : IncidenceInput s src) (hCan : Canonical M (s.arrs constraintMatrix))
    (hR : s.vars incidenceRow = r.val) (hN : s.vars inputColsR = n)
    (hMod : s.vars modR = M) :
    ∃ t, Run W (writeIncidence e) s t 45 ∧ Canonical M (t.arrs constraintMatrix) ∧
      (∀ i, decode M (t.arrs constraintMatrix) i = decode M (s.arrs constraintMatrix) i +
        if i = r.val*n+(src r e).val then ternarySign M e else 0) ∧
      (∀ i, i ≠ r.val*n+(src r e).val →
        (t.arrs constraintMatrix).getD i 0 = (s.arrs constraintMatrix).getD i 0) ∧
      Frame (writeIncidence e) s t := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hRv := r.isLt
  have hEv := e.isLt
  have hCW := (src r e).isLt.trans hCols
  have hRw : r.val < W := by omega
  have hIW : 3*r.val+e.val < W := by omega
  have hS : 3*r.val+e.val < (s.arrs incidenceBank).length := by have := hData.1; omega
  have hGet : (s.arrs incidenceBank)[3*r.val+e.val]? = some (src r e).val := by
    rw [List.getElem?_eq_getElem hS]
    simpa [List.getD,hS] using congrArg some (hData.2 r e)
  let j := r.val*n+(src r e).val
  have hj : j < m*n := Mathproof.P15GSSSmithLoad20261007.packed_lt r (src r e)
  have hjW := hj.trans hWords
  have eI : (incidenceIndex e).evalB W s = some (3*r.val+e.val) :=
    ev_add (ev_mul (evalB_lit (by omega)) (ev_var hR hRw) (by omega))
      (evalB_lit (by omega)) hIW
  have eJ : (targetIndex e).evalB W s = some j :=
    ev_add (ev_mul (ev_var hR hRw) (ev_var hN hCols) (by dsimp [j] at hjW; omega))
      (evalB_get eI hGet hCW) hjW
  let u := s.setVar entryAddress j
  have r0 : Run W (.assign entryAddress (targetIndex e)) s u 12 :=
    (Run.assign eJ).mono (by simp [targetIndex,incidenceIndex,Expr.size])
  have hmU : u.vars modR = M := by
    simpa [u,vars_setVar,show modR ≠ entryAddress by decide] using hMod
  let a := if e.val = 0 then 1 else M-1
  have ha : a ≤ M := by dsimp [a]; split <;> omega
  have eA : (signedIncrement e).evalB W u = some a := by
    by_cases he : e.val = 0
    · simpa only [signedIncrement,a,if_pos he] using
        (evalB_lit (σ:=u) (n:=1) (by omega : 1 < W))
    · rw [signedIncrement,if_neg he,show a = M-1 by simp [a,he]]
      change (Expr.bin .sub (.var modR) (.lit 1)).evalB W u = some (M-1)
      exact ev_sub (ev_var hmU (by omega)) (evalB_lit (n:=1) (by omega)) (by omega : M-1 < W)
  let z := u.setVar entryIncrement a
  have r1 : Run W (.assign entryIncrement (signedIncrement e)) u z 4 :=
    (Run.assign eA).mono (by by_cases he : e.val = 0 <;> simp [signedIncrement,he,Expr.size])
  have haZ : z.vars entryAddress = j := by simp [z,u,vars_setVar,show entryAddress ≠ entryIncrement by decide]
  have hmZ : z.vars modR = M := by simpa [z,vars_setVar,show modR ≠ entryIncrement by decide] using hmU
  obtain ⟨t,r2,hCanon,hE,hKeep,_⟩ := updateResidue_run hM (by omega : 2*M+2<W)
    (s:=z) hCan (hj.trans_le hLen) hjW ha haZ (by simp [z]) hmZ
  have haCast : (a : ZMod M) = ternarySign M e := by
    by_cases he : e.val = 0
    · simp [a,ternarySign,he]
    · simp only [a,ternarySign,if_neg he]
      rw [Nat.cast_sub (by omega : 1 ≤ M),ZMod.natCast_self,Nat.cast_one,zero_sub]
  have rr : Run W (writeIncidence e) s t 45 := (r0.seq (r1.seq r2)).mono (by decide)
  refine ⟨t,rr,hCanon,?_,hKeep,Frame.of_run rr⟩
  intro i
  rw [hE,haCast]
  change (if i = j then decode M (s.arrs constraintMatrix) i + ternarySign M e
    else decode M (s.arrs constraintMatrix) i) = decode M (s.arrs constraintMatrix) i +
      (if i = j then ternarySign M e else 0)
  by_cases he : i = j <;> simp [he]

#print axioms writeIncidence_run

end EvenTI.P15Recover
