import EvenP14CRTConstraints

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open EvenTI.P12Compare

def probeEntry : Expr :=
  .add (.mul (.sub (.var rowsR) (.lit 1)) (.var inputColsR)) (.var coordinateSlot)

def storeProbe : Com := .store matrixR probeEntry unitWord
def prepareSmithProbe : Com := .seq reloadSmithConstraints storeProbe

private theorem evalLive' {B v : ℕ} {s : Env} {x : String}
    (h : s.vars x=v) (hv : v<B) : (Expr.var x).evalB B s=some v :=
  evalB_var_iff.mpr ⟨h.symm,h ▸ hv⟩

private theorem storeProbe_run {M B m n : Nat} (i : Fin n) {s : Env}
    (hB : 1<B) (hM : M<B) (hm : s.vars rowsR=m+1)
    (hn : s.vars inputColsR=n) (hi : s.vars coordinateSlot=i.val) (hmod : s.vars modR=M)
    (hmB : m+1<B) (hnB : n<B) (hCells : (m+1)*n<B) (hLen : (m+1)*n≤(s.arrs matrixR).length) :
    ∃ t, Run B storeProbe s t 16 ∧
      t.arrs matrixR=(s.arrs matrixR).set (m*n+i.val) (1%M) ∧
      Frame storeProbe s t := by
  have hmₙ : m*n+i.val < (m+1)*n := by rw [Nat.add_mul,Nat.one_mul]; have := i.isLt; omega
  have er : (Expr.sub (.var rowsR) (.lit 1)).evalB B s = some m := by
    have h := evalB_bin (op:=.sub) (evalLive' hm hmB) (evalB_lit hB)
      (by change m+1-1<B; omega)
    simpa only [Bop.apply,Nat.add_sub_cancel] using h
  have ea : probeEntry.evalB B s = some (m*n+i.val) :=
    evalB_bin (op:=.add)
      (evalB_bin (op:=.mul) er (evalLive' hn hnB) (by change m*n<B; omega))
      (evalLive' hi (i.isLt.trans hnB)) (hmₙ.trans hCells)
  have d := Nat.div_le_self 1 M
  have h := Nat.div_mul_le_self 1 M
  have q := evalB_bin (op:=.div) (evalB_lit (σ:=s) hB) (evalLive' hmod hM)
    (by change 1/M<B; omega)
  have p := evalB_bin (op:=.mul) q (evalLive' hmod hM) (by change (1/M)*M<B; omega)
  have e : unitWord.evalB B s = some (1%M) := by
    have u := evalB_bin (op:=.sub) (evalB_lit hB) p (by change 1-(1/M)*M<B; omega)
    simpa only [unitWord,Bop.apply,Nat.mod_def,Nat.mul_comm] using u
  let t := s.setArr matrixR (m*n+i.val) (1%M)
  have rr : Run B storeProbe s t (1+probeEntry.size+unitWord.size) :=
    Run.store ea e (hmₙ.trans_le hLen)
  have run : Run B storeProbe s t 16 := rr.mono (by decide)
  exact ⟨t,run,by simp [t,arrs_setArr],Frame.of_run run⟩

/-- The persistent coefficient bank includes a final zero row. One replay
and one store install the literal input of the checked Smith recovery call. -/
theorem prepareSmithProbe_run {M B m n : Nat} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (i : Fin n) {s : Env}
    (hB : 1 < B) (hM : M < B) (hm : s.vars rowsR=m+1) (hn : s.vars inputColsR=n)
    (hi : s.vars coordinateSlot=i.val) (hmod : s.vars modR=M)
    (hmB : m+1<B) (hnB : n<B) (hCells : (m+1)*n<B)
    (hS : (m+1)*n≤(s.arrs constraintMatrix).length)
    (hT : (m+1)*n≤(s.arrs matrixR).length)
    (hMs : Canonical M (s.arrs constraintMatrix)) (hMt : Canonical M (s.arrs matrixR))
    (hA : ∀ r : Fin m, ∀ j : Fin n, decode M (s.arrs constraintMatrix) (r.val*n+j.val) = A r j)
    (hz : ∀ j : Fin n, (s.arrs constraintMatrix).getD (m*n+j.val) 0 = 0) :
    ∃ t, Run B prepareSmithProbe s t (20*((m+1)*n)+30) ∧
      Canonical M (t.arrs matrixR) ∧
      (∀ r : Fin (m+1), ∀ j : Fin n,
        decode M (t.arrs matrixR) (r.val*n+j.val) = appendCoordinate A i r j) ∧
      Frame prepareSmithProbe s t := by
  obtain ⟨u,ru,hu,hTail,f⟩ := reloadSmithConstraints_run hB hmB hnB hCells hm hn hS hT
    (fun j _ => (hMs j).trans hM)
  have hLen : (m+1)*n≤(u.arrs matrixR).length := by rw [f.len]; exact hT
  obtain ⟨t,rt,ht,g⟩ := storeProbe_run i hB hM ((f.vars _ (by decide)).trans hm)
    ((f.vars _ (by decide)).trans hn) ((f.vars _ (by decide)).trans hi)
    ((f.vars _ (by decide)).trans hmod) hmB hnB hCells hLen
  have hMp := Nat.pos_of_ne_zero (NeZero.ne M)
  have hj (j : Fin n) : m*n+j.val < (m+1)*n := by rw [Nat.add_mul,Nat.one_mul]; have := j.isLt; omega
  refine ⟨t,ru.seq rt,?_,?_,Frame.of_run (ru.seq rt)⟩
  · intro j
    rw [ht]
    by_cases hj' : j=m*n+i.val
    · subst j
      rw [getD_set_self' ((hj i).trans_le hLen)]
      exact Nat.mod_lt _ hMp
    · rw [getD_set_ne' (Ne.symm hj')]
      by_cases hk : j < (m+1)*n
      · rw [hu j hk]
        exact hMs j
      · rw [hTail j (Nat.le_of_not_gt hk)]
        exact hMt j
  · intro r j
    refine Fin.lastCases ?_ (fun q => ?_) r
    · simp only [appendCoordinate,Fin.lastCases_last,Fin.val_last]
      change (((t.arrs matrixR).getD (m*n+j.val) 0 : ℕ) : ZMod M) = _
      rw [ht]
      by_cases h : j=i
      · subst j
        rw [getD_set_self' ((hj i).trans_le hLen),if_pos rfl]
        simp
      · have ne : m*n+j.val ≠ m*n+i.val := fun he => h (Fin.ext (by omega))
        rw [getD_set_ne' (Ne.symm ne),hu _ (hj j),hz j,if_neg h]
        simp
    · simp only [appendCoordinate,Fin.lastCases_castSucc,Fin.val_castSucc]
      have hb := Nat.mul_le_mul_right n (show q.val+1 ≤ m from q.isLt)
      rw [Nat.add_mul,Nat.one_mul] at hb
      have hq : q.val*n+j.val < m*n := by have := j.isLt; omega
      have hq' : q.val*n+j.val < (m+1)*n := by rw [Nat.add_mul,Nat.one_mul]; omega
      change (((t.arrs matrixR).getD (q.val*n+j.val) 0 : ℕ) : ZMod M) = A q j
      rw [ht,getD_set_ne' (by omega),hu _ hq']
      exact hA q j

#print axioms prepareSmithProbe_run
end EvenTI.P14Recovery
