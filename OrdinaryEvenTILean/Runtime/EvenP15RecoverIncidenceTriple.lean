import EvenP15RecoverIncidenceRow

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open EvenTI.P14Recovery (constraintMatrix)

set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def incidenceMatrix {m n : ℕ} (M : ℕ) (src : Fin m → Fin 3 → Fin n) :
    Matrix (Fin m) (Fin n) (ZMod M) :=
  fun r j => (if src r 0 = j then 1 else 0) -
    (if src r 1 = j then 1 else 0) - (if src r 2 = j then 1 else 0)

private theorem sameEntry {m n : ℕ} (r q : Fin m) (i j : Fin n) :
    r.val*n+i.val = q.val*n+j.val ↔ r = q ∧ i = j := by
  constructor
  · intro h
    have hn : 0 < n := by have := i.isLt; omega
    have hmod := congrArg (fun x => x%n) h
    have hdiv := congrArg (fun x => x/n) h
    change (r.val*n+i.val)%n = (q.val*n+j.val)%n at hmod
    change (r.val*n+i.val)/n = (q.val*n+j.val)/n at hdiv
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hmod
    simp only [Nat.mul_comm _ n,Nat.mul_add_div hn,Nat.div_eq_of_lt i.isLt,Nat.div_eq_of_lt j.isLt,
      Nat.add_zero] at hdiv
    exact ⟨Fin.ext hdiv,Fin.ext hmod⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def writeTriple : Com := .seq (writeIncidence (0 : Fin 3))
  (.seq (writeIncidence (1 : Fin 3)) (writeIncidence (2 : Fin 3)))

theorem writeTriple_run {M W m n : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (r : Fin m)
    (hW : 2*M+4 < W) (hRows : 3*m < W) (hCols : n < W) (hWords : m*n < W)
    (hLen : m*n ≤ (s.arrs constraintMatrix).length)
    (hData : IncidenceInput s src) (hCan : Canonical M (s.arrs constraintMatrix))
    (hR : s.vars incidenceRow = r.val) (hN : s.vars inputColsR = n)
    (hMod : s.vars modR = M) :
    ∃ t, Run W writeTriple s t 135 ∧ Canonical M (t.arrs constraintMatrix) ∧
      (∀ (q : Fin m) (j : Fin n), decode M (t.arrs constraintMatrix) (q.val*n+j.val) =
        decode M (s.arrs constraintMatrix) (q.val*n+j.val) +
          if q = r then incidenceMatrix M src r j else 0) ∧
      (∀ i, m*n ≤ i → (t.arrs constraintMatrix).getD i 0 = (s.arrs constraintMatrix).getD i 0) ∧
      Frame writeTriple s t := by
  obtain ⟨u,r0,hCan0,hE0,hP0,f0⟩ :=
    writeIncidence_run src r (0 : Fin 3) hW hRows hCols hWords hLen hData hCan hR hN hMod
  obtain ⟨v,r1,hCan1,hE1,hP1,_⟩ := writeIncidence_run src r (1 : Fin 3) hW hRows hCols hWords
    (by rw [f0.len _]; exact hLen) (hData.congr_env (f0.arrs _ (by decide))) hCan0
    ((f0.vars _ (by decide)).trans hR) ((f0.vars _ (by decide)).trans hN) ((f0.vars _ (by decide)).trans hMod)
  have f01 := Frame.of_run (r0.seq r1)
  obtain ⟨t,r2,hCan2,hE2,hP2,_⟩ := writeIncidence_run src r (2 : Fin 3) hW hRows hCols hWords
    (by rw [f01.len _]; exact hLen) (hData.congr_env (f01.arrs _ (by decide))) hCan1
    ((f01.vars _ (by decide)).trans hR) ((f01.vars _ (by decide)).trans hN) ((f01.vars _ (by decide)).trans hMod)
  have rr : Run W writeTriple s t 135 := r0.seq (r1.seq r2)
  refine ⟨t,rr,hCan2,?_,?_,Frame.of_run rr⟩
  · intro q j
    simp only [hE2,hE1,hE0,sameEntry q r j (src r (2 : Fin 3)),sameEntry q r j (src r (1 : Fin 3)),
      sameEntry q r j (src r (0 : Fin 3))]
    by_cases h : q = r
    · subst q
      have sign0 : ternarySign M (0 : Fin 3) = 1 := rfl
      have sign1 : ternarySign M (1 : Fin 3) = -1 := rfl
      have sign2 : ternarySign M (2 : Fin 3) = -1 := rfl
      have eq0 : (j = src r 0) ↔ (src r 0 = j) := eq_comm
      have eq1 : (j = src r 1) ↔ (src r 1 = j) := eq_comm
      have eq2 : (j = src r 2) ↔ (src r 2 = j) := eq_comm
      simp only [true_and,if_pos rfl,sign0,sign1,sign2,incidenceMatrix,eq0,eq1,eq2]
      by_cases h0 : src r 0 = j <;> by_cases h1 : src r 1 = j <;> by_cases h2 : src r 2 = j <;>
        simp [h0,h1,h2] <;> ring
    · simp [h]
  · intro i hi
    have hL (e : Fin 3) : r.val*n+(src r e).val < m*n :=
      Mathproof.P15GSSSmithLoad20261007.packed_lt r (src r e)
    rw [hP2 i (by have := hL (2 : Fin 3); omega),hP1 i (by have := hL (1 : Fin 3); omega),
      hP0 i (by have := hL (0 : Fin 3); omega)]

#print axioms writeTriple_run

end EvenTI.P15Recover
