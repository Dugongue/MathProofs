import EvenP12CompareLiveCRTPadding
import EvenP14CRTConstraints
import Mathproof.Meta.P15GSSSmithLoad20261007

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15GSSSmithLoad20261007 (packed_lt)
open EvenTI.P12Compare

set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

structure ConstraintBanks {M m n : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (w : Fin n → ZMod M) (p : ℕ) (σ : Env) : Prop where
  canonical : Canonical M (σ.arrs constraintMatrix)
  coefficient : ∀ (r : Fin (m+n)) (j : Fin n),
    decode M (σ.arrs constraintMatrix) (r.val*n+j.val) = fixedCoordinateMatrix A p r j
  probe : ∀ j : Fin n, (σ.arrs constraintMatrix).getD ((m+n)*n+j.val) 0 = 0
  rhs : σ.arrs crtRhsBank = List.ofFn (fun j => (fixedCoordinateRhs b w p j).val)

theorem ConstraintBanks.congr_env {M m n : ℕ} [NeZero M]
    {A : Matrix (Fin m) (Fin n) (ZMod M)} {b : Fin m → ZMod M}
    {w : Fin n → ZMod M} {p : ℕ} {σ τ : Env} (h : ConstraintBanks A b w p σ)
    (hA : τ.arrs constraintMatrix = σ.arrs constraintMatrix)
    (hb : τ.arrs crtRhsBank = σ.arrs crtRhsBank) : ConstraintBanks A b w p τ := by
  constructor
  · rw [hA]; exact h.canonical
  · rw [hA]; exact h.coefficient
  · rw [hA]; exact h.probe
  · rw [hb]; exact h.rhs

private theorem ofFn_store {N : ℕ} (f g : Fin N → ℕ) (r : Fin N) (v : ℕ)
    (h : ∀ i : Fin N, g i = if i = r then v else f i) :
    (List.ofFn f).set r.val v = List.ofFn g := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < N
  · let j : Fin N := ⟨k,hk⟩
    have hg := h j
    by_cases hj : j = r
    · have hEq : k = r.val := congrArg Fin.val hj
      rw [hEq,List.getElem?_set_self (by simpa using r.isLt)]
      simp [r.isLt,h r]
    · have hne : r.val ≠ k := fun hEq => hj (Fin.ext hEq.symm)
      rw [List.getElem?_set_ne hne]
      simp only [List.getElem?_ofFn,dif_pos hk]
      rw [hg,if_neg hj]
  · rw [List.getElem?_eq_none (by simp [Nat.le_of_not_gt hk]),List.getElem?_ofFn,dif_neg hk]

private theorem packed_entry_iff {m n : ℕ} (r : Fin (m+n)) (j i : Fin n) :
    r.val*n+j.val = (m+i.val)*n+i.val ↔ r.val = m+i.val ∧ j = i := by
  constructor
  · intro h
    have hmod := congrArg (fun x => x%n) h
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt,Nat.mod_eq_of_lt i.isLt] at hmod
    have hj : j = i := Fin.ext hmod
    have hdiv := congrArg (fun x => x/n) h
    have hn : 0 < n := by have := i.isLt; omega
    change (r.val*n+j.val)/n = ((m+i.val)*n+i.val)/n at hdiv
    rw [Nat.mul_comm r.val n,Nat.mul_comm (m+i.val) n,Nat.mul_add_div hn,
      Nat.mul_add_div hn,Nat.div_eq_of_lt j.isLt,Nat.div_eq_of_lt i.isLt] at hdiv
    exact ⟨by simpa using hdiv,hj⟩
  · rintro ⟨hr,rfl⟩
    rw [hr]

theorem ConstraintBanks.advance {M m n : ℕ} [NeZero M]
    {A : Matrix (Fin m) (Fin n) (ZMod M)} {b : Fin m → ZMod M}
    {w : Fin n → ZMod M} {σ τ : Env}
    (i : Fin n) (v : ZMod M) (h : ConstraintBanks A b w i.val σ)
    (hL : (m+n+1)*n ≤ (σ.arrs constraintMatrix).length)
    (hA : τ.arrs constraintMatrix = (σ.arrs constraintMatrix).set ((m+i.val)*n+i.val) (1%M))
    (hb : τ.arrs crtRhsBank = (σ.arrs crtRhsBank).set (m+i.val) v.val) :
    ConstraintBanks A b (Function.update w i v) (i.val+1) τ := by
  let r₀ : Fin (m+n) := ⟨m+i.val,Nat.add_lt_add_left i.isLt m⟩
  have ha0 : (m+i.val)*n+i.val < (m+n)*n := packed_lt r₀ i
  have ha1 : (m+i.val)*n+i.val < (σ.arrs constraintMatrix).length := by
    rw [Nat.add_mul,Nat.one_mul] at hL
    omega
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  constructor
  · intro j
    rw [hA]
    by_cases hj : j = (m+i.val)*n+i.val
    · subst j
      rw [getD_set_self' ha1]
      exact Nat.mod_lt _ hM
    · rw [getD_set_ne' (Ne.symm hj)]
      exact h.canonical j
  · intro r j
    rw [hA,fixedCoordinateMatrix_succ]
    by_cases hj : r.val = m+i.val ∧ j = i
    · rw [if_pos hj,(packed_entry_iff r j i).mpr hj,decode,getD_set_self' ha1]
      simp [ZMod.natCast_mod]
    · rw [if_neg hj,decode,getD_set_ne' (Ne.symm (fun he => hj ((packed_entry_iff r j i).mp he)))]
      exact h.coefficient r j
  · intro j
    rw [hA,getD_set_ne' (by omega)]
    exact h.probe j
  · rw [hb,h.rhs]
    apply ofFn_store _ _ r₀
    intro r
    rw [fixedCoordinateRhs_succ]
    by_cases hr : r = r₀
    · subst r
      simp [r₀]
    · have hne : r.val ≠ m+i.val := fun he => hr (Fin.ext he)
      rw [if_neg hr,if_neg hne]

def CoordinatePrefix {M n : ℕ} (w : Fin n → ZMod M) (p : ℕ) (σ : Env) : Prop :=
  ∀ i : Fin n, i.val < p → (σ.arrs coordinateBank).getD i.val 0 = (w i).val

theorem CoordinatePrefix.advance {M n : ℕ} {w : Fin n → ZMod M} {σ τ : Env}
    (i : Fin n) (v : ZMod M) (h : CoordinatePrefix w i.val σ)
    (hL : i.val < (σ.arrs coordinateBank).length)
    (hStore : τ.arrs coordinateBank = (σ.arrs coordinateBank).set i.val v.val) :
    CoordinatePrefix (Function.update w i v) (i.val+1) τ := by
  intro j hj
  rw [hStore]
  by_cases he : j = i
  · subst j
    rw [getD_set_self' hL,Function.update_self]
  · have hval : i.val ≠ j.val := fun hEq => he (Fin.ext hEq.symm)
    rw [getD_set_ne' hval,Function.update_of_ne he]
    have hn : j.val ≠ i.val := Ne.symm hval
    exact h j (by omega)

#print axioms ConstraintBanks.advance
#print axioms CoordinatePrefix.advance

end EvenTI.P14Recovery
