import EvenP14CRTComplete
import EvenP8BaseResidual

namespace EvenTI.P15Recover

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)
open EvenTI.P14Recovery (constraintMatrix)

set_option maxRecDepth 15000
set_option maxHeartbeats 2000000

def entryAddress : String := "even.recovery.residue.address"
def entryIncrement : String := "even.recovery.residue.delta"

def wordRem (x y : Expr) : Expr := .sub x (.mul (.div x y) y)

theorem eval_wordRem {W x y : ℕ} {f g : Expr} {s : Env}
    (hf : f.evalB W s = some x) (hg : g.evalB W s = some y) :
    (wordRem f g).evalB W s = some (x%y) := by
  have hx := Expr.lt_of_evalB hf
  unfold wordRem
  exact (ev_sub hf (ev_mul (ev_div hf hg ((Nat.div_le_self ..).trans_lt hx))
    hg ((Nat.div_mul_le_self ..).trans_lt hx)) ((Nat.sub_le ..).trans_lt hx)).trans
    (congrArg some (hmdg x y))

private def deltaValue : Expr :=
  .add (.get constraintMatrix (.var entryAddress)) (.var entryIncrement)

def updateResidue : Com :=
  .store constraintMatrix (.var entryAddress) (wordRem deltaValue (.var modR))

/-- Add a bounded integer residue to the addressed coefficient. All other
cells are retained, including unused padded coordinate rows. -/
theorem updateResidue_run {M W j a : ℕ} [NeZero M] {s : Env}
    (hM : 0 < M) (hW : 2*M+2 < W)
    (hs : Canonical M (s.arrs constraintMatrix))
    (hLen : j < (s.arrs constraintMatrix).length) (hj : j < W) (ha : a ≤ M)
    (hAddr : s.vars entryAddress = j) (hInc : s.vars entryIncrement = a)
    (hMod : s.vars modR = M) :
    ∃ t, Run W updateResidue s t 21 ∧ Canonical M (t.arrs constraintMatrix) ∧
      (∀ i, decode M (t.arrs constraintMatrix) i =
        if i = j then decode M (s.arrs constraintMatrix) i + (a : ZMod M)
        else decode M (s.arrs constraintMatrix) i) ∧
      (∀ i, i ≠ j → (t.arrs constraintMatrix).getD i 0 = (s.arrs constraintMatrix).getD i 0) ∧
      Frame updateResidue s t := by
  let u := (s.arrs constraintMatrix).getD j 0
  let v := (u+a)%M
  have hv : v < M := Nat.mod_lt _ hM
  have hu : u < M := hs j
  have hD : (s.arrs constraintMatrix)[j]? = some u := by
    rw [List.getElem?_eq_getElem hLen]
    simp [u,List.getD,hLen]
  have ep : (Expr.var entryAddress).evalB W s = some j := ev_var hAddr hj
  have e0 : deltaValue.evalB W s = some (u+a) :=
    ev_add (evalB_get ep hD (by omega)) (ev_var hInc (by omega)) (by omega)
  have e1 : (wordRem deltaValue (.var modR)).evalB W s = some v :=
    eval_wordRem e0 (ev_var hMod (by omega))
  let t := s.setArr constraintMatrix j v
  have r : Run W updateResidue s t 21 := (Run.store ep e1 hLen).mono (by decide)
  have ht : t.arrs constraintMatrix = (s.arrs constraintMatrix).set j v := by simp [t]
  have hKeep (i) (hi : i ≠ j) : (t.arrs constraintMatrix).getD i 0 =
        (s.arrs constraintMatrix).getD i 0 := by
    rw [ht,getD_set_ne' (Ne.symm hi)]
  refine ⟨t,r,?_,?_,hKeep,Frame.of_run r⟩
  · intro i
    by_cases hi : i = j
    · subst i
      rw [ht,getD_set_self' hLen]
      exact hv
    · rw [hKeep i hi]
      exact hs i
  · intro i
    by_cases hi : i = j
    · subst i
      rw [if_pos rfl,decode,ht,getD_set_self' hLen]
      change (((u+a)%M : ℕ) : ZMod M) = (u : ZMod M)+(a : ZMod M)
      rw [ZMod.natCast_mod,Nat.cast_add]
    · rw [if_neg hi]
      unfold decode
      rw [hKeep i hi]

#print axioms updateResidue_run

end EvenTI.P15Recover
