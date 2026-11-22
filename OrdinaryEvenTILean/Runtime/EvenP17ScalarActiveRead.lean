import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace EvenTI.P17Scalar.ActiveRead

open Lax13Proofs.Imp Lax13Proofs.Reasoning

def indexedResidue (coords slots cursor : String) : Expr :=
  .get coords (.get slots (.var cursor))

def keepResidueBit (coords slots cursor reference answer : String) : Com :=
  .ite (.eq (indexedResidue coords slots cursor) (.var reference))
    .skip (.assign answer (.lit 0))

theorem indexedResidue_eval {W k slot value : ℕ} {s : Env}
    (coords slots cursor : String)
    (hCursor : s.vars cursor=k) (hk : k < W)
    (hSlot : (s.arrs slots)[k]?=some slot) (hs : slot < W)
    (hValue : (s.arrs coords)[slot]?=some value) (hv : value < W) :
    (indexedResidue coords slots cursor).evalB W s=some value := by
  have ec : (Expr.var cursor).evalB W s=some k :=
    evalB_var_iff.mpr ⟨hCursor.symm,by rwa [hCursor]⟩
  exact evalB_get (evalB_get ec hSlot hs) hValue hv

/-- One paid residue equality visit, with its entire host-state frame. -/
theorem keepResidueBit_run {W k slot value saved : ℕ} {s : Env}
    (coords slots cursor reference answer : String)
    (hCursor : s.vars cursor=k) (hk : k < W)
    (hSlot : (s.arrs slots)[k]?=some slot) (hs : slot < W)
    (hValue : (s.arrs coords)[slot]?=some value) (hv : value < W)
    (hReference : s.vars reference=saved) (hr : saved < W)
    (hW : 0 < W) :
    ∃ t, Run W (keepResidueBit coords slots cursor reference answer) s t 10 ∧
      t.vars answer=(if value=saved then s.vars answer else 0) ∧
      (∀ x, x ≠ answer → t.vars x=s.vars x) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  have ev := indexedResidue_eval coords slots cursor hCursor hk hSlot hs hValue hv
  have er : (Expr.var reference).evalB W s=some saved :=
    evalB_var_iff.mpr ⟨hReference.symm,by rwa [hReference]⟩
  have eg := evalB_condEq ev er
  by_cases he : value=saved
  · have et : (Cond.eq (indexedResidue coords slots cursor) (.var reference)).evalB W s=some true := by
      simpa [he] using eg
    refine ⟨s,?_,by simp [he],fun _ _ => rfl,rfl,rfl,rfl⟩
    exact (Run.ite_true (d:=.assign answer (.lit 0)) et Run.skip).mono (by
      simp [indexedResidue,Cond.size,Expr.size])
  · have ef : (Cond.eq (indexedResidue coords slots cursor) (.var reference)).evalB W s=some false := by
      simpa [he,beq_iff_eq] using eg
    refine ⟨s.setVar answer 0,?_,by simp [he],fun x hx => by simp [hx],rfl,rfl,rfl⟩
    exact (Run.ite_false (c:=.skip) ef (Run.assign (evalB_lit hW))).mono (by
      simp [indexedResidue,Cond.size,Expr.size])

#print axioms indexedResidue_eval
#print axioms keepResidueBit_run
end EvenTI.P17Scalar.ActiveRead
