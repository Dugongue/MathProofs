import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace EvenTI.P17Scalar.ActiveProducer

open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- Emit a fixed-length active-slot stencil. A zero chart entry contributes
the reference slot, so no compaction or variable-length allocation is needed. -/
def installSlot (chart sites target cursor columns zero reference : String) : Com :=
  .ite (.eq (.get chart (.var cursor)) (.var zero))
    (.store target (.var cursor) (.var reference))
    (.store target (.var cursor) (.get sites (.div (.var cursor) (.var columns))))

/-- One actual live row-major chart entry installs its corresponding site
slot, or the harmless reference slot when the entry is zero. -/
theorem installSlot_run
    {W k cols label zeroWord referenceSlot siteSlot : ℕ} {s : Env}
    (chart sites target cursor columns zero reference : String)
    (hCursor : s.vars cursor=k) (hk : k < W)
    (hColumns : s.vars columns=cols) (hc : cols < W) (hRow : k/cols < W)
    (hLabel : (s.arrs chart)[k]?=some label) (hl : label < W)
    (hZero : s.vars zero=zeroWord) (hz : zeroWord < W)
    (hReference : s.vars reference=referenceSlot) (hr : referenceSlot < W)
    (hSite : (s.arrs sites)[k/cols]?=some siteSlot) (hs : siteSlot < W)
    (hTarget : k < (s.arrs target).length) :
    Run W (installSlot chart sites target cursor columns zero reference) s
      (s.setArr target k (if label=zeroWord then referenceSlot else siteSlot)) 20 := by
  have ek : (Expr.var cursor).evalB W s=some k :=
    evalB_var_iff.mpr ⟨hCursor.symm,by rwa [hCursor]⟩
  have el : (Expr.get chart (.var cursor)).evalB W s=some label :=
    evalB_get ek hLabel hl
  have ez : (Expr.var zero).evalB W s=some zeroWord :=
    evalB_var_iff.mpr ⟨hZero.symm,by rwa [hZero]⟩
  have eg := evalB_condEq el ez
  by_cases he : label=zeroWord
  · have et : (Cond.eq (.get chart (.var cursor)) (.var zero)).evalB W s=some true := by
      simpa [he] using eg
    have er : (Expr.var reference).evalB W s=some referenceSlot :=
      evalB_var_iff.mpr ⟨hReference.symm,by rwa [hReference]⟩
    simpa only [installSlot,he,if_true] using
      (Run.ite_true (d:=.store target (.var cursor)
        (.get sites (.div (.var cursor) (.var columns)))) et
        (Run.store ek er hTarget)).mono (by simp [Cond.size,Expr.size])
  · have ef : (Cond.eq (.get chart (.var cursor)) (.var zero)).evalB W s=some false := by
      simpa [he,beq_iff_eq] using eg
    have ec : (Expr.var columns).evalB W s=some cols :=
      evalB_var_iff.mpr ⟨hColumns.symm,by rwa [hColumns]⟩
    have es : (Expr.get sites (.div (.var cursor) (.var columns))).evalB W s=some siteSlot :=
      evalB_get (evalB_bin (op:=.div) ek ec hRow) hSite hs
    simpa only [installSlot,he,if_false] using
      (Run.ite_false (c:=.store target (.var cursor) (.var reference)) ef
        (Run.store ek es hTarget)).mono (by simp [Cond.size,Expr.size])

#print axioms installSlot_run
end EvenTI.P17Scalar.ActiveProducer
