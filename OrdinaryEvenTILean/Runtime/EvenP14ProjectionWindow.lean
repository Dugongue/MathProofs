import EvenP12ComparePrepCodecPair
import EvenP12ComparePrepSpectral
import Mathproof.Meta.Problem18P34Machine20261002Layout
import Mathproof.Meta.IMPAutoTactics20261004

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P14Projection

open EvenTI.P10Oracle EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004

def remaining : Expr := .sub (.var "end") (.var "cursor")
def inside : Cond := .lt (.var "cursor") (.var "end")
def shortBlock : Cond := .lt (.var "word") remaining

def openWindow : Com :=
  .seq (.assign "word" (.get "data" (.var "cursor")))
    (.seq advanceCursor (.seq (.assign "stop" (.var "end"))
      (.ite shortBlock (.assign "stop" (.add (.var "cursor") (.var "word"))) .skip)))

/-- Consume the length header of a nonempty window. Both resulting endpoints
are within the old window even when the recorded length exceeds the payload. -/
theorem openWindow_run (z : List Nat) {c e B : Nat} {s : Env}
    (hc : s.vars "cursor" = c) (he : s.vars "end" = e)
    (hce : c < e) (hez : e ≤ z.length) (hz : z.length < B) (hB : 1 < B)
    (hv : ∀ v ∈ z, v < B) (hd : s.arrs "data" = sentinelWords z) :
    ∃ t, Run B openWindow s t 21 ∧ t.vars "cursor" = c+1 ∧
      t.vars "stop" = c+1+min (z[c]'(hce.trans_le hez)) (e-(c+1)) ∧
      t.vars "end" = e ∧ Frame openWindow s t := by
  let a := z[c]'(hce.trans_le hez)
  let r := s.setVar "word" a
  let u := r.setVar "cursor" (c+1)
  let v := u.setVar "stop" e
  have ha : a < B := hv a (List.getElem_mem (hce.trans_le hez))
  have ea : (Expr.get "data" (.var "cursor")).evalB B s = some a := by
    apply evalB_get (evalB_var (by rw [hc]; omega)) _ ha
    rw [hd,hc,sentinelWords,List.getElem?_append_left (hce.trans_le hez),List.getElem?_eq_getElem]
  have r₁ : Run B (.assign "word" (.get "data" (.var "cursor"))) s r 3 := Run.assign ea
  have ec : (Expr.add (.var "cursor") (.lit 1)).evalB B r = some (c+1) := by
    apply evalB_bin (op := .add) (evalB_var_iff.mpr ⟨by simp [r,hc],by simp [r,hc]; omega⟩)
      (evalB_lit hB)
    change c+1<B
    omega
  have r₂ : Run B advanceCursor r u 4 := Run.assign ec
  have ee : (Expr.var "end").evalB B u = some e :=
    evalB_var_iff.mpr ⟨by simp [u,r,he],by simp [u,r,he]; omega⟩
  have r₃ : Run B (.assign "stop" (.var "end")) u v 2 := Run.assign ee
  have ew : (Expr.var "word").evalB B v = some a := evalB_var_iff.mpr
    ⟨by simp [v,u,r],by simpa [v,u,r] using ha⟩
  have ev : (Expr.var "cursor").evalB B v = some (c+1) := evalB_var_iff.mpr
    ⟨by simp [v,u],by simp [v,u]; omega⟩
  have eev : (Expr.var "end").evalB B v = some e := evalB_var_iff.mpr
    ⟨by simp [v,u,r,he],by simp [v,u,r,he]; omega⟩
  have er : remaining.evalB B v = some (e-(c+1)) := by
    apply evalB_bin (op := .sub) eev ev
    change e-(c+1)<B
    omega
  have eg : shortBlock.evalB B v = some (decide (a < e-(c+1))) := evalB_condLt ew er
  by_cases h : a < e-(c+1)
  · have ea' : (Expr.add (.var "cursor") (.var "word")).evalB B v = some (c+1+a) :=
      evalB_bin (op := .add) ev ew (by change c+1+a<B; omega)
    let t := v.setVar "stop" (c+1+a)
    have r₄ : Run B (.assign "stop" (.add (.var "cursor") (.var "word"))) v t 4 := Run.assign ea'
    have eg' : shortBlock.evalB B v = some true := by simpa [h] using eg
    have rr : Run B openWindow s t 21 := (r₁.seq (r₂.seq (r₃.seq
      (Run.ite_true (d := .skip) eg' r₄)))).mono (by decide)
    exact ⟨t,rr,by simp [t,v,u],by simp [t,Nat.min_eq_left h.le,a],
      by simp [t,v,u,r,he],Frame.of_run rr⟩
  · have eg' : shortBlock.evalB B v = some false := by simpa [h] using eg
    have rr : Run B openWindow s v 21 := (r₁.seq (r₂.seq (r₃.seq
      (Run.ite_false (c := .assign "stop" (.add (.var "cursor") (.var "word"))) eg' Run.skip)))).mono
      (by decide)
    exact ⟨v,rr,by simp [v,u],by simp [v,Nat.min_eq_right (Nat.le_of_not_gt h),a]; omega,
      by simp [v,u,r,he],Frame.of_run rr⟩

#print axioms openWindow_run
end EvenTI.P14Projection
