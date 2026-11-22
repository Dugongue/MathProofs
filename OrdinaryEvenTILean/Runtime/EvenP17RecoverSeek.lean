import EvenP17RecoverWindows
import EvenP15TrialTraverse

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace EvenTI.P17Recover

open EvenTI.P15Trial EvenTI.P14Projection EvenTI.P10Scan EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands commands_run install)

def anchorWanted : String := "even.recover.anchor.want"
def anchorRemaining : String := "even.recover.anchor.remaining"

def anchorAxis : TrialAxis :=
  ⟨"even.recover.anchor.scan","even.recover.anchor.limit","even.recover.anchor.begin","even.recover.anchor.end"⟩

private theorem anchorAxisValid : anchorAxis.Valid := by decide

private def seekGuard : Cond := .lt (.lit 0) (.var anchorRemaining)
private def seekBody : Com :=
  .seq anchorAxis.openBlock <|
    .seq (.assign anchorAxis.scan (.var anchorAxis.stop))
      (.assign anchorRemaining (.sub (.var anchorRemaining) (.lit 1)))
private def seekLoop : Com := .while seekGuard seekBody

private def seekBindings (right : Bool) : List (String × Expr) :=
  [(anchorAxis.scan,.add (.var (anchorListStart right)) (.lit 1)),
   (anchorAxis.limit,.var (formStart right)),(anchorRemaining,.var anchorWanted)]

def selectAnchor (right : Bool) : Com :=
  .seq (commands (seekBindings right)) (.seq seekLoop anchorAxis.openBlock)

private theorem live {B v : ℕ} {s : Env} {r : String} (h : s.vars r=v) (hb : v < B) :
    (Expr.var r).evalB B s=some v := evalB_var_iff.mpr ⟨h.symm,h ▸ hb⟩

private theorem selectorSafe (right : Bool) :
    ∀ p ∈ seekBindings right, ∀ q ∈ seekBindings right, NoVar p.1 q.2 := by
  cases right <;> intro p hp q hq <;>
    simp only [seekBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq <;>
    rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;>
    simp [NoVar,anchorAxis,anchorListStart,formStart,anchorRemaining,anchorWanted]

private theorem seekLoop_run (z : List ℕ) (rows : List (List ℕ)) {B c e i : ℕ} {s : Env}
    (hScan : s.vars anchorAxis.scan=c) (hCount : s.vars anchorRemaining=i)
    (hi : i < rows.length) (hiB : i < B) (hc : c ≤ e) (he : e ≤ z.length)
    (hLen : z.length < B) (hB : 1 < B) (hData : s.arrs "data"=sentinelWords z)
    (hRows : slice z c e=rows.flatMap blockW) :
    ∃ t p, Run B seekLoop s t (19*i+4) ∧ t.vars anchorAxis.scan=p ∧ p≤e ∧
      t.arrs "data"=sentinelWords z ∧ slice z p e=(rows.drop i).flatMap blockW := by
  induction rows generalizing i c s with
  | nil => simp at hi
  | cons a rows ih =>
    cases i with
    | zero =>
      have hg := evalB_condLt (e:=.lit 0) (f:=.var anchorRemaining)
        (evalB_lit (σ:=s) (n:=0) (by omega)) (live hCount hiB)
      exact ⟨s,c,Run.while_false (by simpa [seekGuard] using hg),hScan,hc,hData,by simpa using hRows⟩
    | succ j =>
      obtain ⟨u,r₀,hWin,hEnd,_,hTail,hArr,_,_,hFrame⟩ :=
        openTrialBlock_run z anchorAxis anchorAxisValid a rows hScan he hc hLen hB hData hRows
      let q := c+1+a.length
      let v := u.setVar anchorAxis.scan q
      let w := v.setVar anchorRemaining j
      have hqB : q < B := hEnd.trans_lt (he.trans_lt hLen)
      have r₁ : Run B (.assign anchorAxis.scan (.var anchorAxis.stop)) u v 2 :=
        Run.assign (live hWin.stop hqB)
      have hRem' : v.vars anchorRemaining=j+1 := by
        have hOld := (hFrame anchorRemaining (by decide) (by decide)).trans hCount
        simpa [v,anchorAxis,anchorRemaining] using hOld
      have eRem : (Expr.sub (.var anchorRemaining) (.lit 1)).evalB B v=some j := by
        have h := evalB_bin (op:=.sub) (live hRem' hiB) (evalB_lit hB)
          (by simp [Bop.apply]; omega)
        simpa using h
      have r₂ : Run B (.assign anchorRemaining (.sub (.var anchorRemaining) (.lit 1))) v w 4 :=
        Run.assign eRem
      have hScan' : w.vars anchorAxis.scan=q := by simp [w,v,anchorAxis,anchorRemaining]
      have hCount' : w.vars anchorRemaining=j := by simp [w]
      have hData' : w.arrs "data"=sentinelWords z := (congrFun hArr "data").trans hData
      have hj : j < rows.length := by simpa using hi
      obtain ⟨t,p,rt,ht,hpe,hBank,hDone⟩ :=
        ih hScan' hCount' hj (by omega) hEnd hData' hTail
      have hg := evalB_condLt (e:=.lit 0) (f:=.var anchorRemaining)
        (evalB_lit (σ:=s) (n:=0) (by omega)) (live hCount hiB)
      have hTrue : seekGuard.evalB B s=some true := by simpa [seekGuard] using hg
      have rBody : Run B seekBody s w (9+(2+4)) := r₀.seq (r₁.seq r₂)
      obtain ⟨kb,hkb,hBody⟩ := rBody
      obtain ⟨kt,hkt,hLoop⟩ := rt
      have rr : Run B seekLoop s t (19*(j+1)+4) := by
        refine ⟨4+kb+kt,?_,BigStepB.while_true hTrue hBody hLoop⟩
        omega
      exact ⟨t,p,rr,ht,hpe,hBank,by simpa using hDone⟩

/-- Locate any numbered anchor in its existing serialized trial, paying for
each skipped length prefix and preserving the original word bank. -/
theorem selectAnchor_run (z forms : List ℕ) (right : Bool) (rows : List (List ℕ))
    {B i : ℕ} {s : Env} (hSec : OperandSections z right (listW rows) forms s)
    (hi : i < rows.length) (hiB : i < B) (hI : s.vars anchorWanted=i)
    (hLen : z.length < B) (hB : 1 < B) (hData : s.arrs "data"=sentinelWords z) :
    ∃ t p q, Run B (selectAnchor right) s t (19*i+22) ∧
      TrialWindow z t anchorAxis.start anchorAxis.stop p q ∧ slice z p q=rows[i] ∧
      Frame (selectAnchor right) s t := by
  let a := s.vars (anchorListStart right)
  let e := s.vars (formStart right)
  have hAE : a ≤ e := hSec.ordered.1
  have he : e ≤ z.length := hSec.ordered.2.1.trans hSec.ordered.2.2
  have hh := congrArg List.length hSec.anchors
  change (slice z a e).length=(listW rows).length at hh
  rw [slice_length z he,listW,List.length_cons] at hh
  have hLT : a < e := by omega
  have hSlice := hSec.anchors
  change slice z a e=listW rows at hSlice
  rw [slice_cons z hLT he,listW] at hSlice
  have hPayload : slice z (a+1) e=rows.flatMap blockW := (List.cons.inj hSlice).2
  let u := install [(anchorAxis.scan,a+1),(anchorAxis.limit,e),(anchorRemaining,i)] s
  have ha : (Expr.var (anchorListStart right)).evalB B s=some a := live rfl ((hAE.trans he).trans_lt hLen)
  have ha1 := evalB_bin (op:=.add) ha (evalB_lit hB) (show a+1 < B by omega)
  have hu : Run B (commands (seekBindings right)) s u 9 :=
    commands_run (seekBindings right) [a+1,e,i] s (by cases right <;> rfl)
      (.cons ha1 (.cons (live rfl (he.trans_lt hLen)) (.cons (live hI hiB) .nil)))
      (selectorSafe right)
  obtain ⟨v,p,rv,hP,hpe,hBank,hSuffix⟩ :=
    seekLoop_run z rows (s:=u) (by simp [u,install,anchorAxis,anchorRemaining])
      (by simp [u,install,anchorAxis,anchorRemaining]) hi hiB (by omega) he hLen hB hData hPayload
  rw [List.drop_eq_getElem_cons hi] at hSuffix
  obtain ⟨t,rt,hWindow,_,hs,_,_,_,_,_⟩ :=
    openTrialBlock_run z anchorAxis anchorAxisValid rows[i] (rows.drop (i+1)) hP he hpe hLen hB hBank hSuffix
  have hr : Run B (selectAnchor right) s t (19*i+22) := (hu.seq (rv.seq rt)).mono (by omega)
  exact ⟨t,_,_,hr,hWindow,hs,Frame.of_run hr⟩

#print axioms selectAnchor_run
end EvenTI.P17Recover
