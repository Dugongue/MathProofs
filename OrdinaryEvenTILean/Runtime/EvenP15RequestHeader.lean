import EvenP15RequestFrame
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P10Scan EvenTI.P12CountPre EvenTI.P14Projection
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands install commands_run)

def requestOrder : String := "even.request.order"
def requestWidth : String := "even.request.width"
def requestLeftTag : String := "even.request.left.tag"
def requestRightTag : String := "even.request.right.tag"

private def requestHeaderBindings : List (String × Expr) :=
  [(requestOrder,.get "data" (.var requestRawStart)),
   (requestWidth,.get "data" (.add (.var requestRawStart) (.lit 1))),
   (requestLeftTag,.get "data" (.var "cursor")),
   (requestRightTag,.get "data" (.var "stop"))]

def requestHeaderProgram : Com := commands requestHeaderBindings

theorem requestReadSliceCell {B c e j : ℕ} {s : Env} (z w : List ℕ) (index : Expr)
    (hData : s.arrs "data"=sentinelWords z) (he : e ≤ z.length)
    (hW : ∀ v ∈ z, v < B) (hSlice : slice z c e=w) (hj : j < w.length)
    (hIdx : index.evalB B s=some (c+j)) :
    (Expr.get "data" index).evalB B s=some w[j] := by
  have hs := congrArg List.length hSlice
  simp only [slice,List.length_drop,List.length_take,min_eq_left he] at hs
  have hc : c+j < z.length := by omega
  have hk : j < (slice z c e).length := by rwa [hSlice]
  have heq : z[c+j]'hc = w[j] := by
    have hr := congrArg (fun l : List ℕ => l[j]?) hSlice
    simp only [List.getElem?_eq_getElem hk,List.getElem?_eq_getElem hj,Option.some.injEq] at hr
    simpa only [slice,List.getElem_drop,List.getElem_take] using hr
  refine evalB_get hIdx ?_ (heq ▸ hW _ (List.getElem_mem hc))
  rw [hData,sentinelWords,List.getElem?_append_left hc,List.getElem?_eq_getElem hc,heq]

/-- Read the order, width, and both trial tags in the state carrying the
original and paired trial word windows. -/
theorem requestHeaderProgram_run {B : ℕ} {s : Env} {d n p q : ℕ} (raw left right : List ℕ)
    (h : LoadedRequest (d::n::raw) (p::left) (q::right) s) (hB : 1 < B)
    (hLen : (pairW (d::n::raw) (pairW (p::left) (q::right))).length < B)
    (hWords : ∀ a ∈ pairW (d::n::raw) (pairW (p::left) (q::right)), a < B) :
    ∃ t, Run B requestHeaderProgram s t 15 ∧
      LoadedRequest (d::n::raw) (p::left) (q::right) t ∧
      t.vars requestOrder=d ∧ t.vars requestWidth=n ∧
      t.vars requestLeftTag=p ∧ t.vars requestRightTag=q ∧ t.inp=s.inp ∧ t.out=s.out := by
  let z := pairW (d::n::raw) (pairW (p::left) (q::right))
  obtain ⟨h₁,h₂,h₃,h₄,he⟩ := h.ordered
  have hZ : z.length < B := hLen
  have hEnd : s.vars "end"=z.length := he
  have ha : s.vars requestRawStart+1 < s.vars requestRawEnd := by
    have hL := congrArg List.length h.raw
    have hE : s.vars requestRawEnd ≤ z.length := by omega
    change (slice z (s.vars requestRawStart) (s.vars requestRawEnd)).length = (d::n::raw).length at hL
    simp only [slice,List.length_drop,List.length_take,min_eq_left hE,List.length_cons] at hL
    omega
  have eStart : (Expr.var requestRawStart).evalB B s=some (s.vars requestRawStart) := evalB_var (by omega)
  have eWidth : (Expr.add (.var requestRawStart) (.lit 1)).evalB B s=some (s.vars requestRawStart+1) :=
    evalB_bin (op:=.add) eStart (evalB_lit hB) (by change s.vars requestRawStart+1 < B; omega)
  have eOrder := requestReadSliceCell z (d::n::raw) (.var requestRawStart) h.stored
    (by omega : s.vars requestRawEnd ≤ z.length) hWords h.raw (j:=0) (by simp) (by simpa using eStart)
  have eWidth' := requestReadSliceCell z (d::n::raw) (.add (.var requestRawStart) (.lit 1)) h.stored
    (by omega : s.vars requestRawEnd ≤ z.length) hWords h.raw (j:=1) (by simp) eWidth
  have eLeft := requestReadSliceCell z (p::left) (.var "cursor") h.stored
    (by omega : s.vars "stop" ≤ z.length) hWords h.leftTrial (j:=0) (by simp)
    (by simpa using (evalB_var (σ:=s) (x:="cursor") (by omega : s.vars "cursor" < B)))
  have eRight := requestReadSliceCell z (q::right) (.var "stop") h.stored hEnd.le hWords h.rightTrial (j:=0) (by simp)
    (by simpa using (evalB_var (σ:=s) (x:="stop") (by omega : s.vars "stop" < B)))
  have hh : List.Forall₂ (fun v k => v.2.evalB B s=some k) requestHeaderBindings [d,n,p,q] :=
    .cons eOrder (.cons eWidth' (.cons eLeft (.cons eRight .nil)))
  let t := install [(requestOrder,d),(requestWidth,n),(requestLeftTag,p),(requestRightTag,q)] s
  have run : Run B requestHeaderProgram s t 15 := commands_run requestHeaderBindings [d,n,p,q] s
    (by rfl) hh (by simp [requestHeaderBindings,NoVar,requestOrder,requestWidth,requestLeftTag,requestRightTag,requestRawStart])
  refine ⟨t,run,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨h.stored,?_,?_,?_,?_⟩
    all_goals
      first
      | simpa [t,install,requestOrder,requestWidth,requestLeftTag,requestRightTag,
          requestRawStart,requestRawEnd] using h.raw
      | simpa [t,install,requestOrder,requestWidth,requestLeftTag,requestRightTag,
          requestRawStart,requestRawEnd] using h.leftTrial
      | simpa [t,install,requestOrder,requestWidth,requestLeftTag,requestRightTag,
          requestRawStart,requestRawEnd] using h.rightTrial
      | simpa [t,install,requestOrder,requestWidth,requestLeftTag,requestRightTag,
          requestRawStart,requestRawEnd] using h.ordered
  all_goals simp [t,install,requestOrder,requestWidth,requestLeftTag,requestRightTag]

#print axioms requestHeaderProgram_run
end EvenTI.P15Execution