import EvenP14ProjectionEngine
import EvenP12CompareBankLoad
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P17Recover

open EvenTI.Contract EvenTI.P12Compare EvenTI.P14Projection EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_slots)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def shiftedWindow (first : String) (skip : ℕ) : Expr := .add (.var first) (.lit skip)

private def windowLoadBindings (first last : String) (skip : ℕ) : List (String × Expr) :=
  [(inputBase,shiftedWindow first skip),(loadLength,.sub (.var last) (shiftedWindow first skip))]

noncomputable def loadFieldWindow (D : FieldEncoding K) (F : FieldPresentation K)
    (first last : String) (skip : ℕ) : Com :=
  .seq (commands (windowLoadBindings first last skip)) (encodedBankLoad D F "data" contiguousAddress)

/-- A word proven to belong to a stored request window is physically at
the offset supplied to the field loader. -/
theorem getWord_of_slice (z : List ℕ) {a e : ℕ} (hE : e ≤ z.length)
    {words : List ℕ} (h : slice z a e=words) {k : ℕ} (hk : k < words.length) :
    (sentinelWords z)[a+k]? = some words[k] := by
  have hLen := congrArg List.length h
  rw [slice_length z hE] at hLen
  have hZ : a+k < z.length := by omega
  have hk' : k < (slice z a e).length := by rwa [h]
  have heq := congrArg (fun l : List ℕ => l[k]?) h
  simp only [List.getElem?_eq_getElem hk',List.getElem?_eq_getElem hk,Option.some.injEq] at heq
  rw [sentinelWords,List.getElem?_append_left hZ,List.getElem?_eq_getElem hZ]
  simpa only [slice,List.getElem_drop,List.getElem_take] using congrArg some heq

private theorem loadWindowSafe (first last : String) (skip : ℕ)
    (h₁ : inputBase ≠ first) (h₂ : inputBase ≠ last)
    (h₃ : loadLength ≠ first) (h₄ : loadLength ≠ last) :
    ∀ p ∈ windowLoadBindings first last skip, ∀ q ∈ windowLoadBindings first last skip, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [windowLoadBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;>
    simp [NoVar,shiftedWindow,h₁,h₂,h₃,h₄,Ne.symm h₁,Ne.symm h₂,Ne.symm h₃,Ne.symm h₄]

/-- Physically install consecutive encoded field entries from the immutable
request bank. The offset and length come from live window registers. -/
theorem loadFieldWindow_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z : List ℕ) (values : List K) (first last : String) (skip : ℕ)
    {B S a e base : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B) (hB : 1 < B)
    (hAB : a+skip ≤ e) (hE : e ≤ z.length) (hLen : z.length < B)
    (hF : s.vars first=a) (hL : s.vars last=e)
    (h₁ : inputBase ≠ first) (h₂ : inputBase ≠ last)
    (h₃ : loadLength ≠ first) (h₄ : loadLength ≠ last)
    (hBase : s.vars loadBase=base) (hFit : base+values.length ≤ S)
    (hWords : slice z (a+skip) e=values.map (fun x => (D x).val))
    (hBank : s.arrs "data"=sentinelWords z) :
    ∃ t, Run B (loadFieldWindow D F first last skip) s t
      (11+encodedBankLoadCost F contiguousAddress values.length) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k (hk : k < values.length), val F canonical qN.WS t (base+k) = values[k]) ∧
      (∀ j, j < base ∨ base+values.length ≤ j → val F canonical qN.WS t j=val F canonical qN.WS s j) ∧
      (∀ r, r ≠ inputBase → r ≠ loadLength → ¬loadChanges r → t.vars r=s.vars r) ∧
      (∀ bank, bank ≠ canonical.mem → t.arrs bank=s.arrs bank) ∧ t.inp=s.inp ∧ t.out=s.out := by
  have hN := congrArg List.length hWords
  rw [slice_length z hE,List.length_map] at hN
  have ea : (Expr.var first).evalB B s=some a := evalB_var_iff.mpr ⟨hF.symm,hF ▸ (by omega)⟩
  have ee : (Expr.var last).evalB B s=some e := evalB_var_iff.mpr ⟨hL.symm,hL ▸ (by omega)⟩
  have eStart : (shiftedWindow first skip).evalB B s=some (a+skip) :=
    evalB_bin (op:=.add) ea (evalB_lit (by omega)) (by change a+skip < B; omega)
  have eLen : (Expr.sub (.var last) (shiftedWindow first skip)).evalB B s=some values.length := by
    rw [← hN]
    exact evalB_bin (op:=.sub) ee eStart (by change e-(a+skip)<B; omega)
  let args := [(inputBase,a+skip),(loadLength,values.length)]
  let u := install args s
  have ru : Run B (commands (windowLoadBindings first last skip)) s u 11 :=
    commands_run (windowLoadBindings first last skip) [a+skip,values.length] s (by rfl)
      (.cons eStart (.cons eLen .nil)) (loadWindowSafe first last skip h₁ h₂ h₃ h₄)
  have huSlot : Slots F canonical qN.WS S B u := by
    apply installed_slots F args s hS
    intro p hp
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> simp only [Prod.fst] <;> decide
  have huBase : u.vars loadBase=base := by
    simpa [u,args,install,loadBase,inputBase,loadLength] using hBase
  have huInput : u.vars inputBase=a+skip := by simp [u,args,install,inputBase,loadLength]
  have huLen : u.vars loadLength=values.length := by simp [u,args,install]
  have hData (j : ℕ) (hj : j < values.length) :
      (u.arrs "data")[a+skip+j]? = some (D (values.getD j 0)).val := by
    change (s.arrs "data")[a+skip+j]? = some (D (values.getD j 0)).val
    rw [hBank]
    have hm : j < (values.map (fun x => (D x).val)).length := by simpa using hj
    simpa only [List.getD_eq_getElem _ _ hj,List.getElem_map] using getWord_of_slice z hE hWords hm
  obtain ⟨t,rt,hSlots,hVals,hOther,hVars,hArr,hInp,hOut⟩ :=
    contiguousBankLoad_run D F "data" (fun j => values.getD j 0) (by decide) huSlot hQ hB
      (by omega) (by omega) huBase huLen huInput hFit hData
  refine ⟨t,ru.seq rt,hSlots,?_,?_,?_,hArr,hInp,hOut⟩
  · intro j hj
    simpa only [List.getD_eq_getElem _ _ hj] using hVals j hj
  · intro j hj
    rw [hOther j hj]
    change val F canonical qN.WS ((s.setVar inputBase (a+skip)).setVar loadLength values.length) j = _
    rw [val_setVar F canonical (by decide : loadLength ≠ qN.WS),
      val_setVar F canonical (by decide : inputBase ≠ qN.WS)]
  · intro r hi hl h
    rw [hVars r h]
    simp [u,args,install,hi,hl]

#print axioms loadFieldWindow_run
end EvenTI.P17Recover
