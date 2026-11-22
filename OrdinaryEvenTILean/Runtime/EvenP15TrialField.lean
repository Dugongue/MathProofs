import EvenP12CompareDigitLoad

set_option autoImplicit false
set_option maxHeartbeats 1450000

namespace EvenTI.P15Trial

open EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice decode_coordinates decode_injective)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def labelAddress : String := "even_trial_field_address"

def fieldTest (p : ℕ × ℕ) : Cond :=
  .eq (.get canonical.mem (.add (.var labelAddress) (.lit p.1))) (.lit p.2)

def digitBranch (tests : List (ℕ × ℕ)) (yes no : Com) : Com :=
  match tests with
  | [] => yes
  | p::rest => .ite (fieldTest p) (digitBranch rest yes no) no

private theorem digitBranch_run {B Y N : ℕ} {σ τ υ : Env}
    (tests : List (ℕ×ℕ)) (ok : (ℕ×ℕ) → Bool) {yes no : Com}
    (ht : ∀ p ∈ tests, (fieldTest p).evalB B σ=some (ok p))
    (hy : tests.all ok=true → Run B yes σ τ Y)
    (hn : tests.all ok=false → Run B no σ υ N) :
    Run B (digitBranch tests yes no) σ (if tests.all ok then τ else υ)
      (7*tests.length+max Y N) := by
  induction tests with
  | nil =>
    exact (hy rfl).mono (by simp)
  | cons p ts ih =>
    cases hp : ok p with
    | false =>
      have hAll : (p::ts).all ok=false := by simp [hp]
      have he := (ht p List.mem_cons_self).trans (congrArg some hp)
      rw [hAll]
      exact (Run.ite_false (c := digitBranch ts yes no) he (hn hAll)).mono
        (by change 7+N≤7*(ts.length+1)+max Y N; omega)
    | true =>
      have hAll : (p::ts).all ok=ts.all ok := by simp [hp]
      have he := (ht p List.mem_cons_self).trans (congrArg some hp)
      rw [hAll]
      have r := ih (fun q hq => ht q (List.mem_cons_of_mem _ hq))
        (fun h => hy (hAll.trans h)) (fun h => hn (hAll.trans h))
      exact (Run.ite_true (d := no) he r).mono
        (by change 7+(7*ts.length+max Y N) ≤ 7*(ts.length+1)+max Y N; omega)

def coordinateTests (F : FieldPresentation K) (x : K) : List (ℕ×ℕ) :=
  (List.finRange F.e).map fun i => (i.val,(F.coordinate x i).val)

noncomputable def fieldLabelBranches (D : FieldEncoding K) (F : FieldPresentation K) : List K → Com
  | [] => .skip
  | x::xs => digitBranch (coordinateTests F x) (.write (.lit (D x).val)) (fieldLabelBranches D F xs)

noncomputable def emitFieldLabel (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  fieldLabelBranches D F ((List.finRange (Fintype.card K)).map D.symm)

def emitFieldLabelCost (F : FieldPresentation K) : ℕ := 7*F.e*Fintype.card K+2

private theorem labelCoordinatePass (F : FieldPresentation K) {B S s : ℕ} {σ : Env}
    (hS : Slots F canonical qN.WS S B σ) (hs : s < S) {x : K} :
    let u := σ.vars qN.WS+s*F.e
    let agree := fun p : ℕ×ℕ => decide ((σ.arrs canonical.mem).getD (u+p.1) 0=p.2)
    (coordinateTests F x).all agree = true ↔ val F canonical qN.WS σ s=x := by
  let u := σ.vars qN.WS+s*F.e
  have hCan := hS.canon s hs
  have hl : (coordinateTests F x).all
      (fun p => decide ((σ.arrs canonical.mem).getD (u+p.1) 0=p.2)) = true ↔
      slice F σ canonical u = (fun i : Fin F.e => (F.coordinate x i).val) := by
    constructor
    · intro h
      funext i
      apply of_decide_eq_true
      exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩)
    · intro h
      apply List.all_eq_true.mpr
      intro p hp
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
      exact decide_eq_true (congrFun h i)
  refine hl.trans ?_
  change _ ↔ Mathproof.Problem18IMPFieldPresentation20261001.decode F (slice F σ canonical u)=x
  exact (decode_injective F hCan (fun i => (F.coordinate x i).isLt)).symm.trans
    (by rw [decode_coordinates])
/-- A single field coordinate takes its bytes from the physical canonical
memory, then converts by the fixed public label table. The program works for
all field presentations and leaves all field registers and banks unchanged. -/
theorem emitFieldLabel_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S s : ℕ} {σ : Env} (hS : Slots F canonical qN.WS S B σ)
    (hs : s < S) (hB : Fintype.card K≤B) (hP : F.p < B)
    (hBase : σ.vars labelAddress=σ.vars qN.WS+s*F.e) :
    Run B (emitFieldLabel D F) σ
      {σ with out := σ.out++[(D (val F canonical qN.WS σ s)).val]}
      (emitFieldLabelCost F) := by
  let x := val F canonical qN.WS σ s
  let u := σ.vars qN.WS+s*F.e
  let τ := {σ with out := σ.out++[(D x).val]}
  let agree := fun p : ℕ×ℕ => decide ((σ.arrs canonical.mem).getD (u+p.1) 0=p.2)
  have ht (y : K) (p : ℕ×ℕ) (hp : p ∈ coordinateTests F y) :
      (fieldTest p).evalB B σ=some (agree p) := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    let j := i.val
    have hj := i.isLt
    have hN : u+j < (σ.arrs canonical.mem).length := by
      have hp := Nat.mul_le_mul_right F.e (by omega : s+1≤S)
      rw [Nat.succ_mul] at hp
      have hh := hS.fit
      dsimp [u,j]
      omega
    have hB' := hN.trans hS.base.memory_word
    have hD (v : ℕ) (hv : v < (σ.arrs canonical.mem).length) :
        (σ.arrs canonical.mem)[v]? = some ((σ.arrs canonical.mem).getD v 0) := by
      simp [List.getElem?_eq_getElem hv,List.getD_eq_getElem?_getD]
    have hRead : (σ.arrs canonical.mem).getD (u+j) 0 < B :=
      (hS.canon s hs i).trans hP
    have hLoad : (Expr.get canonical.mem (.add (.var labelAddress) (.lit j))).evalB B σ =
        some ((σ.arrs canonical.mem).getD (u+j) 0) := by
      apply evalB_get _ (hD _ hN) hRead
      exact evalB_bin (op := .add)
        (evalB_var_iff.mpr ⟨hBase.symm,hBase ▸ (by omega : u < B)⟩)
        (evalB_lit (by omega : j < B)) hB'
    have he := evalB_condEq hLoad (evalB_lit (((F.coordinate y i).isLt).trans hP))
    let m := (σ.arrs canonical.mem).getD (u+j) 0
    let n := (F.coordinate y i).val
    have hEq : (m == n)=decide (m=n) := by
      by_cases h : m=n <;> simp [h]
    rw [show ((σ.arrs canonical.mem).getD (u+j) 0 == (F.coordinate y i).val) =
      decide ((σ.arrs canonical.mem).getD (u+j) 0 = (F.coordinate y i).val) from hEq] at he
    exact he
  have hMatch (y : K) : (coordinateTests F y).all agree = true ↔ x=y :=
    labelCoordinatePass F hS hs
  have hr (ys : List K) (hm : x ∈ ys) :
      Run B (fieldLabelBranches D F ys) σ τ (7*F.e*ys.length+2) := by
    induction ys with
    | nil => simp at hm
    | cons y ys ih =>
      by_cases hxy : x=y
      · have ha := (hMatch y).mpr hxy
        have rr : Run B (.write (.lit (D y).val)) σ τ 2 := by
          subst y
          exact Run.write (evalB_lit ((D x).isLt.trans_le hB))
        have rs := digitBranch_run (coordinateTests F y) agree (no := fieldLabelBranches D F ys)
          (N := 0) (υ := σ) (ht y) (fun _ => rr) (fun bad => by rw [ha] at bad; contradiction)
        have hL : (coordinateTests F y).length=F.e := by simp [coordinateTests]
        simp only [ha,hL] at rs
        exact rs.mono (by simp [Nat.mul_add] <;> omega)
      · have ha : (coordinateTests F y).all agree = false :=
          Bool.eq_false_iff.mpr (fun hh => hxy ((hMatch y).mp hh))
        have hTail := (List.mem_cons.mp hm).resolve_left hxy
        have rs := digitBranch_run (coordinateTests F y) agree (yes := .write (.lit (D y).val))
          (Y := 2) (τ := σ) (ht y) (fun bad => by rw [ha] at bad; contradiction) (fun _ => ih hTail)
        have hL : (coordinateTests F y).length=F.e := by simp [coordinateTests]
        simp only [ha,hL,Bool.false_eq_true,if_false] at rs
        exact rs.mono (by simp [Nat.max_eq_right (show 2≤7*F.e*ys.length+2 by omega),Nat.mul_add]; omega)
  have hmem : x ∈ (List.finRange (Fintype.card K)).map D.symm :=
    List.mem_map.mpr ⟨D x,List.mem_finRange _,D.symm_apply_apply x⟩
  simpa [emitFieldLabel,emitFieldLabelCost,τ,x] using hr _ hmem

#print axioms emitFieldLabel_run
end EvenTI.P15Trial
