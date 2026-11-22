import EvenP15TrialField
import EvenP15ScalarMatrix

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace EvenTI.P15Scalar

open EvenTI.Contract EvenTI.P15Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice decode_coordinates decode_injective)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def scalarLabelDest : String := "even.scalar.label.dst"

private noncomputable def scalarLabelBranches (D : FieldEncoding K) (F : FieldPresentation K) : List K → Com
  | [] => .skip
  | x::xs => digitBranch (coordinateTests F x)
      (.store "data" (.var scalarLabelDest) (.lit (D x).val))
      (scalarLabelBranches D F xs)

noncomputable def installScalarLabel (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  scalarLabelBranches D F ((List.finRange (Fintype.card K)).map D.symm)

def installScalarLabelCost (F : FieldPresentation K) : ℕ := 7*F.e*Fintype.card K+3

local macro "scalarDigitBranchRun" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP15TrialField `EvenTI.P15Trial.digitBranch_run))
private theorem scalarLabelCoordinatePass (F : FieldPresentation K) {B S s : ℕ} {ws : String} {σ : Env}
    (hS : Slots F canonical ws S B σ) (hs : s < S) {x : K} :
    let u := σ.vars ws+s*F.e
    let agree := fun p : ℕ×ℕ => decide ((σ.arrs canonical.mem).getD (u+p.1) 0=p.2)
    (coordinateTests F x).all agree = true ↔ val F canonical ws σ s=x := by
  let u := σ.vars ws+s*F.e
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
/-- Copy one canonical field slot directly into the live scalar-scanning
bank without serializing through the bit-machine input or output tapes. -/
theorem installScalarLabel_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S s : ℕ} {ws : String} {σ : Env} (hS : Slots F canonical ws S B σ)
    (hs : s < S) (hB : Fintype.card K≤B) (hP : F.p < B)
    (hBase : σ.vars labelAddress=σ.vars ws+s*F.e)
    (hBank : (σ.arrs "data").length < B) (hDest : σ.vars scalarLabelDest < (σ.arrs "data").length) :
    Run B (installScalarLabel D F) σ
      (σ.setArr "data" (σ.vars scalarLabelDest) (D (val F canonical ws σ s)).val)
      (installScalarLabelCost F) := by
  let x := val F canonical ws σ s
  let u := σ.vars ws+s*F.e
  let τ := σ.setArr "data" (σ.vars scalarLabelDest) (D x).val
  have eDest : (Expr.var scalarLabelDest).evalB B σ = some (σ.vars scalarLabelDest) :=
    evalB_var (hDest.trans hBank)
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
    scalarLabelCoordinatePass F hS hs
  have hr (ys : List K) (hm : x ∈ ys) :
      Run B (scalarLabelBranches D F ys) σ τ (7*F.e*ys.length+3) := by
    induction ys with
    | nil => simp at hm
    | cons y ys ih =>
      by_cases hxy : x=y
      · have ha := (hMatch y).mpr hxy
        have rr : Run B (.store "data" (.var scalarLabelDest) (.lit (D y).val)) σ τ 3 := by
          subst y
          exact Run.store eDest (evalB_lit ((D x).isLt.trans_le hB)) hDest
        have noCase (bad : (coordinateTests F y).all agree = false) :
            Run B (scalarLabelBranches D F ys) σ σ 0 := by
          rw [ha] at bad
          contradiction
        have rs := scalarDigitBranchRun (coordinateTests F y) agree (ht y) (fun _ => rr) noCase
        have hL : (coordinateTests F y).length=F.e := by simp [coordinateTests]
        simp only [ha,hL] at rs
        exact rs.mono (by simp [Nat.mul_add] <;> omega)
      · have ha : (coordinateTests F y).all agree = false :=
          Bool.eq_false_iff.mpr (fun hh => hxy ((hMatch y).mp hh))
        have hTail := (List.mem_cons.mp hm).resolve_left hxy
        have yesCase (bad : (coordinateTests F y).all agree = true) :
            Run B (.store "data" (.var scalarLabelDest) (.lit (D y).val)) σ σ 3 := by
          rw [ha] at bad
          contradiction
        have rs := scalarDigitBranchRun (coordinateTests F y) agree (ht y) yesCase (fun _ => ih hTail)
        have hL : (coordinateTests F y).length=F.e := by simp [coordinateTests]
        simp only [ha,hL,Bool.false_eq_true,if_false] at rs
        exact rs.mono (by simp [Nat.max_eq_right (show 3≤7*F.e*ys.length+3 by omega),Nat.mul_add]; omega)
  have hmem : x ∈ (List.finRange (Fintype.card K)).map D.symm :=
    List.mem_map.mpr ⟨D x,List.mem_finRange _,D.symm_apply_apply x⟩
  simpa [installScalarLabel,installScalarLabelCost,τ,x] using hr _ hmem

#print axioms installScalarLabel_run
end EvenTI.P15Scalar