import EvenP12ComparePrepShape
import EvenP12CompareLeftKernel
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands install commands_run installed_arrays installed_scalar)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs KBLay kAM kOUT)
open Mathproof.P15RecogIMPDot20261007 (dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
set_option autoImplicit false

/-- Static positive arithmetic expressions evaluated at the live cut side.
Positivity bounds every arithmetic subexpression by the final result. -/
inductive Address where
  | side
  | litSucc (k : Nat)
  | add (a b : Address)
  | mul (a b : Address)

def Address.value (m : Nat) : Address → Nat
  | .side => m
  | .litSucc k => k+1
  | .add a b => a.value m + b.value m
  | .mul a b => a.value m * b.value m

def Address.expr : Address → Expr
  | .side => .var shapePower.out
  | .litSucc k => .lit (k+1)
  | .add a b => .add a.expr b.expr
  | .mul a b => .mul a.expr b.expr

theorem Address.positive {m : Nat} (hm : 0 < m) (a : Address) : 0 < a.value m := by
  induction a <;> simp [Address.value, *] <;> positivity

theorem Address.eval {B m : Nat} {σ : Env} (hm : σ.vars shapePower.out = m) (hpos : 0 < m)
    (a : Address) (ha : a.value m < B) :
    a.expr.evalB B σ = some (a.value m) := by
  induction a with
  | side => exact (evalB_var_iff.mpr ⟨hm.symm,hm ▸ ha⟩)
  | litSucc k => exact evalB_lit ha
  | add a b ihA ihB =>
    change a.value m + b.value m < B at ha
    exact evalB_bin (ihA (by omega)) (ihB (by omega)) ha
  | mul a b ihA ihB =>
    have h₁ := Nat.le_mul_of_pos_right (a.value m) (Address.positive hpos b)
    have h₂ := Nat.le_mul_of_pos_left (b.value m) (Address.positive hpos a)
    exact evalB_bin (ihA (h₁.trans_lt ha)) (ihB (h₂.trans_lt ha)) ha

theorem Address.noVar (a : Address) {r : String} (h : r ≠ shapePower.out) : NoVar r a.expr := by
  induction a <;> simp [Address.expr,NoVar, *, Ne.symm h]

def cutArea : Address := .mul .side .side

def rowKernelWidth : Address := .add (.add (.add .side .side) .side) (.litSucc 0)

def rowKernelBlock : Address := .add (.litSucc 4) (.add rowKernelWidth (.mul .side rowKernelWidth))

def rawMatrixBase : Address := .mul (.add .side (.litSucc 0)) rowKernelBlock

def augmentedMatrixBase : Address := .add rawMatrixBase cutArea

def firstOutputBase : Address := .add augmentedMatrixBase (.mul (.litSucc 1) cutArea)

def outputBase (i : Fin 4) : Address :=
  if i.val = 0 then firstOutputBase else .add firstOutputBase (.mul (.litSucc (i.val-1)) cutArea)

def constantsBase : Address := .add firstOutputBase (.mul (.litSucc 3) cutArea)

def pairCutSlotCount : Address := .add constantsBase (.litSucc 3)

def inputOffset (target : Bool) : Address :=
  if target then .add (.litSucc 1) cutArea else .litSucc 1

theorem rowKernelBlock_value (m : Nat) : rowKernelBlock.value m = XBs m m := by
  simp only [rowKernelBlock,rowKernelWidth,Address.value,Mathproof.Problem18IMPIntertwinerScan20261001.blockSize,
    Mathproof.Problem18ClaudeIMPPivot20261001.rowStart]
  ring

theorem cutArea_value (m : Nat) : cutArea.value m = m*m := rfl

theorem outputBase_value (m : Nat) (i : Fin 4) :
    (outputBase i).value m = firstOutputBase.value m + i.val*(m*m) := by
  by_cases h : i.val = 0
  · simp [outputBase,h]
  · have h' : i.val-1+1 = i.val := by omega
    simp only [outputBase,if_neg h,Address.value,cutArea_value,h']

theorem concreteKernelLayout (m : Nat) (i : Fin 4) {B : Nat} (hm : 0 < m)
    (hB : pairCutSlotCount.value m + m + m + 10 < B) :
    KBLay m m (augmentedMatrixBase.value m) ((outputBase i).value m) (constantsBase.value m)
      (pairCutSlotCount.value m) B := by
  have hh : i.val*m*m + m*m ≤ 4*(m*m) := by
    rw [Nat.mul_assoc]
    have h := Nat.mul_le_mul_right (m*m) i.isLt
    rw [Nat.succ_mul] at h
    omega
  refine ⟨hm,?_,?_,?_,?_,hB⟩
  · simp only [augmentedMatrixBase,rawMatrixBase,Address.value,cutArea_value,rowKernelBlock_value,Nat.zero_add]
    omega
  · rw [outputBase_value]
    simp only [firstOutputBase,Address.value,cutArea_value]
    ring_nf
    omega
  · rw [outputBase_value]
    simp only [constantsBase,Address.value,cutArea_value]
    rw [Nat.mul_assoc] at hh
    omega
  · simp [pairCutSlotCount,Address.value]

def kernelBindings (target : Bool) (i : Fin 4) : List (String × Address) :=
  [(tNR,.side),(tD,.side),(originalRows,.side),(originalColumns,.side),
    (loadBase,rawMatrixBase),(tRB,rawMatrixBase),(loadLength,cutArea),
    (kAM,augmentedMatrixBase),(kOUT,outputBase i),(inputBase,inputOffset target),
    (dZ,constantsBase),(rOs,.add constantsBase (.litSucc 0)),
    (dT,.add constantsBase (.litSucc 1)),(dU,.add constantsBase (.litSucc 2))]

def kernelAssignment (target : Bool) (i : Fin 4) : Com :=
  commands ((kernelBindings target i).map fun p => (p.1,p.2.expr))

def kernelState (target : Bool) (i : Fin 4) (m : Nat) (σ : Env) : Env :=
  install ((kernelBindings target i).map fun p => (p.1,p.2.value m)) σ

private theorem zip_map_pairs {A B C : Type} (xs : List (A × B)) (f : B → C) :
    List.zip (xs.map Prod.fst) (xs.map fun p => f p.2) = xs.map (fun p => (p.1,f p.2)) := by
  induction xs with
  | nil => rfl
  | cons h hs ih => cases h; simp [ih]

theorem kernelAssignment_run (target : Bool) (i : Fin 4) (m : Nat)
    {B : Nat} {σ : Env} (hm : σ.vars shapePower.out = m) (hPos : 0 < m)
    (hFits : ∀ v ∈ kernelBindings target i, v.2.value m < B) :
    Run B (kernelAssignment target i) σ (kernelState target i m σ)
      ((((kernelBindings target i).map fun v => v.2.expr.size+1).sum)+1) := by
  let xs := kernelBindings target i
  let es := xs.map fun p => (p.1,p.2.expr)
  let vs := xs.map fun p => p.2.value m
  have aux (ys : List (String × Address)) (hFits : ∀ v ∈ ys, v.2.value m < B) :
      List.Forall₂ (fun (p : String × Expr) v => p.2.evalB B σ = some v)
        (ys.map fun p => (p.1,p.2.expr)) (ys.map fun p => p.2.value m) := by
    induction ys with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (Address.eval hm hPos a.2 (hFits a List.mem_cons_self))
        (ih fun p hp => hFits p (List.mem_cons_of_mem a hp))
  have hv : List.Forall₂ (fun p v => p.2.evalB B σ = some v) es vs := aux xs hFits
  have hn (v : String × Address) (h : v ∈ kernelBindings target i) : v.1 ≠ shapePower.out := by
    simp only [kernelBindings,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> simp only [Prod.fst] <;> decide
  have hh : ∀ p ∈ es, ∀ r ∈ es, NoVar p.1 r.2 := by
    intro p hp r hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact Address.noVar u.2 (hn v hv)
  have hRun := commands_run es vs σ (by simp [es,vs]) hv hh
  change Run B (commands es) σ (kernelState target i m σ) _
  have he : List.zip (es.map Prod.fst) vs = (kernelBindings target i).map (fun p => (p.1,p.2.value m)) := by
    simpa [es,vs,xs,List.map_map,Function.comp_def] using
      zip_map_pairs (kernelBindings target i) (fun a : Address => a.value m)
  rw [he] at hRun
  simpa [kernelState,es,xs,List.map_map,Function.comp_def] using hRun

#print axioms concreteKernelLayout
#print axioms kernelAssignment_run
end EvenTI.P12ComparePrep
