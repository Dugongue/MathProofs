import EvenP15ReciprocalPower
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18PairBoundaryMatrixPower20261004
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar Slots)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_slots installed_valid installed_arrays)

/-- One live matrix followed by four square banks and three field scratch slots. -/
def inverseLayout (n input start : ℕ) : Layout :=
  ⟨n,input,start,start+1*(n*n),start+2*(n*n),start+3*(n*n),start+4*(n*n)⟩

theorem inverseLayout_ok {n input start S : ℕ} (hn : 0 < n)
    (hApart : input+n*n ≤ start) (hFit : start+4*(n*n)+3 ≤ S) : (inverseLayout n input start).Ok S := by
  refine ⟨hn,?_,?_,?_,?_,hFit,?_,.inl ?_,.inl ?_,.inl ?_,.inl ?_,.inl ?_⟩ <;>
    simp only [inverseLayout] <;> omega

def inverseSizeWord : String := "even.inverse.frame.side"
def inverseInputWord : String := "even.inverse.frame.input"
def inverseOutputWord : String := "even.inverse.frame.output"
private def sizeExpr : Expr := .var inverseSizeWord
private def nnExpr : Expr := .mul sizeExpr sizeExpr
private def layoutOffset (k : ℕ) : Expr := .add (.var inverseOutputWord) (.mul (.lit k) nnExpr)
private def inverseBindings : List (String × Expr) :=
  [(nReg,sizeExpr),(nnReg,nnExpr),(n1Reg,.add sizeExpr (.lit 1)),
    (inR,.var inverseInputWord),(accR,.var inverseOutputWord),
    (baseR,layoutOffset 1),(copyR,layoutOffset 2),(outR,layoutOffset 3),(workR,layoutOffset 4)]

def configureInverse : Com := commands inverseBindings

/-- Install the checked matrix-power ABI from three physical caller registers. -/
theorem configureInverse_run {K : Type} [Field K] [Fintype K] (F : FieldPresentation K)
    {n input start S B : ℕ} {s : Env} (hn : 0 < n) (hB : 4 < B)
    (hApart : input+n*n ≤ start) (hFit : start+4*(n*n)+3 ≤ S)
    (hV : ValidMemory F B s) (hS : Slots F canonical ws S B s)
    (hN : s.vars inverseSizeWord=n) (hIn : s.vars inverseInputWord=input)
    (hStart : s.vars inverseOutputWord=start) :
    ∃ t, Run B configureInverse s t 47 ∧ Regs (inverseLayout n input start) t ∧
      ValidMemory F B t ∧ Slots F canonical ws S B t ∧ t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  have hS' := hS.slots_word
  have hnn : n ≤ n*n := Nat.le_mul_of_pos_right _ hn
  have ev (r : String) (v : ℕ) (hr : s.vars r=v) (hv : v<B) :
      (Expr.var r).evalB B s=some v := evalB_var_iff.mpr ⟨hr.symm,hr ▸ hv⟩
  have eN : sizeExpr.evalB B s = some n := ev _ _ hN (by omega)
  have eNN : nnExpr.evalB B s = some (n*n) := evalB_bin (op:=.mul) eN eN (show n*n<B by omega)
  have eN₁ : (Expr.add sizeExpr (.lit 1)).evalB B s = some (n+1) :=
    evalB_bin (op:=.add) eN (evalB_lit (by omega)) (show n+1<B by omega)
  have eIn := ev _ _ hIn (by omega)
  have eStart := ev _ _ hStart (by omega)
  have eOff (k : ℕ) (hk : k ≤ 4) : (layoutOffset k).evalB B s = some (start+k*(n*n)) := by
    have hh := Nat.mul_le_mul_right (n*n) hk
    exact evalB_bin (op:=.add) eStart
      (evalB_bin (op:=.mul) (evalB_lit (by omega)) eNN (show k*(n*n)<B by omega))
      (show start+k*(n*n)<B by omega)
  let vals := [n,n*n,n+1,input,start,start+1*(n*n),start+2*(n*n),start+3*(n*n),start+4*(n*n)]
  let pairs := List.zip (inverseBindings.map Prod.fst) vals
  let t := install pairs s
  have hh : List.Forall₂ (fun p v => p.2.evalB B s=some v) inverseBindings vals :=
    .cons eN (.cons eNN (.cons eN₁ (.cons eIn (.cons eStart (.cons (eOff 1 (by decide))
      (.cons (eOff 2 (by decide)) (.cons (eOff 3 (by decide)) (.cons (eOff 4 (by decide)) .nil))))))))
  have hRoster (p : String × ℕ) (hp : p ∈ pairs) : p.1 ∈ layoutRegs := by
    simpa [pairs,vals,inverseBindings,layoutRegs] using
      (List.mem_map.mpr ⟨p,hp,rfl⟩ : p.1 ∈ pairs.map Prod.fst)
  have hFresh : ∀ x ∈ layoutRegs, canonical.e≠x ∧ canonical.p≠x ∧ canonical.modBase≠x ∧ canonical.exp≠x ∧ ws≠x := by decide
  have hV' := installed_valid F pairs s hV (fun p hp =>
    let h := hFresh _ (hRoster p hp)
    ⟨h.1,h.2.1,h.2.2.1⟩)
  have hS'' := installed_slots F pairs s hS (fun p hp => hFresh _ (hRoster p hp))
  have r : Run B configureInverse s t 47 := commands_run inverseBindings vals s (by rfl) hh (by
    simp [inverseBindings,NoVar,sizeExpr,nnExpr,layoutOffset,nReg,nnReg,n1Reg,inR,accR,baseR,copyR,outR,workR,
      inverseSizeWord,inverseInputWord,inverseOutputWord])
  refine ⟨t,r,?_,hV',hS'',installed_arrays pairs s⟩
  constructor <;> first | rfl | simp [t,pairs,vals,install,inverseLayout,inverseBindings,
    nReg,nnReg,n1Reg,inR,accR,baseR,copyR,outR,workR]

#print axioms inverseLayout_ok
#print axioms configureInverse_run
end EvenTI.P15Execution