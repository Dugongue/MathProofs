import Mathproof.Meta.Problem18RAMLax13ProofsReasoning20261001

set_option autoImplicit false

namespace EvenTI.P15Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning

def appendInput (σ : Env) (tail : List ℕ) : Env := {σ with inp := σ.inp++tail}

private theorem evalExpr_tail (B : ℕ) (σ : Env) (tail : List ℕ) (e : Expr) :
    e.evalB B (appendInput σ tail)=e.evalB B σ := by
  induction e with
  | lit => rfl
  | var => rfl
  | get a i hi =>
    exact congrArg (fun r : Option ℕ => r.bind fun k => (σ.arrs a)[k]?.bind (fit B)) hi
  | bin op a b ha hb => simp only [Expr.evalB,ha,hb]

private theorem evalCond_tail (B : ℕ) (σ : Env) (tail : List ℕ) (e : Cond) :
    e.evalB B (appendInput σ tail)=e.evalB B σ := by
  cases e <;> simp only [Cond.evalB,evalExpr_tail]

private theorem step_tail {B k : ℕ} {c : Com} {σ τ : Env} (tail : List ℕ)
    (h : BigStepB B c σ τ k) : BigStepB B c (appendInput σ tail) (appendInput τ tail) k := by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (by rwa [evalExpr_tail])
  | store h₁ h₂ h₃ =>
    exact .store (by rwa [evalExpr_tail]) (by rwa [evalExpr_tail]) h₃
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true h _ ih => exact .ite_true (by rwa [evalCond_tail]) ih
  | ite_false h _ ih => exact .ite_false (by rwa [evalCond_tail]) ih
  | while_true h _ _ ih ih' => exact .while_true (by rwa [evalCond_tail]) ih ih'
  | while_false h => exact .while_false (by rwa [evalCond_tail])
  | read h =>
    apply BigStepB.read
    simp only [appendInput,h,List.cons_append]
  | write h => exact .write (by rwa [evalExpr_tail])

/-- A caller may append its remaining tape to a verified prefix execution.
The prefix touches exactly the same state and retains the extra words. -/
theorem paidRun_appendInput {B k : ℕ} {c : Com} {σ τ : Env} (tail : List ℕ)
    (h : Run B c σ τ k) : Run B c (appendInput σ tail) (appendInput τ tail) k := by
  obtain ⟨v,hv,hStep⟩ := h
  exact ⟨v,hv,step_tail tail hStep⟩

#print axioms paidRun_appendInput
end EvenTI.P15Trial
