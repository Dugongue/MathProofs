import Mathproof.Meta.Problem18RAMLax13ProofsReasoning20261001

set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile

private theorem exprWordLift {B B' : ℕ} (h : B ≤ B') (σ : Env) (e : Expr) {v : ℕ}
    (he : e.evalB B σ=some v) : e.evalB B' σ=some v := by
  induction e generalizing v with
  | lit n =>
    obtain ⟨hv,hn⟩ := evalB_lit_iff.mp he
    exact evalB_lit_iff.mpr ⟨hv,hn.trans_le h⟩
  | var r =>
    obtain ⟨hv,hn⟩ := evalB_var_iff.mp he
    exact evalB_var_iff.mpr ⟨hv,hn.trans_le h⟩
  | get a i ih =>
    obtain ⟨k,hk,hr,hv⟩ := evalB_get_iff.mp he
    exact evalB_get (ih hk) hr (hv.trans_le h)
  | bin op e f ihe ihf =>
    obtain ⟨m,n,hm,hn,rfl,hv⟩ := evalB_bin_iff.mp he
    exact evalB_bin (ihe hm) (ihf hn) (hv.trans_le h)

private theorem condWordLift {B B' : ℕ} (h : B ≤ B') (σ : Env) (c : Cond) {v : Bool}
    (hc : c.evalB B σ=some v) : c.evalB B' σ=some v := by
  cases c with
  | eq a b =>
    obtain ⟨i,j,hi,hj,rfl⟩ := evalB_condEq_iff.mp hc
    exact evalB_condEq (exprWordLift h σ a hi) (exprWordLift h σ b hj)
  | lt a b =>
    obtain ⟨i,j,hi,hj,rfl⟩ := evalB_condLt_iff.mp hc
    exact evalB_condLt (exprWordLift h σ a hi) (exprWordLift h σ b hj)

private theorem stepWordLift {B B' : ℕ} {c : Com} {σ τ : Env} {k : ℕ}
    (h : B ≤ B') (hr : BigStepB B c σ τ k) : BigStepB B' c σ τ k := by
  induction hr with
  | skip => exact .skip
  | assign he => exact .assign (exprWordLift h _ _ he)
  | store hi he hx => exact .store (exprWordLift h _ _ hi) (exprWordLift h _ _ he) hx
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hc _ ih => exact .ite_true (condWordLift h _ _ hc) ih
  | ite_false hc _ ih => exact .ite_false (condWordLift h _ _ hc) ih
  | while_true hc _ _ ih₁ ih₂ => exact .while_true (condWordLift h _ _ hc) ih₁ ih₂
  | while_false hc => exact .while_false (condWordLift h _ _ hc)
  | read he => exact .read he
  | write he => exact .write (exprWordLift h _ _ he)

/-- A polynomial bound on word *values* can be lifted to the compiler's
power-of-two word ceiling while preserving the literal output and cost. -/
theorem cutRunWordLift {B B' k : ℕ} {c : Com} {σ τ : Env}
    (h : B ≤ B') (hr : Run B c σ τ k) : Run B' c σ τ k := by
  obtain ⟨n,hn,hs⟩ := hr
  exact ⟨n,hn,stepWordLift h hs⟩

#print axioms cutRunWordLift
end EvenTI.P12ComparePrep
