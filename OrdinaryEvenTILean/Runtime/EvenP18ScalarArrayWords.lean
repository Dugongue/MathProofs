import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace EvenTI.P18Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- Every store in a bounded execution writes a bounded word. Therefore an
initially bounded array remains bounded, including unused allocated cells. -/
theorem arrayWords_of_bigStep {W cost : ℕ} {c : Com} {s t : Env}
    (run : BigStepB W c s t cost) (bank : String) :
    (∀ a ∈ s.arrs bank, a < W) → ∀ a ∈ t.arrs bank, a < W := by
  induction run with
  | skip => exact id
  | assign => exact id
  | store hi hv hlen =>
    intro h a ha
    simp only [arrs_setArr] at ha
    split at ha
    · rename_i hEq
      subst bank
      rcases List.mem_or_eq_of_mem_set ha with hOld | hNew
      · exact h a hOld
      · subst a
        exact Expr.lt_of_evalB hv
    · exact h a ha
  | seq _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
  | while_false => exact id
  | read => exact id
  | write => exact id

theorem arrayWords_of_run {W cost : ℕ} {c : Com} {s t : Env}
    (run : Run W c s t cost) (bank : String)
    (h : ∀ a ∈ s.arrs bank, a < W) : ∀ a ∈ t.arrs bank, a < W := by
  obtain ⟨_,_,r⟩ := run
  exact arrayWords_of_bigStep r bank h

#print axioms arrayWords_of_run
end EvenTI.P18Scalar
