import Mathproof.Meta.Problem18RAMLax13ProofsBounds20261001

namespace Mathproof.Problem18IMPModularArithmetic20261001
open Lax13Proofs.Imp

/-- A concrete RAM-expression implementation of remainder; division by zero
has the same total natural-number semantics as Lean. -/
def modExpr (a p : Expr) : Expr := .sub a (.mul (.div a p) p)

theorem modExpr_eval {a p : Expr} {σ : Env} {n d : ℕ}
    (ha : a.eval σ=some n) (hp : p.eval σ=some d) :
    (modExpr a p).eval σ=some (n%d) := by
  simp [modExpr,Expr.eval,ha,hp,Bop.apply,Nat.mod_def] <;> simp only [Nat.mul_comm]

/-- Remainder introduces no value larger than the numerator, so its actual
bounded execution follows from the bounds on the two operands. -/
theorem modExpr_evalB {a p : Expr} {σ : Env} {B n d : ℕ}
    (ha : a.evalB B σ=some n) (hp : p.evalB B σ=some d) :
    (modExpr a p).evalB B σ=some (n%d) := by
  have hn := Expr.lt_of_evalB ha
  have hq : n/d<B := (Nat.div_le_self n d).trans_lt hn
  have hm : n/d*d<B := (Nat.div_mul_le_self n d).trans_lt hn
  have hr : n-n/d*d<B := (Nat.sub_le n (n/d*d)).trans_lt hn
  simp [modExpr,Expr.evalB,ha,hp,Bop.apply,fit_self hq,fit_self hm,fit_self hr,Nat.mod_def] <;> simp only [Nat.mul_comm]

theorem modExpr_size (a p : Expr) :
    (modExpr a p).size=2*a.size+2*p.size+3 := by
  simp [modExpr,Expr.size]
  omega

end Mathproof.Problem18IMPModularArithmetic20261001