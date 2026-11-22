import EvenP12CountPreHeaders

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile

set_option autoImplicit false

theorem eval_predecessor {B v : Nat} {σ : Env} {e : Expr}
    (he : e.evalB B σ = some (v+1)) (hv : v < B) (hB : 1 < B) :
    (predecessorExpr e).evalB B σ = some v := by
  simpa [predecessorExpr,Nat.add_sub_cancel] using evalB_bin (op := .sub) he (evalB_lit hB)
    (by simp; exact hv)

theorem payloadStart_run {B a d n : Nat} {σ : Env}
    (ha : σ.vars "secondStart" = a) (hd : σ.vars "modeStop" = d+1)
    (hn : σ.vars "dimWord" = n+1)
    (hB : 1 < B) (hD : d+1 < B) (hN : n+1 < B)
    (hM : a+2+n*n < B) (hAll : a+2+d*(n*n) < B) :
    ∃ τ, Run B payloadStart σ τ 30 ∧
    τ.vars "matrixStart" = a+2 ∧ τ.vars "square" = n*n ∧
    τ.vars "matrixEnd" = a+2+n*n ∧ τ.vars "allEnd" = a+2+d*(n*n) ∧
    τ.vars "modeWord" = 1 ∧
    (∀ v, v ≠ "matrixStart" → v ≠ "square" → v ≠ "matrixEnd" →
      v ≠ "allEnd" → v ≠ "modeWord" → τ.vars v = σ.vars v) ∧
    τ.arrs = σ.arrs ∧ τ.out = σ.out := by
  let s := n*n
  let t₁ := σ.setVar "matrixStart" (a+2)
  let t₂ := t₁.setVar "square" s
  let t₃ := t₂.setVar "matrixEnd" (a+2+s)
  let t₄ := t₃.setVar "allEnd" (a+2+d*s)
  let t₅ := t₄.setVar "modeWord" 1
  have hs : s < B := by dsimp [s]; omega
  have hsum : a+2 < B := by omega
  have hload : (Expr.var "secondStart").evalB B σ = some a :=
    by rw [evalB_var_iff,ha]; exact ⟨rfl,by omega⟩
  have hAddr : (addLiteral (.var "secondStart") 2).evalB B σ = some (a+2) :=
    evalB_bin (op := .add) hload (evalB_lit (by omega)) hsum
  have r₁ : Run B (.assign "matrixStart" (addLiteral (.var "secondStart") 2)) σ t₁ 4 := Run.assign hAddr
  have hWord : (Expr.var "dimWord").evalB B t₁ = some (n+1) := by simp [t₁,hn,hN]
  have hPred := eval_predecessor hWord (by omega) hB
  have r₂ : Run B (.assign "square" (.bin .mul (predecessorExpr (.var "dimWord"))
      (predecessorExpr (.var "dimWord")))) t₁ t₂ 8 :=
    Run.assign (evalB_bin (op := .mul) hPred hPred hs)
  have hStart₂ : (Expr.var "matrixStart").evalB B t₂ = some (a+2) := by simp [t₂,t₁,hsum]
  have hSq₂ : (Expr.var "square").evalB B t₂ = some s := by simp [t₂,hs]
  have r₃ : Run B (.assign "matrixEnd" (.add (.var "matrixStart") (.var "square"))) t₂ t₃ 4 :=
    Run.assign (evalB_bin (op := .add) hStart₂ hSq₂ hM)
  have hStart₃ : (Expr.var "matrixStart").evalB B t₃ = some (a+2) := by simp [t₃,t₂,t₁,hsum]
  have hSq₃ : (Expr.var "square").evalB B t₃ = some s := by simp [t₃,t₂,hs]
  have hStop₃ : (Expr.var "modeStop").evalB B t₃ = some (d+1) := by simp [t₃,t₂,t₁,hd,hD]
  have hBS : d*s < B := by dsimp [s]; omega
  have hProd := evalB_bin (op := .mul) (eval_predecessor hStop₃ (by omega) hB) hSq₃ hBS
  have r₄ : Run B (.assign "allEnd" (.add (.var "matrixStart")
       (.bin .mul (predecessorExpr (.var "modeStop")) (.var "square")))) t₃ t₄ 8 :=
    Run.assign (evalB_bin (op := .add) hStart₃ hProd hAll)
  have r₅ : Run B (.assign "modeWord" (.lit 1)) t₄ t₅ 2 := Run.assign (evalB_lit hB)
  refine ⟨t₅,(r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (by decide),?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · simp [t₅,t₄,t₃,t₂,t₁]
  · simp [t₅,t₄,t₃,t₂,s]
  · simp [t₅,t₄,t₃,s]
  · simp [t₅,t₄,s]
  · simp [t₅]
  · intro v h₁ h₂ h₃ h₄ h₅
    simp [t₅,t₄,t₃,t₂,t₁,h₁,h₂,h₃,h₄,h₅]

#print axioms payloadStart_run
end EvenTI.P12CountPre
