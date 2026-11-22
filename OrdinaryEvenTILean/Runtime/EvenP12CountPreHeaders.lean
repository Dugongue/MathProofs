import EvenP12CountPrePrefix

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile

set_option autoImplicit false

def addLiteral (e : Expr) (k : Nat) : Expr := .add e (.lit k)
def predecessorExpr (e : Expr) : Expr := .bin .sub e (.lit 1)
def dataAt (i : Expr) : Expr := .get "data" i

def querySizeGuard : Com :=
  .seq (.assign "paramEnd" (dataAt (.lit 0)))
    (.ite (.lt (addLiteral (.var "paramEnd") 1) (.var "firstEnd"))
      (.seq (.assign "modeStop" (dataAt (.var "paramEnd")))
        (.assign "dimWord" (dataAt (addLiteral (.var "paramEnd") 1))))
      (.seq (.assign "modeStop" (.lit 0)) (.assign "dimWord" (.lit 0))))

def payloadStart : Com :=
  .seq (.assign "matrixStart" (addLiteral (.var "secondStart") 2))
    (.seq (.assign "square" (.bin .mul (predecessorExpr (.var "dimWord")) (predecessorExpr (.var "dimWord"))))
      (.seq (.assign "matrixEnd" (.add (.var "matrixStart") (.var "square")))
        (.seq (.assign "allEnd" (.add (.var "matrixStart")
              (.bin .mul (predecessorExpr (.var "modeStop")) (.var "square"))))
          (.assign "modeWord" (.lit 1)))))

theorem eval_dataAt {z : List Nat} {B j : Nat} {σ : Env} {e : Expr}
    (he : e.evalB B σ = some j) (hj : j < z.length)
    (hBank : σ.arrs "data" = sentinelWords z) (hw : ∀ v ∈ z, v < B) :
    (dataAt e).evalB B σ = some z[j] := by
  apply evalB_get he ?_ (hw _ (List.getElem_mem hj))
  rw [hBank,sentinelWords,List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

theorem querySizeGuard_run (z : List Nat) {B f : Nat} {σ : Env}
    (hf : σ.vars "firstEnd" = f) (hpos : 0 < f) (hfz : f ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length < B) (hWords : ∀ v ∈ z, v+1 < B) :
    let e := z.headD 0
    let m := if e+1 < f then z.getD e 0 else 0
    let n := if e+1 < f then z.getD (e+1) 0 else 0
    ∃ τ, Run B querySizeGuard σ τ 18 ∧ τ.vars "paramEnd" = e ∧
      τ.vars "modeStop" = m ∧ τ.vars "dimWord" = n ∧
      τ.vars "firstEnd" = f ∧ τ.arrs = σ.arrs ∧ τ.out = σ.out := by
  let e := z.headD 0
  let t := σ.setVar "paramEnd" e
  have hz : 0 < z.length := by omega
  have hOne : 1 < B := by omega
  have hhead : z[0] = e := by cases z with | nil => simp at hz | cons => rfl
  have he : e+1 < B := by rw [← hhead]; exact hWords _ (List.getElem_mem hz)
  have r₁ : Run B (.assign "paramEnd" (dataAt (.lit 0))) σ t 3 := by
    apply Run.assign
    rw [← hhead]
    exact eval_dataAt (evalB_lit (by omega)) hz hBank (fun v hv => by have := hWords v hv; omega)
  have hv : (Expr.var "paramEnd").evalB B t = some e := by
    rw [evalB_var_iff,show t.vars "paramEnd" = e by simp [t]]; exact ⟨rfl,by omega⟩
  have hv' : (addLiteral (.var "paramEnd") 1).evalB B t = some (e+1) :=
    evalB_bin (op := .add) hv (evalB_lit hOne) he
  have he' : (Expr.var "firstEnd").evalB B t = some f := by
    rw [evalB_var_iff,show t.vars "firstEnd" = f by simp [t,hf]]; exact ⟨rfl,hfz.trans_lt hLen⟩
  have hcond := evalB_condLt hv' he'
  by_cases h : e+1 < f
  · have hj : e < z.length := by omega
    have hj' : e+1 < z.length := by omega
    let m := z[e]
    let n := z[e+1]
    let u := t.setVar "modeStop" m
    let v := u.setVar "dimWord" n
    have r₂ : Run B (.assign "modeStop" (dataAt (.var "paramEnd"))) t u 3 :=
      Run.assign (eval_dataAt hv hj (by simpa [t] using hBank)
        (fun v hv => by have := hWords v hv; omega))
    have hvar : (Expr.var "paramEnd").evalB B u = some e := by
      rw [evalB_var_iff,show u.vars "paramEnd" = e by simp [u,t]]; exact ⟨rfl,by omega⟩
    have r₃ : Run B (.assign "dimWord" (dataAt (addLiteral (.var "paramEnd") 1))) u v 5 :=
      Run.assign (eval_dataAt (evalB_bin (op := .add) hvar (evalB_lit hOne) he) hj'
        (by simpa [u,t] using hBank) (fun v hv => by have := hWords v hv; omega))
    have hg : (Cond.lt (addLiteral (.var "paramEnd") 1) (.var "firstEnd")).evalB B t = some true :=
      by simpa [h] using hcond
    have hr : Run B querySizeGuard σ v 18 :=
      (r₁.seq (Run.ite_true (d := .seq (.assign "modeStop" (.lit 0)) (.assign "dimWord" (.lit 0)))
        hg (r₂.seq r₃))).mono (by decide)
    refine ⟨v,hr,?_,?_,?_,?_,?_,?_⟩
    · rfl
    · change m = (if e+1 < f then z.getD e 0 else 0)
      simp only [if_pos h,m,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
    · change n = (if e+1 < f then z.getD (e+1) 0 else 0)
      simp only [if_pos h,n,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some]
    · simp [v,u,t,hf]
    · rfl
    · rfl
  · let u := t.setVar "modeStop" 0
    let v := u.setVar "dimWord" 0
    have r₂ : Run B (.assign "modeStop" (.lit 0)) t u 2 := Run.assign (evalB_lit (by omega))
    have r₃ : Run B (.assign "dimWord" (.lit 0)) u v 2 := Run.assign (evalB_lit (by omega))
    have hg : (Cond.lt (addLiteral (.var "paramEnd") 1) (.var "firstEnd")).evalB B t = some false :=
      by simpa [h] using hcond
    have hr : Run B querySizeGuard σ v 18 :=
      (r₁.seq (Run.ite_false (c := .seq (.assign "modeStop" (dataAt (.var "paramEnd")))
        (.assign "dimWord" (dataAt (addLiteral (.var "paramEnd") 1)))) hg (r₂.seq r₃))).mono (by decide)
    refine ⟨v,hr,rfl,?_,?_,?_,rfl,rfl⟩
    · change 0 = (if e+1 < f then z.getD e 0 else 0)
      rw [if_neg h]
    · change 0 = (if e+1 < f then z.getD (e+1) 0 else 0)
      rw [if_neg h]
    · simpa [v,u,t] using hf

#print axioms querySizeGuard_run
end EvenTI.P12CountPre
