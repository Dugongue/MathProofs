import EvenP17TrialReciprocalSweep
import EvenP17ExecutionCells
import EvenP16TrialAnchorEmit
import EvenP16AnchorCrossGrid

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace EvenTI.P19Trial

open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P17Trial EvenTI.P17Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.P15RecogIMPGrid20261007 (gRows)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul ev_add)

def higherHeaderCountExpr : Expr :=
  .add (.var reciprocalSweepLimit) (.var reciprocalSweepLimit)

def higherHeaderLengthExpr : Expr :=
  .add (.lit 1) (.mul (.var reciprocalCountWord) (.add (.var gRows) (.lit 2)))

def higherHeader : Com :=
  .seq (.assign reciprocalCountWord higherHeaderCountExpr) <|
    .seq (.assign gRows (.mul (.var crossN) (.var crossN))) <|
      .seq (.write (.lit 2)) <|
        .seq (.write higherHeaderLengthExpr) (.write (.var reciprocalCountWord))

def higherHeaderState (s : Env) (l n : ℕ) : Env :=
  let c := (l+1)+(l+1)
  let t := (s.setVar reciprocalCountWord c).setVar gRows (n*n)
  {t with out := s.out++[2,1+c*(n*n+2),c]}

/-- Produce the public tag and both exact lengths from live width and
mode-count words. -/
theorem higherHeader_run {B l n : ℕ} {s : Env}
    (hWidth : s.vars crossN=n) (hCount : s.vars reciprocalSweepLimit=l+1)
    (hN : n*n+2 < B) (hLen : 1+((l+1)+(l+1))*(n*n+2) < B) :
    Run B higherHeader s (higherHeaderState s l n) 20 := by
  let c := (l+1)+(l+1)
  let t := (s.setVar reciprocalCountWord c).setVar gRows (n*n)
  let v : Env := {t with out := s.out++[2]}
  let u : Env := {t with out := s.out++[2,1+c*(n*n+2)]}
  have hLen' : 1+c*(n*n+2)<B := hLen
  have hProd : c*(n*n+2)<B := by omega
  have hc : c < B := (Nat.le_mul_of_pos_right c (by omega : 0 < n*n+2)).trans_lt hProd
  have hn : n < B := (Nat.le_mul_self n).trans_lt (by omega)
  have em := ev_var hCount (show l+1 < B by omega)
  have r₁ : Run B (.assign reciprocalCountWord higherHeaderCountExpr) s (s.setVar reciprocalCountWord c) 4 :=
    Run.assign (ev_add em em hc)
  have en' : (s.setVar reciprocalCountWord c).vars crossN=n := hWidth
  have r₂ : Run B (.assign gRows (.mul (.var crossN) (.var crossN))) (s.setVar reciprocalCountWord c) t 4 :=
    Run.assign (ev_mul (ev_var en' hn) (ev_var en' hn) (by omega))
  have r₃ : Run B (.write (.lit 2)) t v 2 :=
    Run.write (evalB_lit (by omega))
  have evC (w : Env) (hw : w.vars=t.vars) :
      (Expr.var reciprocalCountWord).evalB B w=some c :=
    ev_var (show w.vars reciprocalCountWord=c by rw [hw]; rfl) hc
  have evN : (Expr.var gRows).evalB B v=some (n*n) :=
    ev_var (show v.vars gRows=n*n from rfl) (by omega)
  have evLen : higherHeaderLengthExpr.evalB B v=some (1+c*(n*n+2)) :=
    ev_add (evalB_lit (by omega)) (ev_mul (evC v rfl)
      (ev_add evN (evalB_lit (by omega)) hN) hProd) hLen'
  have r₄ : Run B (.write higherHeaderLengthExpr) v u 8 := by
    have he : 1+higherHeaderLengthExpr.size=8 := rfl
    have rr := Run.write evLen
    rw [he] at rr
    simpa only [u,v,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using rr
  have r₅ : Run B (.write (.var reciprocalCountWord)) u (higherHeaderState s l n) 2 := by
    have he : 1+(Expr.var reciprocalCountWord).size=2 := rfl
    have rr := Run.write (evC u rfl)
    rw [he] at rr
    simpa only [u,t,c,higherHeaderState,List.append_assoc,List.cons_append,List.nil_append] using rr
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

def restoreHigherTraceArgs : Com :=
  .seq (.assign fieldVectorStart (.var anchorTraceWord))
    (.assign fieldVectorLength (.mul (.var crossN) (.var crossN)))

def restoredTraceState (s : Env) (o n : ℕ) : Env :=
  (s.setVar fieldVectorStart o).setVar fieldVectorLength (n*n)

/-- Keep the bank roles available for the following form-pair visit after
serializing the two full forms. -/
theorem restoreHigherTraceArgs_run {B o n : ℕ} {s : Env}
    (hO : s.vars anchorTraceWord=o) (hN : s.vars crossN=n)
    (ho : o<B) (hn : n*n<B) :
    Run B restoreHigherTraceArgs s (restoredTraceState s o n) 6 := by
  let α := s.setVar fieldVectorStart o
  have r₁ : Run B (.assign fieldVectorStart (.var anchorTraceWord)) s α 2 :=
    Run.assign (ev_var hO ho)
  have hα : α.vars crossN=n := hN
  have en := ev_var hα ((Nat.le_mul_self n).trans_lt hn)
  have r₂ : Run B (.assign fieldVectorLength (.mul (.var crossN) (.var crossN))) α
      (restoredTraceState s o n) 4 :=
    Run.assign (ev_mul en en hn)
  exact r₁.seq r₂

#print axioms higherHeader_run
#print axioms restoreHigherTraceArgs_run
end EvenTI.P19Trial
