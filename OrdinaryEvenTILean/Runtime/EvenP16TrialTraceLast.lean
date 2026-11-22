import EvenP16AnchorTraceGrid
import EvenP15ReciprocalTrace
import Mathproof.Meta.P15RecogIMPGrid20261007

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P16Trial

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul ev_add)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

open EvenTI.P16Execution (traceGridBase traceGridOne)
private def gridTraceRegs : List String := [dL,dT,dU,dZ,gRows,gCols,gOut,traceGridBase,traceGridOne]

def traceLastGridIndex (base n i j a : ℕ) : ℕ := base + ((i*n+a)*(n*n)+(j*n+a))
private def groupedLast (x : String) : Expr := .add (.mul (.var x) (.var gCols)) (.var dI)
private def sides : Expr := .mul (.var gCols) (.var gCols)
private def traceLastGridAddress : Expr := .add (.var traceGridBase)
  (.add (.mul (groupedLast gU) sides) (groupedLast gV))

noncomputable def traceLastGrid (F : FieldPresentation K) : Com :=
  gridProg (fieldMacros F) traceLastGridAddress (.var traceGridOne)

noncomputable def traceLastGridCost (F : FieldPresentation K) (n : ℕ) : ℕ :=
  gridCost (fieldMacros F) traceLastGridAddress (.var traceGridOne) n n n

private theorem traceLastGridIndex_lt {base n i j a S : ℕ} (hi : i<n) (hj : j<n) (ha : a<n)
    (hFit : base+(n*n)*(n*n)≤S) : traceLastGridIndex base n i j a < S := by
  have hr : i*n+a < n*n := by simpa using (out_lt (o0:=0) hi ha)
  have hc : j*n+a < n*n := by simpa using (out_lt (o0:=0) hj ha)
  exact (out_lt (o0:=base) hr hc).trans_le hFit

/-- The entire diagonal-block partial trace, in the exact row-major
field bank consumed by the following anchor serialization stage. -/
theorem traceLastGrid_run (F : FieldPresentation K) {B S n base o tt uu z one : ℕ} {s : Env}
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) K)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1<B)
    (hFit : base+(n*n)*(n*n)≤S) (hOut : o+n*n≤S)
    (hO : s.vars gOut=o) (hR : s.vars gRows=n) (hC : s.vars gCols=n) (hL : s.vars dL=n)
    (hT : s.vars dT=tt) (hU : s.vars dU=uu) (hZ : s.vars dZ=z)
    (hBase : s.vars traceGridBase=base) (hOne : s.vars traceGridOne=one)
    (hSep : o+n*n≤base) (hTBelow : tt<o) (hUBelow : uu<o) (hTU : tt≠uu)
    (hZB : z<S) (h1B : one<S)
    (hZkeep : ¬ Written o n n tt uu z) (h1keep : ¬ Written o n n tt uu one)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hMat : ∀ (i j a : Fin n), val F canonical qN.WS s
      (traceLastGridIndex base n i.val j.val a.val)=A (i,a) (j,a)) :
    ∃ t, Run B (traceLastGrid F) s t (traceLastGridCost F n) ∧ Slots F canonical qN.WS S B t ∧
      (∀ (i j : Fin n), val F canonical qN.WS t (o+(i.val*n+j.val)) =
        ∑ a : Fin n, A (i,a) (j,a)) ∧
      (∀ k < S, ¬ Written o n n tt uu k → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ x, x ∉ regNames canonical → x ≠ dI → x ≠ gU → x ≠ gV → x ≠ dO → t.vars x=s.vars x) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hSB := hS.slots_word
  let fa := traceLastGridIndex base n
  have ha (r : Env) (hf : ∀ x ∈ gridTraceRegs,r.vars x=s.vars x)
      (i : ℕ) (hi : i<n) (j : ℕ) (hj : j<n) (a : ℕ) (hA : a<n)
      (hRi : r.vars gU=i) (hRj : r.vars gV=j) (hRa : r.vars dI=a) :
      traceLastGridAddress.evalB B r=some (fa i j a) := by
    have hr : i*n+a < n*n := by simpa using (out_lt (o0:=0) hi hA)
    have hc : j*n+a < n*n := by simpa using (out_lt (o0:=0) hj hA)
    have haB := (traceLastGridIndex_lt hi hj hA hFit).trans hSB
    unfold traceLastGridIndex at haB
    have hn0 : 0 < n := by omega
    have hSq : n*n ≤ (n*n)*(n*n) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hn0 hn0)
    have hSqB : n*n < B := by omega
    have en := ev_var ((hf gCols (by simp [gridTraceRegs])).trans hC) (show n<B by omega)
    have ea := ev_var hRa (show a<B by omega)
    have ei := ev_add (ev_mul (ev_var hRi (show i<B by omega)) en (show i*n<B by omega))
      ea (show i*n+a<B by omega)
    have ej := ev_add (ev_mul (ev_var hRj (show j<B by omega)) en (show j*n<B by omega))
      ea (show j*n+a<B by omega)
    have eb := ev_var ((hf traceGridBase (by simp [gridTraceRegs])).trans hBase) (show base<B by omega)
    exact ev_add eb (ev_add (ev_mul ei (ev_mul en en hSqB) (by omega)) ej (by omega)) haB
  obtain ⟨t,hr,hSt,hVals,hKeep,hVars,_,hInput,hOutput⟩ :=
    grid_run (fieldMacros F) gridTraceRegs (by decide)
      (by simp [gridTraceRegs]) (by simp [gridTraceRegs]) (by simp [gridTraceRegs]) (by simp [gridTraceRegs])
      (by simp [gridTraceRegs]) (by simp [gridTraceRegs]) (by simp [gridTraceRegs])
      traceLastGridAddress (.var traceGridOne)
      (by simp [traceLastGridAddress,groupedLast,sides,gridTraceRegs,VarsIn]) (by simp [gridTraceRegs,VarsIn])
      (fa:=fa) (fb:=fun _ _ _ => one) hS hL hT hU hZ hR hC hO ha
      (fun r hf _ _ _ _ _ _ _ _ _ => ev_var ((hf _ (by simp [gridTraceRegs])).trans hOne) (h1B.trans hSB))
      (fun i hi j hj a hA => ⟨traceLastGridIndex_lt hi hj hA hFit,by unfold fa traceLastGridIndex Written; omega⟩)
      (fun _ _ _ _ _ _ => ⟨h1B,h1keep⟩) hOut (by omega) (by omega) hZB hTU hZkeep
      (by omega) (by omega) hZero hN hN hN (hOut.trans_lt hSB)
  refine ⟨t,hr,hSt,?_,hKeep,hVars,hInput,hOutput⟩
  intro i j
  rw [hVals i.val i.isLt j.val j.isLt,←Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show fa i.val j.val a.val = traceLastGridIndex base n i.val j.val a.val from rfl,hMat i j a,hUnit,mul_one]

#print axioms traceLastGrid_run
end EvenTI.P16Trial