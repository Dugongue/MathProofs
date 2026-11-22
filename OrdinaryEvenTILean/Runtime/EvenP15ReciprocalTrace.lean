import EvenP14CutDot
import EvenP15ReciprocalProducts

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.Problem18ClaudeIMPAxpy20261001 (VarsIn)
open Mathproof.Problem18ClaudeFieldMacrosInstancePow20261001 (fieldMacros)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul ev_add)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

private def traceBase : String := "even.trace.base"
private def traceRow : String := "even.trace.row"
private def traceCol : String := "even.trace.col"
private def traceSide : String := "even.trace.side"
private def traceOne : String := "even.trace.one"
private def traceRegs : List String := [dL,dO,dT,dU,dZ,traceBase,traceRow,traceCol,traceSide,traceOne]

private def traceProductSide : Expr := .mul (.var traceSide) (.var traceSide)
private def traceGrouped : Expr := .mul (.var dI) (.var traceSide)
private def traceAddress : Expr := .add (.var traceBase)
  (.add (.mul (.add traceGrouped (.var traceRow)) traceProductSide) (.add traceGrouped (.var traceCol)))

noncomputable def partialTraceEntry (F : FieldPresentation K) : Com :=
  dotProg (fieldMacros F) traceAddress (.var traceOne)

private def traceIndex (base n i j a : ℕ) : ℕ := base+((a*n+i)*(n*n)+(a*n+j))

/-- A paid diagonal-block sum on the live row-major square. The register
parameters select the output entry and the donor dot product supplies its loop. -/
theorem partialTraceEntry_run (F : FieldPresentation K) {B Sn n base o t u z one : ℕ}
    {s : Env} (M : Matrix (Fin n × Fin n) (Fin n × Fin n) K) (i j : Fin n)
    (hS : Slots F canonical qN.WS Sn B s) (hLen : n+1<B)
    (hFit : base+(n*n)*(n*n)≤Sn) (hLive : s.vars dL=n)
    (hB : s.vars traceBase=base) (hi : s.vars traceRow=i.val) (hj : s.vars traceCol=j.val)
    (hn : s.vars traceSide=n) (hOne : s.vars traceOne=one)
    (hO : s.vars dO=o) (hT : s.vars dT=t) (hU : s.vars dU=u) (hZ : s.vars dZ=z)
    (hot : o≠t) (hou : o≠u) (htu : t≠u) (hoz : o≠z)
    (ho : o<base) (ht : t<base) (hu : u<base) (hz : z<Sn)
    (hon : one<Sn) (hnotO : one≠o) (hnotT : one≠t) (hnotU : one≠u)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hMat : ∀ a : Fin n, val F canonical qN.WS s (traceIndex base n i.val j.val a.val)=M (a,i) (a,j)) :
    ∃ s', Run B (partialTraceEntry F) s s' (dotCost (fieldMacros F) traceAddress (.var traceOne) n) ∧
      Slots F canonical qN.WS Sn B s' ∧
      val F canonical qN.WS s' o=∑ a : Fin n, M (a,i) (a,j) ∧
      (∀ k < Sn,k≠o → k≠t → k≠u → val F canonical qN.WS s' k=val F canonical qN.WS s k) ∧
      s'.inp=s.inp ∧ s'.out=s.out := by
  have hSn := hS.slots_word
  have hIdx (a : ℕ) (ha : a<n) : traceIndex base n i.val j.val a<Sn := by
    let f : Fin n := ⟨a,ha⟩
    have hir := Mathproof.Problem18IMPMatrixMemory20261001.index_lt f i
    have hjr := Mathproof.Problem18IMPMatrixMemory20261001.index_lt f j
    let r : Fin (n*n) := ⟨a*n+i.val,hir⟩
    let c : Fin (n*n) := ⟨a*n+j.val,hjr⟩
    have hc := Mathproof.Problem18IMPMatrixMemory20261001.index_lt r c
    change (a*n+i.val)*(n*n)+(a*n+j.val) < (n*n)*(n*n) at hc
    unfold traceIndex
    omega
  have hArgs (τ : Env) (hτ : ∀ x ∈ traceRegs,τ.vars x=s.vars x) (a : ℕ) (ha : a<n)
      (hc : τ.vars dI=a) : traceAddress.evalB B τ = some (traceIndex base n i.val j.val a) := by
    have hIx := (hIdx a ha).trans hSn
    unfold traceIndex at hIx
    have hnp : 0 < n*n := Nat.mul_pos (by omega) (by omega)
    have hlp : n*n ≤ (n*n)*(n*n) := Nat.le_mul_of_pos_right _ hnp
    have eN := ev_var ((hτ _ (by simp [traceRegs])).trans hn) (by omega : n<B)
    have eG := ev_mul (ev_var hc (by omega : a<B)) eN (by
      have h := Mathproof.Problem18IMPMatrixMemory20261001.index_lt (⟨a,ha⟩ : Fin n) j
      exact (Nat.le_add_right _ _).trans_lt (h.trans (hlp.trans_lt (by omega))))
    have eR := ev_var ((hτ _ (by simp [traceRegs])).trans hi) (i.isLt.trans (show n < B by omega))
    have eC := ev_var ((hτ _ (by simp [traceRegs])).trans hj) (j.isLt.trans (show n < B by omega))
    have eS := ev_mul eN eN (by omega : n*n<B)
    have er := ev_add eG eR (by
      have hr := Mathproof.Problem18IMPMatrixMemory20261001.index_lt (⟨a,ha⟩ : Fin n) i
      exact hr.trans (by omega))
    have ec := ev_add eG eC (by omega)
    exact ev_add (ev_var ((hτ _ (by simp [traceRegs])).trans hB) (by omega))
      (ev_add (ev_mul er eS (by omega)) ec (by omega)) hIx
  obtain ⟨s',hr,hS',hOut,hKeep,_,_,hIn,hO'⟩ := dot_run (fieldMacros F) traceRegs
    (by decide) (by simp [traceRegs]) (by simp [traceRegs]) (by simp [traceRegs]) (by simp [traceRegs])
    (by simp [traceRegs]) traceAddress (.var traceOne)
    (by simp [traceAddress,traceGrouped,traceProductSide,traceRegs,VarsIn])
    (by simp [traceRegs,VarsIn]) hS hLive hO hT hU hZ hArgs
    (fun τ hτ _ _ _ => ev_var ((hτ _ (by simp [traceRegs])).trans hOne) (hon.trans hSn))
    (fun a ha => ⟨hIdx a ha,by unfold traceIndex; omega,by unfold traceIndex; omega,by unfold traceIndex; omega⟩)
    (fun _ _ => ⟨hon,hnotO,hnotT,hnotU⟩) (by omega) (by omega) (by omega) hz hot hou htu hoz hZero hLen
  refine ⟨s',hr,hS',?_,hKeep,hIn,hO'⟩
  rw [hOut,←Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hMat a,hUnit,mul_one]

#print axioms partialTraceEntry_run
end EvenTI.P15Execution