import EvenP16TrialTraceLast
import EvenP16AnchorSquareTrace

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace EvenTI.P18Trial

open EvenTI.P16Trial EvenTI.P16Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar regNames)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_slots installed_arrays installed_scalar)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU dI dO)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut gU gV Written)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

variable {K : Type} [Field K] [Fintype K]

def oppositeTraceArgs : List (String × Expr) :=
  [(gRows,.var anchorSideWord),(gCols,.var anchorSideWord),(dL,.var anchorSideWord),
   (gOut,.var anchorTraceWord),(traceGridBase,.var anchorSquareWord),(traceGridOne,.var anchorUnitWord)]

def oppositeTraceRegisters : List String := [gRows,gCols,dL,gOut,traceGridBase,traceGridOne]

noncomputable def oppositeTraceCall (F : FieldPresentation K) : Com :=
  .seq (commands oppositeTraceArgs) (traceLastGrid F)

noncomputable def oppositeTraceCallCost (F : FieldPresentation K) (n : ℕ) : ℕ :=
  13+traceLastGridCost F n

/-- Invoke the opposite trace of the already computed square, using the
saved square and output offsets. The shared square and low banks remain
available, including the fixed field constants. -/
theorem oppositeTraceCall_run (F : FieldPresentation K) {B S n base o tt uu z one : ℕ} {s : Env}
    (A : Matrix (Fin n × Fin n) (Fin n × Fin n) K)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1<B)
    (hFit : base+(n*n)*(n*n)≤S) (hSep : o+n*n≤base) (hTBelow : tt<o) (hUBelow : uu<o) (hTU : tt≠uu)
    (hZ : z<o ∧ z≠tt ∧ z≠uu) (hOne : one<o ∧ one≠tt ∧ one≠uu)
    (hTR : s.vars dT=tt) (hUR : s.vars dU=uu) (hZR : s.vars dZ=z)
    (hSide : s.vars anchorSideWord=n) (hBase : s.vars anchorSquareWord=base)
    (hO : s.vars anchorTraceWord=o) (hUnit : s.vars anchorUnitWord=one)
    (hZero : val F canonical qN.WS s z=0) (hOneVal : val F canonical qN.WS s one=1)
    (hMat : ∀ (i j a : Fin n), val F canonical qN.WS s
      (traceLastGridIndex base n i.val j.val a.val)=A (i,a) (j,a)) :
    ∃ t, Run B (oppositeTraceCall F) s t (oppositeTraceCallCost F n) ∧ Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (o+(i.val*n+j.val))=∑ a : Fin n, A (i,a) (j,a)) ∧
      (∀ k < S, ¬ Written o n n tt uu k → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r∉oppositeTraceRegisters → r∉regNames canonical → r≠dI → r≠gU → r≠gV → r≠dO →
        t.vars r=s.vars r) ∧ t.inp=s.inp ∧ t.out=s.out := by
  have hSB := hS.slots_word
  let vals := [(gRows,n),(gCols,n),(dL,n),(gOut,o),(traceGridBase,base),(traceGridOne,one)]
  let μ := install vals s
  have en := ev_var hSide (show n<B by omega)
  have eo := ev_var hO (show o<B by omega)
  have es := ev_var hBase (show base<B by omega)
  have e1 := ev_var hUnit (show one<B by omega)
  have r₀ : Run B (commands oppositeTraceArgs) s μ 13 :=
    commands_run oppositeTraceArgs [n,n,n,o,base,one] s rfl
      (.cons en (.cons en (.cons en (.cons eo (.cons es (.cons e1 .nil))))))
      (by simp [oppositeTraceArgs,NoVar,gRows,gCols,dL,gOut,traceGridBase,traceGridOne,
        anchorSideWord,anchorTraceWord,anchorSquareWord,anchorUnitWord])
  have hReg (r : String) (hr : r ∉ oppositeTraceRegisters) : μ.vars r=s.vars r :=
    installed_scalar vals s r (fun q hq he => hr (List.mem_map.mpr ⟨q,hq,he.symm⟩))
  have hField : ∀ r∈oppositeTraceRegisters, canonical.e≠r ∧ canonical.p≠r ∧
      canonical.modBase≠r ∧ canonical.exp≠r ∧ qN.WS≠r := by decide
  have hSμ := installed_slots F vals s hS (fun p hp => hField p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))
  obtain ⟨hArr,hI,hOut⟩ := installed_arrays vals s
  have hMem (k : ℕ) : val F canonical qN.WS μ k=val F canonical qN.WS s k := by
    unfold val slice
    rw [hReg _ (by decide),hArr]
  obtain ⟨t,r₁,hSlot,hVal,hFrame,hVars,hi,ho⟩ := traceLastGrid_run F A hSμ hN hFit
    (by omega)
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    ((hReg _ (by decide)).trans hTR) ((hReg _ (by decide)).trans hUR) ((hReg _ (by decide)).trans hZR)
    (by rfl)
    (by rfl)
    hSep hTBelow hUBelow hTU (by omega) (by omega)
    (by unfold Written; omega) (by unfold Written; omega)
    ((hMem _).trans hZero) ((hMem _).trans hOneVal) (fun i j a => (hMem _).trans (hMat i j a))
  exact ⟨t,r₀.seq r₁,hSlot,hVal,fun k hk hk' => (hFrame k hk hk').trans (hMem k),
    fun r h₁ h₂ h₃ h₄ h₅ h₆ => (hVars r h₂ h₃ h₄ h₅ h₆).trans (hReg r h₁),hi.trans hI,ho.trans hOut⟩

#print axioms oppositeTraceCall_run
end EvenTI.P18Trial
