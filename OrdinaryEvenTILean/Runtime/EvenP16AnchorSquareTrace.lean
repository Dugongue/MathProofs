import EvenP16AnchorTraceGrid
import EvenP16TrialRectangular
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace EvenTI.P16Execution

open EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val NoVar regNames)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_slots installed_arrays installed_scalar)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

def anchorSideWord : String := "even.anchor.side"
def anchorCrossWord : String := "even.anchor.crossed"
def anchorSquareWord : String := "even.anchor.square"
def anchorTraceWord : String := "even.anchor.trace"
def anchorUnitWord : String := "even.anchor.unit"

private def squareArgs : List (String × Expr) :=
  [(dL,.var gRows),(rectangularLeftBase,.var anchorCrossWord),
   (rectangularRightBase,.var anchorCrossWord),(gOut,.var anchorSquareWord)]
private def traceArgs : List (String × Expr) :=
  [(gRows,.var anchorSideWord),(gCols,.var anchorSideWord),(dL,.var anchorSideWord),
   (gOut,.var anchorTraceWord),(traceGridBase,.var anchorSquareWord),(traceGridOne,.var anchorUnitWord)]

noncomputable def squareTrace (F : FieldPresentation K) : Com :=
  .seq (commands squareArgs) (.seq (rectangularProduct F false) (.seq (commands traceArgs) (traceGrid F)))
noncomputable def squareTraceCost (F : FieldPresentation K) (n : ℕ) : ℕ :=
  9+(rectangularCost F false (n*n) (n*n) (n*n)+(13+traceGridCost F n))

/-- Literal field-slot order for the retained pair. -/
def pairWordIndex {n : ℕ} (p : Fin n × Fin n) : ℕ := p.1.val*n+p.2.val

private theorem pairWordIndex_equiv {n : ℕ} (p : Fin n × Fin n) :
    pairWordIndex p = (finProdFinEquiv p).val := by
  simp [pairWordIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

private theorem installedSlot (F : FieldPresentation K) {B S : ℕ} {s : Env}
    (hS : Slots F canonical qN.WS S B s) (ps : List (String × ℕ))
    (h : ∀ p∈ps, canonical.e≠p.1 ∧ canonical.p≠p.1 ∧ canonical.modBase≠p.1 ∧
      canonical.exp≠p.1 ∧ qN.WS≠p.1) :
    Slots F canonical qN.WS S B (install ps s) ∧
    (∀ k, val F canonical qN.WS (install ps s) k = val F canonical qN.WS s k) ∧
    (install ps s).inp=s.inp ∧ (install ps s).out=s.out := by
  obtain ⟨ha,hi,ho⟩ := installed_arrays ps s
  have hv := installed_scalar ps s qN.WS (fun p hp => (h p hp).2.2.2.2)
  refine ⟨installed_slots F ps s hS h,?_,hi,ho⟩
  intro k
  unfold val slice
  rw [hv,ha]

/-- The paid square and partial-trace stages, with all grid register changes
performed by the actual program. The only matrix input is the crossed bank. -/
theorem squareTrace_run (F : FieldPresentation K) {B S n cross square o tt uu z one : ℕ}
    {s : Env} (A : Matrix (Fin n × Fin n) (Fin n × Fin n) K)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1 < B) (hNN : n*n+1 < B)
    (hCross : cross+(n*n)*(n*n) ≤ square) (hSquare : square+(n*n)*(n*n) ≤ S) (hOut : o+n*n ≤ square)
    (hT : tt < cross ∧ tt < o) (hU : uu < cross ∧ uu < o) (hTU : tt≠uu)
    (hZ : z < o ∧ z < cross ∧ z≠tt ∧ z≠uu) (hOne : one < o ∧ one < cross ∧ one≠tt ∧ one≠uu)
    (hZR : s.vars dZ=z) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu)
    (hRows : s.vars gRows=n*n) (hCols : s.vars gCols=n*n)
    (hSide : s.vars anchorSideWord=n) (hCrossW : s.vars anchorCrossWord=cross)
    (hSquareW : s.vars anchorSquareWord=square) (hTraceW : s.vars anchorTraceWord=o)
    (hOneW : s.vars anchorUnitWord=one)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hMat : ∀ i j : Fin n × Fin n, val F canonical qN.WS s
      (cross+(pairWordIndex i*(n*n)+pairWordIndex j)) = A i j) :
    ∃ t, Run B (squareTrace F) s t (squareTraceCost F n) ∧ Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (o+(i.val*n+j.val)) =
        ∑ a : Fin n, ((A ^ (2 : ℕ)) : Matrix (Fin n × Fin n) (Fin n × Fin n) K) (a,i) (a,j)) ∧
      (∀ p q : Fin n × Fin n, val F canonical qN.WS t (square+(pairWordIndex p*(n*n)+pairWordIndex q)) =
        ((A ^ (2 : ℕ)) : Matrix (Fin n × Fin n) (Fin n × Fin n) K) p q) ∧
      (∀ k < S, ¬ Written square (n*n) (n*n) tt uu k → ¬ Written o n n tt uu k →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hB := hS.slots_word
  let squarePairs := [(dL,n*n),(rectangularLeftBase,cross),(rectangularRightBase,cross),(gOut,square)]
  let s₁ := install squarePairs s
  have hs₁ : Run B (commands squareArgs) s s₁ 9 := commands_run squareArgs [n*n,cross,cross,square] s
    rfl (.cons (ev_var hRows (by omega)) (.cons (ev_var hCrossW (by omega))
      (.cons (ev_var hCrossW (by omega)) (.cons (ev_var hSquareW (by omega)) .nil))))
    (by simp [squareArgs,NoVar,dL,gRows,gOut,rectangularLeftBase,rectangularRightBase,anchorCrossWord,anchorSquareWord])
  have s₁safe : ∀ p∈squarePairs, canonical.e≠p.1 ∧ canonical.p≠p.1 ∧ canonical.modBase≠p.1 ∧
      canonical.exp≠p.1 ∧ qN.WS≠p.1 := by
    intro p hp
    simp only [squarePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  obtain ⟨hS₁,hv₁,hi₁,ho₁⟩ := installedSlot F hS squarePairs s₁safe
  have hvreg (r : String) (h : r ∉ [dL,rectangularLeftBase,rectangularRightBase,gOut]) : s₁.vars r=s.vars r :=
    installed_scalar squarePairs s r (fun p hp e => h (by
      have hh : p.1 ∈ squarePairs.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
      simpa [e,squarePairs] using hh))
  have hZkeep : ¬ Written square (n*n) (n*n) tt uu z := by unfold Written; omega
  obtain ⟨s₂,h₂,hS₂,hSq,hKeep,hVars,_,hi₂,ho₂⟩ :=
    rectangularProduct_run F false hS₁ hCross (by simpa using hCross) hSquare (by omega) (by omega) hTU
      (Or.inr ⟨hT.1,hT.1⟩) (Or.inr ⟨hU.1,hU.1⟩) (by omega) hZkeep ((hv₁ z).trans hZero)
      ⟨hNN,hNN,hNN⟩ (by simp [s₁,squarePairs,install,dL,rectangularLeftBase,rectangularRightBase,gOut])
      ((hvreg _ (by decide)).trans hTR) ((hvreg _ (by decide)).trans hUR) ((hvreg _ (by decide)).trans hZR)
      ((hvreg _ (by decide)).trans hRows) ((hvreg _ (by decide)).trans hCols)
      (by simp [s₁,squarePairs,install,gOut])
      (by simp [s₁,squarePairs,install,rectangularLeftBase,rectangularRightBase,gOut])
      (by simp [s₁,squarePairs,install,rectangularRightBase,gOut])
  have hState (r : String) (h₁ : r ∉ regNames canonical) (h₂ : r≠dI) (h₃ : r≠gU) (h₄ : r≠gV)
      (h₅ : r≠dO) (h : r ∉ [dL,rectangularLeftBase,rectangularRightBase,gOut]) : s₂.vars r=s.vars r :=
    (hVars r h₁ h₂ h₃ h₄ h₅).trans (hvreg r h)
  let tracePairs := [(gRows,n),(gCols,n),(dL,n),(gOut,o),(traceGridBase,square),(traceGridOne,one)]
  let s₃ := install tracePairs s₂
  have hSide' := (hState anchorSideWord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSide
  have eN := ev_var hSide' (show n < B by omega)
  have eO := ev_var ((hState anchorTraceWord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTraceW) (show o < B by omega)
  have eSq := ev_var ((hState anchorSquareWord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSquareW) (show square < B by omega)
  have eOne := ev_var ((hState anchorUnitWord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOneW) (show one < B by omega)
  have hs₃ : Run B (commands traceArgs) s₂ s₃ 13 := commands_run traceArgs [n,n,n,o,square,one] s₂
    rfl (.cons eN (.cons eN (.cons eN (.cons eO (.cons eSq (.cons eOne .nil))))))
    (by simp [traceArgs,NoVar,gRows,gCols,dL,gOut,traceGridBase,traceGridOne,
      anchorSideWord,anchorTraceWord,anchorSquareWord,anchorUnitWord])
  have s₃safe : ∀ p∈tracePairs, canonical.e≠p.1 ∧ canonical.p≠p.1 ∧ canonical.modBase≠p.1 ∧
      canonical.exp≠p.1 ∧ qN.WS≠p.1 := by
    intro p hp
    simp only [tracePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  obtain ⟨hS₃,hv₃,hi₃,ho₃⟩ := installedSlot F hS₂ tracePairs s₃safe
  have hOther (r : String) (h : r∉[gRows,gCols,dL,gOut,traceGridBase,traceGridOne]) : s₃.vars r=s₂.vars r :=
    installed_scalar tracePairs s₂ r (fun p hp e => h (by
      have hh : p.1 ∈ tracePairs.map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
      simpa [e,tracePairs] using hh))
  have hZ₃ : val F canonical qN.WS s₃ z=0 :=
    (hv₃ _).trans ((hKeep _ (by omega) hZkeep).trans ((hv₁ z).trans hZero))
  have hOne₃ : val F canonical qN.WS s₃ one=1 :=
    (hv₃ _).trans ((hKeep _ (by omega) (by unfold Written; omega)).trans ((hv₁ one).trans hUnit))
  have hFull (p q : Fin n × Fin n) : val F canonical qN.WS s₃ (square+(pairWordIndex p*(n*n)+pairWordIndex q)) =
      ((A ^ (2 : ℕ)) : Matrix (Fin n × Fin n) (Fin n × Fin n) K) p q := by
    rw [hv₃]
    have hp : pairWordIndex p < n*n := by rw [pairWordIndex_equiv]; exact (finProdFinEquiv p).isLt
    have hq : pairWordIndex q < n*n := by rw [pairWordIndex_equiv]; exact (finProdFinEquiv q).isLt
    rw [hSq _ hp _ hq,pow_two,Matrix.mul_apply,←Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ k : Fin (n*n), A p (finProdFinEquiv.symm k) * A (finProdFinEquiv.symm k) q := by
        apply Finset.sum_congr rfl
        intro k _
        have ek : pairWordIndex (finProdFinEquiv.symm k)=k.val := by rw [pairWordIndex_equiv,Equiv.apply_symm_apply]
        simp only [rightIndex,Bool.false_eq_true,if_false,←ek,hv₁,hMat]
      _ = _ := (finProdFinEquiv.symm : Fin (n*n) ≃ Fin n × Fin n).sum_comp (fun x => A p x * A x q)
  have htr (r : String) (h : r∉[gRows,gCols,dL,gOut,traceGridBase,traceGridOne])
      (h₁ : r ∉ regNames canonical) (h₂ : r≠dI) (h₃ : r≠gU) (h₄ : r≠gV) (h₅ : r≠dO)
      (h₆ : r ∉ [dL,rectangularLeftBase,rectangularRightBase,gOut]) : s₃.vars r=s.vars r :=
    (hOther r h).trans (hState r h₁ h₂ h₃ h₄ h₅ h₆)
  obtain ⟨t,ht,hSt,hv,hAfter,_,hi,ho⟩ := traceGrid_run F (A ^ (2 : ℕ)) hS₃ hN hSquare (hOut.trans (by omega))
    (by simp [s₃,tracePairs,install,gOut,traceGridBase,traceGridOne])
    (by simp [s₃,tracePairs,install,gRows,gCols,dL,gOut,traceGridBase,traceGridOne])
    (by simp [s₃,tracePairs,install,gCols,dL,gOut,traceGridBase,traceGridOne])
    (by simp [s₃,tracePairs,install,dL,gOut,traceGridBase,traceGridOne])
    ((htr dT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTR)
    ((htr dU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hUR)
    ((htr dZ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hZR)
    (by simp [s₃,tracePairs,install,traceGridBase,traceGridOne]) (by simp [s₃,tracePairs,install,traceGridOne])
    hOut hT.2 hU.2 hTU (by omega) (by omega) (by unfold Written; omega) (by unfold Written; omega)
    hZ₃ hOne₃ (fun i j a => hFull (a,i) (a,j))
  refine ⟨t,hs₁.seq (h₂.seq (hs₃.seq ht)),hSt,hv,?_,?_,hi.trans (hi₃.trans (hi₂.trans hi₁)),
    ho.trans (ho₃.trans (ho₂.trans ho₁))⟩
  · intro p q
    have hp : pairWordIndex p < n*n := by rw [pairWordIndex_equiv]; exact (finProdFinEquiv p).isLt
    have hq : pairWordIndex q < n*n := by rw [pairWordIndex_equiv]; exact (finProdFinEquiv q).isLt
    have hSlot := out_lt (o0:=square) hp hq
    have hSep : ¬ Written o n n tt uu (square+(pairWordIndex p*(n*n)+pairWordIndex q)) := by
      unfold Written
      omega
    exact (hAfter _ (hSlot.trans_le hSquare) hSep).trans (hFull p q)
  · intro k hk hsq htr
    exact (hAfter k hk htr).trans ((hv₃ k).trans ((hKeep k hk hsq).trans (hv₁ k)))

#print axioms squareTrace_run
end EvenTI.P16Execution