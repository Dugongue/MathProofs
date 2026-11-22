import EvenP19TrialHigherRecord
import EvenP16AnchorCosts

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 18000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep EvenTI.P12Compare
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16TrialNative EvenTI.P16Execution
open EvenTI.P18Trial (oppositeTraceCallCost)
open Lax13Proofs.Imp Lax51.BinaryWordEncoding Polynomial
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeFieldMacros20261001 (FieldMacros)
open Mathproof.P15RecogIMPGrid20261007 (gridCost)

variable {K : Type} [Field K] [Fintype K]

private noncomputable def sizePoly : Polynomial ℕ := (X+1)^2

private theorem sizePoly_eval (L : ℕ) : sizePoly.eval L=(L+1)*(L+1) := by
  simp [sizePoly,pow_two]

private theorem sizePoly_ge (L : ℕ) : L ≤ sizePoly.eval L ∧ 1 ≤ sizePoly.eval L := by
  rw [sizePoly_eval]
  have h := Nat.le_mul_of_pos_right (L+1) (show 0 < L+1 by omega)
  omega

private theorem gridOver (F : FieldPresentation K) (M : FieldMacros F canonical) (a b : Expr) :
    ∀ {i u w L : ℕ}, i ≤ sizePoly.eval L → u ≤ sizePoly.eval L → w ≤ sizePoly.eval L →
      gridCost M a b i u w ≤ (gridCostPolynomial M a b sizePoly sizePoly sizePoly).eval L := by
  intro i u w L hi hu hw
  rw [gridCostPolynomial_eval]
  exact gridCost_mono M a b hi hu hw

private theorem projectionOver (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {l n L : ℕ}, n*n ≤ sizePoly.eval L → n^(l+1) ≤ sizePoly.eval L →
      nativeProjectionGridCost F n (n^l) 1 ≤ p.eval L := by
  unfold nativeProjectionGridCost
  exact ⟨_, fun {l n L} hN hM =>
    gridOver F _ _ _ (i:=1) (u:=n*n) (w:=(1*n)*n^l)
      (sizePoly_ge L).2 hN (by simpa only [one_mul,←pow_succ'] using hM)⟩

private theorem rectangularOver (F : FieldPresentation K) (mirror : Bool) :
    ∃ p : Polynomial ℕ, ∀ {i u w L : ℕ}, i ≤ sizePoly.eval L → u ≤ sizePoly.eval L → w ≤ sizePoly.eval L →
      rectangularCost F mirror u i w ≤ p.eval L := by
  unfold rectangularCost
  exact ⟨gridCostPolynomial _ _ _ sizePoly sizePoly sizePoly,gridOver F _ _ _⟩

private theorem shuffleOver (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {n L : ℕ}, n*n ≤ sizePoly.eval L → crossShuffleCost F n n ≤ p.eval L := by
  unfold crossShuffleCost
  exact ⟨gridCostPolynomial _ _ _ sizePoly sizePoly sizePoly,
    fun {_ L} hN => gridOver F _ _ _ (sizePoly_ge L).2 hN hN⟩

private theorem leftTraceOver (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {n L : ℕ}, n ≤ sizePoly.eval L → traceLastGridCost F n ≤ p.eval L := by
  unfold traceLastGridCost
  exact ⟨gridCostPolynomial _ _ _ sizePoly sizePoly sizePoly,
    fun hN => gridOver F _ _ _ hN hN hN⟩

private theorem rightTraceOver (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {n L : ℕ}, n ≤ sizePoly.eval L → traceGridCost F n ≤ p.eval L := by
  unfold traceGridCost
  exact ⟨gridCostPolynomial _ _ _ sizePoly sizePoly sizePoly,
    fun hN => gridOver F _ _ _ hN hN hN⟩

private theorem modeOver (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {l n L : ℕ}, n≤L → n^(l+1)≤L →
      ∀ side, higherModeVisitCost F side l n ≤ p.eval L := by
  obtain ⟨P,hP⟩ := projectionOver F
  obtain ⟨U,hU⟩ := rectangularOver F true
  obtain ⟨V,hV⟩ := rectangularOver F false
  obtain ⟨S,hS⟩ := shuffleOver F
  obtain ⟨A,hA⟩ := leftTraceOver F
  obtain ⟨B,hB⟩ := rightTraceOver F
  refine ⟨C 200+C 2*P+U+C 2*V+S+A+B+C (emitFieldLabelCost F+16)*sizePoly,?_⟩
  intro l n L hn hm side
  have hN : n ≤ sizePoly.eval L := hn.trans (sizePoly_ge L).1
  have hM : n^(l+1) ≤ sizePoly.eval L := hm.trans (sizePoly_ge L).1
  have hN2 : n*n ≤ sizePoly.eval L := by
    rw [sizePoly_eval]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hp := hP (l:=l) hN2 hM
  have hu := hU hM hM hN2
  have hv := hV hM hN2 hN2
  have hSquare := hV hN2 hN2 hN2
  have hShuffle := hS hN2
  have ha := hA hN
  have hb := hB hN
  have he := Nat.mul_le_mul_left (emitFieldLabelCost F+16) hN2
  cases side <;> simp only [higherModeVisitCost,higherAnchorTailCost,higherContractionCost,
    contractionProductsCost,sideTraceRecordCost,squareTraceCost,oppositeTraceCallCost,emitAnchorBlockCost,
    Bool.false_eq_true,if_false,if_true,eval_add,eval_mul,eval_C] <;> omega

variable [DecidableEq K]

/-- Charge the complete installed higher trial record in the original pair
bits, including the projected grids, both sweeps and the two form writes. -/
theorem produceHigherTrial_originalBits (D : FieldEncoding K) (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n), 2≤n →
      produceHigherTrialCost F l n ≤ p.eval (bitSize (comparisonInput D T U)) := by
  obtain ⟨p,hp⟩ := modeOver F
  refine ⟨C 72+C 2*(p+C 12)*X+C 2*(C 24*X+C (26+emitFieldLabelCost F))*X,?_⟩
  intro l n T U hn
  let L := bitSize (comparisonInput D T U)
  obtain ⟨hN,hM,hL⟩ := cutInput_side_bounds D T U (by omega : 1≤l+1) hn
  have hnL : n≤L := hN.trans hM
  have hmL : n^(l+1)≤L := hM
  have hlL : l+1≤L := hL
  have hA : higherModeVisitCost F false l n+12 ≤ p.eval L+12 :=
    Nat.add_le_add_right (hp hnL hmL false) 12
  have hB : higherModeVisitCost F true l n+12 ≤ p.eval L+12 :=
    Nat.add_le_add_right (hp hnL hmL true) 12
  have ha := Nat.mul_le_mul hA hlL
  have hb := Nat.mul_le_mul hB hlL
  have hConst : 24*(l+1)+26+emitFieldLabelCost F ≤ 24*L+26+emitFieldLabelCost F := by omega
  have hEmit := Nat.mul_le_mul hConst hmL
  simp only [Nat.add_assoc] at hEmit
  change produceHigherTrialCost F l n ≤ (C 72+C 2*(p+C 12)*X+C 2*(C 24*X+C (26+emitFieldLabelCost F))*X).eval L
  simp only [produceHigherTrialCost,emitInstalledHigherFormCost,emitHigherFormCost,
    eval_add,eval_mul,eval_C,eval_X,Nat.mul_assoc,Nat.add_assoc]
  rw [two_mul, two_mul]
  omega

#print axioms produceHigherTrial_originalBits
end EvenTI.P19Trial



