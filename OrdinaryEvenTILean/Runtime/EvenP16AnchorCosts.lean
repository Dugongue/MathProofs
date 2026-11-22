import EvenP16AnchorCrossGrid
import EvenP16AnchorSquareTrace
import EvenP14CutRawSetup
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false

namespace EvenTI.P16Execution

open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeFieldMacros20261001 (FieldMacros)
open Mathproof.P15RecogIMPDot20261007
open Mathproof.P15RecogIMPGrid20261007
open EvenTI.P16Trial Polynomial

variable {K : Type} [Field K] [Fintype K] {F : FieldPresentation K}

/-- Each installed grid command has the same polynomial cost expression
regardless of the tensor order that produced its arguments. -/
noncomputable def gridCostPolynomial (M : FieldMacros F canonical) (a b : Expr)
    (l u w : Polynomial ℕ) : Polynomial ℕ :=
  C 6+(C 14+(C (40+M.costPoint)+C (4+dotStep M a b)*l)*w)*u

theorem gridCostPolynomial_eval (M : FieldMacros F canonical) (a b : Expr)
    (l u w : Polynomial ℕ) (x : ℕ) :
    (gridCostPolynomial M a b l u w).eval x = gridCost M a b (l.eval x) (u.eval x) (w.eval x) := by
  simp only [gridCostPolynomial,eval_add,eval_mul,eval_C,gridCost,rowStep,innerStep,dotCost]
  ring

theorem gridCost_mono (M : FieldMacros F canonical) (a b : Expr) {l u w l' u' w' : ℕ}
    (hl : l ≤ l') (hu : u ≤ u') (hw : w ≤ w') : gridCost M a b l u w ≤ gridCost M a b l' u' w' := by
  unfold gridCost rowStep innerStep dotCost
  gcongr

private theorem allSquareBudget (M : FieldMacros F canonical) (a b : Expr) :
    ∃ p : Polynomial ℕ, ∀ L : ℕ, gridCost M a b (L*L) (L*L) (L*L)=p.eval L := by
  refine ⟨gridCostPolynomial M a b (X*X) (X*X) (X*X),fun L => ?_⟩
  rw [gridCostPolynomial_eval]
  simp

private theorem allLinearBudget (M : FieldMacros F canonical) (a b : Expr) :
    ∃ p : Polynomial ℕ, ∀ L : ℕ, gridCost M a b L L L=p.eval L := by
  refine ⟨gridCostPolynomial M a b X X X,fun L => ?_⟩
  rw [gridCostPolynomial_eval]
  simp

/-- One polynomial in the original bit length bounds the entire crossed,
square and trace calculation once the two physical dimensions are bounded
by that original length. No tensor-order exponent enters this polynomial. -/
theorem anchorGrid_polyBudget (F : FieldPresentation K) (mirror : Bool) :
    ∃ p : Polynomial ℕ, ∀ {n a L : ℕ}, n ≤ L → a ≤ L →
      crossGridCost F mirror n a+squareTraceCost F n ≤ p.eval L := by
  have hCross : ∃ p : Polynomial ℕ, ∀ L : ℕ, crossGridCost F mirror L L=p.eval L := by
    unfold crossGridCost
    exact allSquareBudget _ _ _
  have hSquare : ∃ p : Polynomial ℕ, ∀ L : ℕ, rectangularCost F false (L*L) (L*L) (L*L)=p.eval L := by
    unfold rectangularCost
    exact allSquareBudget _ _ _
  have hTrace : ∃ p : Polynomial ℕ, ∀ L : ℕ, traceGridCost F L=p.eval L := by
    unfold traceGridCost
    exact allLinearBudget _ _ _
  obtain ⟨p,hp⟩ := hCross
  obtain ⟨q,hq⟩ := hSquare
  obtain ⟨r,hr⟩ := hTrace
  refine ⟨p+(C 9+(q+(C 13+r))),?_⟩
  intro n a L hn ha
  have h1 : crossGridCost F mirror n a ≤ crossGridCost F mirror L L := by
    unfold crossGridCost
    exact gridCost_mono _ _ _ (Nat.mul_le_mul ha ha) (Nat.mul_le_mul hn hn) (Nat.mul_le_mul hn hn)
  have h2 : rectangularCost F false (n*n) (n*n) (n*n) ≤ rectangularCost F false (L*L) (L*L) (L*L) := by
    unfold rectangularCost
    exact gridCost_mono _ _ _ (Nat.mul_le_mul hn hn) (Nat.mul_le_mul hn hn) (Nat.mul_le_mul hn hn)
  have h3 : traceGridCost F n ≤ traceGridCost F L := by
    unfold traceGridCost
    exact gridCost_mono _ _ _ hn hn hn
  simp only [eval_add,eval_C,←hp L,←hq L,←hr L,squareTraceCost]
  omega

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep Lax51.BinaryWordEncoding in
/-- The bound in the literal input length of the balanced tensor pair. -/
theorem anchorGrid_originalBitBudget [DecidableEq K] (D : FieldEncoding K)
    (F : FieldPresentation K) (mirror : Bool) :
    ∃ p : Polynomial ℕ, ∀ {l n : ℕ} (T S : Tensor K ((l+1)+(l+1)) n), 2 ≤ n →
      crossGridCost F mirror n (n^l)+squareTraceCost F n ≤ p.eval (bitSize (comparisonInput D T S)) := by
  obtain ⟨p,hp⟩ := anchorGrid_polyBudget F mirror
  refine ⟨p,?_⟩
  intro l n T S hn
  have h := cutInput_side_bounds D T S (by omega : 1 ≤ l+1) hn
  exact hp (h.1.trans h.2.1) ((Nat.pow_le_pow_right (by omega) (Nat.le_succ l)).trans h.2.1)

#print axioms anchorGrid_originalBitBudget
#print axioms anchorGrid_polyBudget
end EvenTI.P16Execution