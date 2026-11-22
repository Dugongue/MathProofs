import EvenP16AnchorCosts

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep
open Lax51.BinaryWordEncoding
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def anchorWordExponent (F : FieldPresentation K) : Polynomial ℕ :=
  cutWordPoly F + C (Fintype.card K) * (X^2 + X + C 2)

/-- The exact powered-inverse requirement and all grid counters fit in a
word whose number of bits is polynomial in the original dense input size.
The same word capacity also accommodates the existing raw cut setup. -/
theorem anchorWordExponent_bounds (D : FieldEncoding K) (F : FieldPresentation K)
    {l n : ℕ} (T S : Tensor K ((l+1)+(l+1)) n) (hn : 2 ≤ n) :
    let L := bitSize (comparisonInput D T S)
    let B : ℕ := 2^((anchorWordExponent F).eval L+L+1)
    (cutWordPoly F).eval L ≤ B ∧
    Fintype.card K^((n*n^l)*(n*n^l)+n*n^l+2) < B ∧
    4 < B ∧ Fintype.card K ≤ B ∧ n+1 < B ∧ n*n+1 < B ∧ (n^l)*(n^l)+1 < B := by
  dsimp only
  let L := bitSize (comparisonInput D T S)
  let a := n^l
  let m := n*a
  let q := Fintype.card K
  let b := (anchorWordExponent F).eval L+L+1
  change (cutWordPoly F).eval L ≤ 2^b ∧ q^(m*m+m+2) < 2^b ∧
    4 < 2^b ∧ q ≤ 2^b ∧ n+1 < 2^b ∧ n*n+1 < 2^b ∧ a*a+1 < 2^b
  have hDim := cutInput_side_bounds D T S (show 1 ≤ l+1 by omega) hn
  have hML : m ≤ L := by
    simpa only [m,a,pow_succ'] using hDim.2.1
  have hNM : n ≤ m := by
    simpa only [m,a,pow_succ'] using hDim.1
  have hAM : a ≤ m := by
    dsimp only [m]
    exact Nat.le_mul_of_pos_left a (by omega)
  have hExp : q*(m*m+m+2) < b := by
    have hMM := Nat.mul_le_mul hML hML
    have hh : m*m+m+2 ≤ L*L+L+2 := by omega
    have h := Nat.mul_le_mul_left q hh
    simp only [b,anchorWordExponent,eval_add,eval_mul,eval_C,eval_X,pow_two]
    change q*(m*m+m+2) < (cutWordPoly F).eval L+q*(L*L+L+2)+L+1
    omega
  have hP : (cutWordPoly F).eval L ≤ b := by
    simp only [b,anchorWordExponent,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    omega
  have hQ : q < b := by
    have h := Nat.le_mul_of_pos_right q (show 0 < m*m+m+2 by omega)
    omega
  have hAux : (m+q+1)*(m+q+1) < (cutWordPoly F).eval L := cutWordBudget_choice F hML
  have hAddN : n+1 < b := by
    have h := Nat.le_mul_of_pos_right (m+q+1) (show 0 < m+q+1 by omega)
    omega
  have hM2 : m*m+1 < b := by
    have hSh : m ≤ m+q+1 := by omega
    have hh := Nat.mul_lt_mul_of_pos_left (show m < m+q+1 by omega) (show 0 < m by omega)
    have h := hh.trans_le (Nat.mul_le_mul_right (m+q+1) hSh)
    omega
  have hFour : 4 < b := by
    have hnm := Nat.mul_le_mul (show 2 ≤ m by omega) (show 2 ≤ m by omega)
    norm_num at hnm
    omega
  have hB : b < 2^b := Nat.lt_two_pow_self
  refine ⟨by omega,?_,by omega,by omega,by omega,?_,?_⟩
  · have h1 : q^(m*m+m+2) ≤ (2^q)^(m*m+m+2) :=
      Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=q)).le _
    rw [←pow_mul] at h1
    exact h1.trans_lt (Nat.pow_lt_pow_right (by decide) hExp)
  · have h := Nat.mul_le_mul hNM hNM
    omega
  · have h := Nat.mul_le_mul hAM hAM
    omega

#print axioms anchorWordExponent_bounds
end EvenTI.P16Execution
