import EvenP2FormsRank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The singular form selector succeeds away from a small exceptional event. -/
namespace Mathproof.EvenTI.Singular.Forms

open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne
open EvenTI.Action Matrix Module
open scoped BigOperators Matrix

noncomputable section

variable {X A : Type*} [Fintype X] [Fintype A] [Zero X]

/-- For a uniform family of maps whose zero event for any given nonzero
vector is (1/|X|), finding a bad nonzero vector in the kernel is as rare
as sampling a bad vector of the ambient space. -/
theorem uniformFraction_bad_kernel_le (bad : X → Prop) (hit : A → X → Prop)
    (hf : ∀ x : X, x ≠ 0 → uniformFraction A (fun a => hit a x) = 1 / (Fintype.card X : ℝ)) :
    uniformFraction A (fun a => ∃ x : X, x ≠ 0 ∧ hit a x ∧ bad x) ≤
      uniformFraction X bad := by
  classical
  let B := {x : X // x ≠ 0 ∧ bad x}
  have hcard : Fintype.card B ≤ Nat.card {x : X // bad x} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective
      (fun x : B => (⟨x.val, x.property.2⟩ : {x : X // bad x}))
      (fun _ _ e => Subtype.ext (congrArg (fun y : {x : X // bad x} => y.val) e))
  calc
    _ ≤ uniformFraction A (fun a => ∃ x : B, hit a x.val) :=
      uniformFraction_le_of_imp (by rintro a ⟨x, hx, hh, hb⟩; exact ⟨⟨x, hx, hb⟩, hh⟩)
    _ ≤ ∑ x : B, uniformFraction A (fun a => hit a x.val) := uniformFraction_exists_le _
    _ = (Fintype.card B : ℝ) / Fintype.card X := by
      simp [show ∀ x : B, uniformFraction A (fun a => hit a x.val) = 1 / (Fintype.card X : ℝ)
        from fun x => hf x.val x.property.1, div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ _ := by
      unfold uniformFraction
      rw [Nat.card_eq_fintype_card (α := X)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

variable {K : Type*} [Field K] [Fintype K] {l n : ℕ}

abbrev BadRetained (x : Coord (l+1) n → K) : Prop :=
  ∃ i, (retainedForm i x).rank ≠ n

abbrev BadRightForm (T : Tensor K ((l+1)+(l+1)) n) : Prop :=
  ∃ x : Coord (l+1) n → K, x ≠ 0 ∧ rightCutKernel T x = 0 ∧ BadRetained x

abbrev BadLeftForm (T : Tensor K ((l+1)+(l+1)) n) : Prop :=
  ∃ x : Coord (l+1) n → K, x ≠ 0 ∧ leftCutKernel T x = 0 ∧ BadRetained x

private theorem formCard :
    (Fintype.card (Coord (l+1) n → K) : ℝ) = (Fintype.card K : ℝ) ^ n^(l+1) := by
  rw [Fintype.card_fun, cut_side_card, Nat.cast_pow]

theorem rightForms_bad_fraction :
    uniformFraction (Tensor K ((l+1)+(l+1)) n) BadRightForm ≤
      (l+1 : ℝ) * ((Fintype.card K : ℝ)^n / (Fintype.card K : ℝ)^(n^l)) := by
  have hx (x : Coord (l+1) n → K) (hnz : x ≠ 0) :
      uniformFraction (Tensor K ((l+1)+(l+1)) n) (fun T => rightCutKernel T x = 0) =
        1 / (Fintype.card (Coord (l+1) n → K) : ℝ) := by
    rw [rightCutKernel_zero_fraction x hnz, formCard]
  exact (uniformFraction_bad_kernel_le BadRetained (fun T x => rightCutKernel T x = 0) hx).trans
    all_retained_bad_fraction

theorem leftForms_bad_fraction :
    uniformFraction (Tensor K ((l+1)+(l+1)) n) BadLeftForm ≤
      (l+1 : ℝ) * ((Fintype.card K : ℝ)^n / (Fintype.card K : ℝ)^(n^l)) := by
  have hx (x : Coord (l+1) n → K) (hnz : x ≠ 0) :
      uniformFraction (Tensor K ((l+1)+(l+1)) n) (fun T => leftCutKernel T x = 0) =
        1 / (Fintype.card (Coord (l+1) n → K) : ℝ) := by
    rw [leftCutKernel_zero_fraction x hnz, formCard]
  exact (uniformFraction_bad_kernel_le BadRetained (fun T x => leftCutKernel T x = 0) hx).trans
    all_retained_bad_fraction

private theorem exponent_sufficient {n l : ℕ} (hn : 3 ≤ n) (hl : 2 ≤ l) :
    2*n+l ≤ n^l := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hl
  subst l
  induction t with
  | zero =>
    have hm := Nat.mul_le_mul_left n hn
    simp only [Nat.add_zero, pow_two]
    omega
  | succ t ih =>
    rw [Nat.add_succ, pow_succ]
    have hm : n^(2+t) * 2 ≤ n^(2+t) * n :=
      Nat.mul_le_mul_left _ (by omega)
    have hlarge : 2*n+(2+t)+1 ≤ n^(2+t) * 2 := by omega
    exact hlarge.trans hm

theorem retained_bound_uniform (q : ℝ) (hq : 2 ≤ q) {n l : ℕ} (hn : 3 ≤ n) (hl : 2 ≤ l) :
    (l+1 : ℝ) * (q^n / q^(n^l)) ≤ 1 / q^n := by
  have hq0 : 0 < q := by linarith
  have hdim : n+l+n ≤ n^l := by
    have := exponent_sufficient hn hl
    omega
  have ht : (l+1 : ℝ) ≤ q^l := by
    calc
      _ ≤ (2:ℝ)^l := by exact_mod_cast (show l+1 ≤ (2:ℕ)^l from l.lt_two_pow_self)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hq _
  apply (le_div_iff₀ (pow_pos hq0 _)).mpr
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_one (pow_pos hq0 _)).mpr
  calc
    _ ≤ (q^l * q^n) * q^n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)
    _ = q^(n+l+n) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hdim

theorem badRightForm_fraction_uniform (hn : 3 ≤ n) (hl : 2 ≤ l) :
    uniformFraction (Tensor K ((l+1)+(l+1)) n) BadRightForm ≤ 1 / (Fintype.card K : ℝ)^n :=
  rightForms_bad_fraction.trans (retained_bound_uniform (Fintype.card K)
    (by exact_mod_cast (Fintype.one_lt_card (α := K))) hn hl)

theorem badLeftForm_fraction_uniform (hn : 3 ≤ n) (hl : 2 ≤ l) :
    uniformFraction (Tensor K ((l+1)+(l+1)) n) BadLeftForm ≤ 1 / (Fintype.card K : ℝ)^n :=
  leftForms_bad_fraction.trans (retained_bound_uniform (Fintype.card K)
    (by exact_mod_cast (Fintype.one_lt_card (α := K))) hn hl)

theorem goodRight_of_not_bad (T : Tensor K ((l+1)+(l+1)) n) (h : ¬ BadRightForm T)
    (x : Coord (l+1) n → K) (hnz : x ≠ 0) (hx : rightCutKernel T x = 0) :
    ∀ i, (retainedForm i x).rank = n := by
  intro i
  by_contra hi
  exact h ⟨x, hnz, hx, i, hi⟩

theorem goodLeft_of_not_bad (T : Tensor K ((l+1)+(l+1)) n) (h : ¬ BadLeftForm T)
    (x : Coord (l+1) n → K) (hnz : x ≠ 0) (hx : leftCutKernel T x = 0) :
    ∀ i, (retainedForm i x).rank = n := by
  intro i
  by_contra hi
  exact h ⟨x, hnz, hx, i, hi⟩

theorem singular_good_forms (T : Tensor K ((l+1)+(l+1)) n)
    (hs : (flatten T).det = 0) (hL : ¬ BadLeftForm T) (hR : ¬ BadRightForm T) :
    ∃ ell rho : Coord (l+1) n → K,
      ell ≠ 0 ∧ leftCutKernel T ell = 0 ∧ (∀ i, (retainedForm i ell).rank = n) ∧
      rho ≠ 0 ∧ rightCutKernel T rho = 0 ∧ (∀ j, (retainedForm j rho).rank = n) := by
  obtain ⟨ell, hell, heq⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (flatten T)ᵀ)).mpr
    (by rwa [Matrix.det_transpose])
  obtain ⟨rho, hrho, hrq⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := flatten T)).mpr hs
  exact ⟨ell, rho, hell, heq, goodLeft_of_not_bad T hL ell hell heq,
    hrho, hrq, goodRight_of_not_bad T hR rho hrho hrq⟩

#print axioms badRightForm_fraction_uniform
#print axioms badLeftForm_fraction_uniform
#print axioms goodRight_of_not_bad
#print axioms goodLeft_of_not_bad
#print axioms singular_good_forms

end
end Mathproof.EvenTI.Singular.Forms
