import Mathlib.Data.Matrix.Basis

namespace LazardClassReduction

def commutator {B : Type*} [Ring B] (x y : B) : B := x * y - y * x

def alternating {B : Type*} [Ring B] (u v : B × B) : B :=
  u.1 * v.2 - v.1 * u.2

theorem adjoint_blocks {B : Type*} [Ring B]
    (P Q U V P' Q' U' V' : B → B)
    (h : ∀ x y x' y',
      alternating (P x + Q y, U x + V y) (x', y') =
        alternating (x, y) (P' x' + Q' y', U' x' + V' y'))
    (h0 : P 0 = 0 ∧ Q 0 = 0 ∧ U 0 = 0 ∧ V 0 = 0 ∧
      P' 0 = 0 ∧ Q' 0 = 0 ∧ U' 0 = 0 ∧ V' 0 = 0) :
    (∀ x, P x = x * V' 1) ∧ (∀ y, V' y = V' 1 * y) ∧
    (∀ x, P' x = x * V 1) ∧ (∀ y, V y = V 1 * y) ∧
    (∀ y, Q y = Q 1 * y) ∧ (∀ y, Q' y = -(Q 1 * y)) ∧
    (∀ x, U x = x * U 1) ∧ (∀ x, U' x = -(x * U 1)) ∧
    (∀ x y, Q 1 * commutator x y = 0) ∧
    (∀ x y, commutator x y * U 1 = 0) := by
  obtain ⟨hP0, hQ0, hU0, hV0, hP'0, hQ'0, hU'0, hV'0⟩ := h0
  have hPV : ∀ x y, P x * y = x * V' y := by
    intro x y
    simpa [alternating, hQ0, hV0, hP'0, hU'0] using h x 0 0 y
  have hVP : ∀ x y, x * V y = P' x * y := by
    intro x y
    simpa [alternating, hP0, hU0, hQ'0, hV'0] using h 0 y x 0
  have hQ : ∀ y z, Q y * z = -(Q' z * y) := by
    intro y z
    simpa [alternating, hP0, hU0, hP'0, hU'0] using h 0 y 0 z
  have hU : ∀ x z, -(z * U x) = x * U' z := by
    intro x z
    simpa [alternating, hQ0, hV0, hQ'0, hV'0] using h x 0 z 0
  have hP (x) : P x = x * V' 1 := by simpa using hPV x 1
  have hV' (y) : V' y = V' 1 * y := by
    simpa [hP] using (hPV 1 y).symm
  have hP' (x) : P' x = x * V 1 := by simpa using (hVP x 1).symm
  have hV (y) : V y = V 1 * y := by simpa [hP'] using hVP 1 y
  have hQ' (y) : Q' y = -(Q 1 * y) := by
    have hh := hQ 1 y
    simpa using (congrArg Neg.neg hh).symm
  have hQm (y) : Q y = Q 1 * y := by simpa [hQ'] using hQ y 1
  have hU' (x) : U' x = -(x * U 1) := by simpa using (hU 1 x).symm
  have hUm (x) : U x = x * U 1 := by
    simpa [hU'] using hU x 1
  refine ⟨hP, hV', hP', hV, hQm, hQ', hUm, hU', ?_, ?_⟩
  · intro x y
    have hh := hQ x y
    rw [hQm x, hQ' y, neg_mul, neg_neg] at hh
    simpa only [commutator, mul_sub, sub_eq_zero, mul_assoc] using hh
  · intro x y
    have hh := hU y x
    rw [hUm y, hU' x, mul_neg, neg_inj] at hh
    simpa only [commutator, sub_mul, sub_eq_zero, mul_assoc] using hh

theorem matrix_commutator_annihilator_left {A : Type*} [Ring A]
    (C : Matrix (Fin 2) (Fin 2) A)
    (h : ∀ X Y, C * commutator X Y = 0) : C = 0 := by
  have h01 : C * Matrix.single (0 : Fin 2) (1 : Fin 2) 1 = 0 := by
    simpa [commutator, show (1 : Fin 2) ≠ 0 by decide] using
      h (Matrix.single 0 0 1) (Matrix.single 0 1 1)
  have h10 : C * Matrix.single (1 : Fin 2) (0 : Fin 2) 1 = 0 := by
    simpa [commutator, show (0 : Fin 2) ≠ 1 by decide] using
      h (Matrix.single 1 1 1) (Matrix.single 1 0 1)
  ext i j
  fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M i 1) h01
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M i 0) h10

theorem matrix_commutator_annihilator_right {A : Type*} [Ring A]
    (C : Matrix (Fin 2) (Fin 2) A)
    (h : ∀ X Y, commutator X Y * C = 0) : C = 0 := by
  have h01 : Matrix.single (0 : Fin 2) (1 : Fin 2) 1 * C = 0 := by
    simpa [commutator, show (1 : Fin 2) ≠ 0 by decide] using
      h (Matrix.single 0 0 1) (Matrix.single 0 1 1)
  have h10 : Matrix.single (1 : Fin 2) (0 : Fin 2) 1 * C = 0 := by
    simpa [commutator, show (0 : Fin 2) ≠ 1 by decide] using
      h (Matrix.single 1 1 1) (Matrix.single 1 0 1)
  ext i j
  fin_cases i
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 j) h10
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 j) h01

theorem normalize_operation {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (source : E → E → E) (target : F →ₗ[R] F →ₗ[R] F)
    (X Y Z : E →ₗ[R] F) (a b : Rˣ)
    (hx : ∀ x, Z x = (a : R) • X x)
    (hy : ∀ y, Z y = (b : R) • Y y)
    (h : ∀ x y, Z (source x y) = target (X x) (Y y)) :
    ∀ x y, ((a * b)⁻¹ : Rˣ) • Z (source x y) =
      target (((a * b)⁻¹ : Rˣ) • Z x) (((a * b)⁻¹ : Rˣ) • Z y) := by
  intro x y
  have h₁ : ((a * b)⁻¹ : Rˣ) • Z x = b⁻¹ • X x := by
    rw [hx x, ← Units.smul_def, smul_smul, mul_inv_rev, mul_assoc,
      inv_mul_cancel, mul_one]
  have h₂ : ((a * b)⁻¹ : Rˣ) • Z y = a⁻¹ • Y y := by
    rw [hy y, ← Units.smul_def, smul_smul, mul_comm a b, mul_inv_rev, mul_assoc,
      inv_mul_cancel, mul_one]
  rw [h₁, h₂, h]
  simp only [Units.smul_def, map_smul, LinearMap.smul_apply, smul_smul]
  rw [← Units.val_mul, mul_comm a b, mul_inv_rev]

end LazardClassReduction

#print axioms LazardClassReduction.adjoint_blocks
#print axioms LazardClassReduction.matrix_commutator_annihilator_left
#print axioms LazardClassReduction.matrix_commutator_annihilator_right
#print axioms LazardClassReduction.normalize_operation
