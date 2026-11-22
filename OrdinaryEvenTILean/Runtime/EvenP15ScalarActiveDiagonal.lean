import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import EvenP8PaddedSupport
import EvenP6LiveCellsAction

set_option autoImplicit false

namespace EvenTI.P15Scalar

open Matrix

variable {K I J : Type} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A full-rank invariant restriction of a diagonal action is scalar
exactly when every row meeting the restricted subspace has the same
diagonal value. Inactive rows impose no condition. -/
theorem scalarRestriction_iff_activeDiagonal
    (P : Matrix I J K) (Q : Matrix J I K) (A : Matrix J J K)
    (lambda : I → K) (s : K) (hLeft : Q * P = 1)
    (hInvariant : Matrix.diagonal lambda * P = P * A) :
    A = s • (1 : Matrix J J K) ↔
      ∀ i, (∃ j, P i j ≠ 0) → lambda i = s := by
  have hMul : P * (s • (1 : Matrix J J K)) = s • P := by
    rw [Matrix.mul_smul,Matrix.mul_one]
  constructor
  · intro hA i hi
    obtain ⟨j,hj⟩ := hi
    have he : Matrix.diagonal lambda * P = s • P :=
      hInvariant.trans ((congrArg (P * ·) hA).trans hMul)
    have hEntry := congrFun (congrFun he i) j
    rw [Matrix.diagonal_mul,Matrix.smul_apply] at hEntry
    have hz : (lambda i-s)*P i j = 0 := by
      rw [sub_mul,hEntry,smul_eq_mul,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hj)
  · intro h
    have hb : Matrix.diagonal lambda * P = s • P := by
      ext i j
      by_cases hZero : P i j = 0
      · simp [Matrix.diagonal_mul,Matrix.smul_apply,hZero]
      · simp [Matrix.diagonal_mul,Matrix.smul_apply,h i ⟨j,hZero⟩,smul_eq_mul]
    have hc : P * A = P * (s • (1 : Matrix J J K)) :=
      hInvariant.symm.trans (hb.trans hMul.symm)
    have hd := congrArg (Q * ·) hc
    simpa only [← Matrix.mul_assoc,hLeft,one_mul] using hd

/-- Apply the criterion directly to a charted diagonal action on a
split padding subspace. The active row pattern depends only on the
source chart and the padding and is shared by all homogeneous actions. -/
theorem scalarCrop_iff_activeChartRows
    (P : Matrix I J K) (Q : Matrix J I K) (N : Matrix I I K)
    (U : (Matrix I I K)ˣ) (lambda : I → K) (s : K)
    (hLeft : Q * P = 1) (hConj : N = U.val * Matrix.diagonal lambda * U.inv)
    (hInvariant : N*P = P*(Q*N*P)) :
    Q*N*P = s • (1 : Matrix J J K) ↔
      ∀ i, (∃ j, (U.inv*P) i j ≠ 0) → lambda i = s := by
  have hLeftChart : (Q*U.val)*(U.inv*P) = 1 := by
    calc
      (Q*U.val)*(U.inv*P) = Q*((U.val*U.inv)*P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [U.val_inv,Matrix.one_mul,hLeft]
  have hInterChart : Matrix.diagonal lambda*(U.inv*P) = (U.inv*P)*(Q*N*P) := by
    calc
      Matrix.diagonal lambda*(U.inv*P) = U.inv*(N*P) := by
        rw [hConj]
        symm
        calc
          U.inv*((U.val*Matrix.diagonal lambda*U.inv)*P) =
              (U.inv*U.val)*(Matrix.diagonal lambda*(U.inv*P)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [U.inv_val,Matrix.one_mul]
      _ = U.inv*(P*(Q*N*P)) := congrArg (U.inv*·) hInvariant
      _ = (U.inv*P)*(Q*N*P) := (Matrix.mul_assoc _ _ _).symm
  exact scalarRestriction_iff_activeDiagonal (U.inv*P) (Q*U.val) (Q*N*P)
    lambda s hLeftChart hInterChart

#print axioms scalarCrop_iff_activeChartRows

section PaddedSource

open EvenTI.CellPreparation

variable {d n : ℕ} {V : Fin d → Type}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- The full retained-rank padding theorem supplies the precise
invariance premise for the active-row scalar criterion. -/
theorem scalarPaddedMode_iff_activeChartRows
    (P : ∀ i, Matrix (V i) (Fin n) K) (Q : ∀ i, Matrix (Fin n) (V i) K)
    (G : ∀ i, Matrix (V i) (V i) K)
    (hLeft : ∀ i, Q i * P i = 1)
    (T : Grid K (fun _ : Fin d => Fin n))
    (hFix : rectGridAction G (rectGridAction P T) = rectGridAction P T)
    (hFull : ∀ M, wordAction M T = T → ∀ i, IsUnit (M i))
    (i : Fin d) (U : (Matrix (V i) (V i) K)ˣ)
    (lambda : V i → K) (s : K) (hConj : G i = U.val * Matrix.diagonal lambda * U.inv) :
    Q i * G i * P i = s • (1 : Matrix (Fin n) (Fin n) K) ↔
      ∀ j, (∃ k, (U.inv * P i) j k ≠ 0) → lambda j = s := by
  have hInter := padding_support_of_full_target P P Q G hLeft T T hFix hFull i
  exact scalarCrop_iff_activeChartRows (P i) (Q i) (G i) U lambda s (hLeft i) hConj hInter

#print axioms scalarPaddedMode_iff_activeChartRows
end PaddedSource

section NativeBlocks

open EvenTI.CellPreparation EvenTI.CellProducer

variable {d : ℕ} {width : Fin d → ℕ}
  {D : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Fintype (D i v)] [∀ i v, DecidableEq (D i v)]
  {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]

/-- Base-field multipliers are genuinely diagonal in the compiled native
block basis, with one repeated value per block. -/
theorem liveActionMatrix_baseScalars
    (t : ∀ i v, WordTable K (D i v))
    (P : ∀ i v, (D i v → K) ≃ₗ[K] X i v)
    (hMul : ∀ i v a b, P i v ((t i v).multiply a b) = P i v a * P i v b)
    (i : Fin d) (lambda : Fin (width i) → K) :
    liveActionMatrix t P i (fun v => algebraMap K (X i v) (lambda v)) =
      Matrix.diagonal (fun p : LiveModeIndex D i => lambda p.1) := by
  ext p q
  let x : D i p.1 → K := fun k => (Pi.single (M:=fun _ : LiveModeIndex D i => K) q 1) ⟨p.1,k⟩
  have hBlock :
      (t i p.1).multiply ((P i p.1).symm (algebraMap K (X i p.1) (lambda p.1))) x =
        lambda p.1 • x := by
    apply (P i p.1).injective
    rw [hMul,LinearEquiv.apply_symm_apply,map_smul,Algebra.smul_def]
  change (t i p.1).multiply ((P i p.1).symm (algebraMap K (X i p.1) (lambda p.1))) x p.2 = _
  rw [hBlock]
  change lambda p.1 * (Pi.single (M:=fun _ : LiveModeIndex D i => K) q 1) p = _
  by_cases h : p = q
  · subst q
    simp
  · simp [Pi.single_eq_of_ne h,Matrix.diagonal_apply_ne _ h]

#print axioms liveActionMatrix_baseScalars
end NativeBlocks

#print axioms scalarRestriction_iff_activeDiagonal
end EvenTI.P15Scalar