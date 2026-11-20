import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Partial traces extracted from the Problem 1.8 formalization and the
conjugacy argument from the order-four quadratic covariants. The narrow
imports allow both singular and reciprocal anchor drivers to reuse them. -/
namespace EvenTI.AnchorCovariance

open scoped BigOperators TensorProduct Matrix
open Matrix

variable {K i j : Type*} [Field K] [Fintype i] [Fintype j]

def partialTraceLeft : Matrix (i × j) (i × j) K →ₗ[K] Matrix i i K where
  toFun X a b := ∑ c, X (a,c) (b,c)
  map_add' X Y := by
    ext a b
    change (∑ c, (X (a,c) (b,c) + Y (a,c) (b,c))) =
      (∑ c, X (a,c) (b,c)) + ∑ c, Y (a,c) (b,c)
    rw [Finset.sum_add_distrib]
  map_smul' k X := by
    ext a b
    change (∑ c, k * X (a,c) (b,c)) = k * ∑ c, X (a,c) (b,c)
    rw [Finset.mul_sum]

def partialTraceRight : Matrix (i × j) (i × j) K →ₗ[K] Matrix j j K where
  toFun X a b := ∑ c, X (c,a) (c,b)
  map_add' X Y := by
    ext a b
    change (∑ c, (X (c,a) (c,b) + Y (c,a) (c,b))) =
      (∑ c, X (c,a) (c,b)) + ∑ c, Y (c,a) (c,b)
    rw [Finset.sum_add_distrib]
  map_smul' k X := by
    ext a b
    change (∑ c, k * X (c,a) (c,b)) = k * ∑ c, X (c,a) (c,b)
    rw [Finset.mul_sum]

omit [Fintype i] in
theorem partialTraceLeft_kronecker (M : Matrix i i K) (N : Matrix j j K) :
    partialTraceLeft (Matrix.kronecker M N) = Matrix.trace N • M := by
  ext a b
  change (∑ c, M a b * N c c) = (∑ c, N c c) * M a b
  rw [← Finset.mul_sum, mul_comm]

omit [Fintype j] in
theorem partialTraceRight_kronecker (M : Matrix i i K) (N : Matrix j j K) :
    partialTraceRight (Matrix.kronecker M N) = Matrix.trace M • N := by
  ext a b
  change (∑ c, M c c * N a b) = (∑ c, M c c) * N a b
  rw [Finset.sum_mul]

variable [DecidableEq i] [DecidableEq j]

theorem trace_sim (M P Q : Matrix i i K) (h : Q * P = 1) :
    Matrix.trace (P * M * Q) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle, h, Matrix.one_mul]

theorem partialLeft_conjugate
    (Z : Matrix (i × j) (i × j) K)
    (P P' : Matrix i i K) (Q Q' : Matrix j j K) (h : Q' * Q = 1) :
    partialTraceLeft (Matrix.kronecker P Q * Z * Matrix.kronecker P' Q') =
      P * partialTraceLeft Z * P' := by
  obtain ⟨W, rfl⟩ := (kroneckerLinearEquiv i i j j K).surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul M N =>
    simp only [kroneckerLinearEquiv_tmul]
    unfold Matrix.kronecker
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    change partialTraceLeft (Matrix.kronecker (P * M * P') (Q * N * Q')) =
      P * partialTraceLeft (Matrix.kronecker M N) * P'
    rw [partialTraceLeft_kronecker, partialTraceLeft_kronecker, trace_sim N Q Q' h]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  | add x y hx hy =>
    simpa only [map_add, Matrix.mul_add, Matrix.add_mul] using congrArg₂ (· + ·) hx hy

theorem partialRight_conjugate
    (Z : Matrix (i × j) (i × j) K)
    (P P' : Matrix i i K) (Q Q' : Matrix j j K) (h : P' * P = 1) :
    partialTraceRight (Matrix.kronecker P Q * Z * Matrix.kronecker P' Q') =
      Q * partialTraceRight Z * Q' := by
  obtain ⟨W, rfl⟩ := (kroneckerLinearEquiv i i j j K).surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul M N =>
    simp only [kroneckerLinearEquiv_tmul]
    unfold Matrix.kronecker
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    change partialTraceRight (Matrix.kronecker (P * M * P') (Q * N * Q')) =
      Q * partialTraceRight (Matrix.kronecker M N) * Q'
    rw [partialTraceRight_kronecker, partialTraceRight_kronecker, trace_sim M P P' h]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  | add x y hx hy =>
    simpa only [map_add, Matrix.mul_add, Matrix.add_mul] using congrArg₂ (· + ·) hx hy

theorem quadratic_covariant
    (Z : Matrix (i × j) (i × j) K)
    (P P' : Matrix i i K) (Q Q' : Matrix j j K)
    (hP : P' * P = 1) (hQ : Q' * Q = 1) :
    let W := Matrix.kronecker P Q * Z * Matrix.kronecker P' Q'
    partialTraceLeft (W ^ 2) = P * partialTraceLeft (Z ^ 2) * P' ∧
    partialTraceRight (W ^ 2) = Q * partialTraceRight (Z ^ 2) * Q' := by
  dsimp only
  have h : Matrix.kronecker P' Q' * Matrix.kronecker P Q = 1 := by
    unfold Matrix.kronecker
    rw [← Matrix.mul_kronecker_mul, hP, hQ, Matrix.one_kronecker_one]
  have hh : (Matrix.kronecker P Q * Z * Matrix.kronecker P' Q') ^ 2 =
      Matrix.kronecker P Q * Z ^ 2 * Matrix.kronecker P' Q' := by
    calc
      _ = Matrix.kronecker P Q * Z *
          (Matrix.kronecker P' Q' * Matrix.kronecker P Q) * Z *
          Matrix.kronecker P' Q' := by simp only [pow_two, mul_assoc]
      _ = _ := by simp only [h, pow_two, mul_one, mul_assoc]
  rw [hh]
  exact ⟨partialLeft_conjugate _ _ _ _ _ hQ, partialRight_conjugate _ _ _ _ _ hP⟩

/-- An anchor shape test depending only on the two characteristic
polynomials has the same result after the physical basis changes. -/
theorem quadratic_charpoly (Z : Matrix (i × j) (i × j) K)
    (P P' : Matrix i i K) (Q Q' : Matrix j j K)
    (hP : P' * P = 1) (hQ : Q' * Q = 1) :
    let W := Matrix.kronecker P Q * Z * Matrix.kronecker P' Q'
    (partialTraceLeft (W ^ 2)).charpoly = (partialTraceLeft (Z ^ 2)).charpoly ∧
      (partialTraceRight (W ^ 2)).charpoly = (partialTraceRight (Z ^ 2)).charpoly := by
  dsimp only
  obtain ⟨hL, hR⟩ := quadratic_covariant Z P P' Q Q' hP hQ
  constructor
  · rw [hL, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  · rw [hR, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul]

#print axioms quadratic_covariant
#print axioms quadratic_charpoly

end EvenTI.AnchorCovariance
