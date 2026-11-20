import EvenNextQuadraticCovariance
import Mathlib.Algebra.CharP.Frobenius

/-! The polar identity and trace support from Problem 1.7, using the
narrow partial trace definitions from the even-order covariance module. -/
namespace Mathproof.EvenOrdinaryTISingular.PolarQuadratic

open scoped BigOperators Matrix
open EvenTI.AnchorCovariance

variable {K i j : Type*} [Field K] [Fintype i] [Fintype j]
variable [DecidableEq i] [DecidableEq j]

omit [DecidableEq i] [DecidableEq j] in
theorem polar_pure
    (X X' : Matrix i i K) (Y Y' : Matrix j j K) :
    let Z := Matrix.kronecker X Y
    let W := Matrix.kronecker X' Y'
    partialTraceLeft (Z * W + W * Z) =
      Matrix.trace (Y * Y') • (X * X' + X' * X) ∧
    partialTraceRight (Z * W + W * Z) =
      Matrix.trace (X * X') • (Y * Y' + Y' * Y) := by
  dsimp only
  have hm (A B : Matrix i i K) (C D : Matrix j j K) :
      Matrix.kronecker A C * Matrix.kronecker B D =
        Matrix.kronecker (A * B) (C * D) := by
    unfold Matrix.kronecker
    rw [Matrix.mul_kronecker_mul]
  rw [hm, hm]
  constructor
  · rw [map_add, partialTraceLeft_kronecker, partialTraceLeft_kronecker,
      Matrix.trace_mul_comm Y' Y, smul_add]
  · rw [map_add, partialTraceRight_kronecker, partialTraceRight_kronecker,
      Matrix.trace_mul_comm X' X, smul_add]

omit [DecidableEq i] [DecidableEq j] in
theorem partial_traces_same_trace (Z : Matrix (i × j) (i × j) K) :
    Matrix.trace (partialTraceLeft Z) = Matrix.trace (partialTraceRight Z) := by
  change (∑ a, ∑ b, Z (a,b) (a,b)) = ∑ b, ∑ a, Z (a,b) (a,b)
  exact Finset.sum_comm

omit [Fintype j] [DecidableEq j] in
theorem trace_square_charTwo [CharP K 2] (Z : Matrix i i K) :
    Matrix.trace (Z ^ 2) = (Matrix.trace Z) ^ 2 := by
  classical
  let f : i × i → K := fun p => if p.1 = p.2 then 0 else Z p.1 p.2 * Z p.2 p.1
  have htwo : (2 : K) = 0 := by exact CharP.cast_eq_zero K 2
  have hoff : ∑ p, f p = 0 := by
    apply Finset.sum_involution (fun p _ => p.swap)
    · rintro ⟨a,b⟩ _
      by_cases hab : a = b
      · simp [f, hab]
      · simp only [f, Prod.swap_prod_mk, if_neg hab, if_neg (Ne.symm hab), mul_comm (Z b a)]
        rw [← two_mul, htwo, zero_mul]
    · rintro ⟨a,b⟩ _ hf hs
      have hba : b = a := congrArg Prod.fst hs
      subst b
      exact hf (by simp [f])
    · intro p hp
      simp
    · intro p hp
      simp
  have hsplit (p : i × i) :
      Z p.1 p.2 * Z p.2 p.1 = f p + if p.1 = p.2 then Z p.1 p.1 ^ 2 else 0 := by
    rcases p with ⟨a,b⟩
    by_cases hab : a = b <;> simp [f, hab, pow_two]
  calc
    Matrix.trace (Z ^ 2) = ∑ p : i × i, Z p.1 p.2 * Z p.2 p.1 := by
      simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    _ = ∑ a, Z a a ^ 2 := by
      simp only [hsplit, Finset.sum_add_distrib, hoff, zero_add]
      simp [Fintype.sum_prod_type]
    _ = (Matrix.trace Z) ^ 2 := by
      change (∑ a, frobenius K 2 (Z a a)) = frobenius K 2 (∑ a, Z a a)
      exact (map_sum _ _ _).symm

theorem quadratic_partial_traces_zero_charTwo [CharP K 2]
    (Z : Matrix (i × j) (i × j) K) (h : Matrix.trace Z = 0) :
    Matrix.trace (partialTraceLeft (Z ^ 2)) = 0 ∧
      Matrix.trace (partialTraceRight (Z ^ 2)) = 0 := by
  have hleft (X : Matrix (i × j) (i × j) K) :
      Matrix.trace (partialTraceLeft X) = Matrix.trace X := by
    change (∑ a, ∑ b, X (a,b) (a,b)) = ∑ p : i × j, X p p
    rw [Fintype.sum_prod_type]
  rw [← partial_traces_same_trace, hleft, trace_square_charTwo, h, zero_pow (by decide)]
  simp

private theorem htrace {a : Type*} [Fintype a] [DecidableEq a] (T U V : Matrix a a K) :
    Matrix.trace (T * (U * V + V * U)) = Matrix.trace ((T * U + U * T) * V) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle T V U]

theorem polar_trace_tensor_sum
    (P X X' : Matrix i i K) (Q Y Y' : Matrix j j K) :
    let Z := Matrix.kronecker X Y
    let W := Matrix.kronecker X' Y'
    let H := Z * W + W * Z
    Matrix.trace (P * partialTraceLeft H) + Matrix.trace (Q * partialTraceRight H) =
      Matrix.trace ((P * X + X * P) * X') * Matrix.trace (Y * Y') +
        Matrix.trace (X * X') * Matrix.trace ((Q * Y + Y * Q) * Y') := by
  dsimp only
  obtain ⟨hL, hR⟩ := polar_pure X X' Y Y'
  rw [hL, hR, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [htrace, htrace]
  simp only [smul_eq_mul]
  ring


end Mathproof.EvenOrdinaryTISingular.PolarQuadratic

#print axioms Mathproof.EvenOrdinaryTISingular.PolarQuadratic.polar_trace_tensor_sum
#print axioms Mathproof.EvenOrdinaryTISingular.PolarQuadratic.quadratic_partial_traces_zero_charTwo
