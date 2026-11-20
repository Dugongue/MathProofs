import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Rectangular reciprocal crossed contractions under an off-diagonal shear. -/
namespace Mathproof.EvenTI.Reciprocal
open scoped BigOperators Matrix
open Matrix

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]

abbrev UpperShear (K H L J : Type*) := Matrix (H × J) (L × J) K

def primalShear (U : (Sum H L × J) → Matrix I B K)
    (X : UpperShear K H L J) : (Sum H L × J) → Matrix I B K
  | (.inl a, j) => U (.inl a, j) + ∑ b : L × J, X (a, j) b • U (.inr b.1, b.2)
  | (.inr a, j) => U (.inr a, j)

def dualShear (V : (Sum H L × J) → Matrix B I K)
    (X : UpperShear K H L J) : (Sum H L × J) → Matrix B I K
  | (.inl a, j) => V (.inl a, j)
  | (.inr a, j) => V (.inr a, j) - ∑ b : H × J, X b (a, j) • V (.inl b.1, b.2)

def crossed (U : (Sum H L × J) → Matrix I B K)
    (V : (Sum H L × J) → Matrix B I K) : Matrix (J × I) (J × I) K :=
  fun p q => ∑ a, (U (a, p.1) * V (a, q.1)) p.2 q.2

def delta (U : (Sum H L × J) → Matrix I B K)
    (V : (Sum H L × J) → Matrix B I K) (X : UpperShear K H L J) :
    Matrix (J × I) (J × I) K :=
  fun p q =>
    (∑ a : H, ∑ b : L × J, X (a, p.1) b * (U (.inr b.1, b.2) * V (.inl a, q.1)) p.2 q.2) -
    (∑ a : L, ∑ b : H × J, X b (a, q.1) * (U (.inr a, p.1) * V (.inl b.1, b.2)) p.2 q.2)

def deltaLinear (U : (Sum H L × J) → Matrix I B K)
    (V : (Sum H L × J) → Matrix B I K) :
    UpperShear K H L J →ₗ[K] Matrix (J × I) (J × I) K where
  toFun := delta U V
  map_add' X Y := by
    ext p q
    simp [delta, add_mul, Finset.sum_add_distrib]
    abel
  map_smul' c X := by
    ext p q
    simp [delta, mul_assoc, ← Finset.mul_sum, mul_sub]

theorem crossed_shear (U : (Sum H L × J) → Matrix I B K)
    (V : (Sum H L × J) → Matrix B I K) (X : UpperShear K H L J) :
    crossed (primalShear U X) (dualShear V X) = crossed U V + deltaLinear U V X := by
  classical
  ext p q
  change crossed (primalShear U X) (dualShear V X) p q =
    crossed U V p q + delta U V X p q
  simp only [crossed, Fintype.sum_sum_type, primalShear, dualShear, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, delta]
  abel

variable [DecidableEq H] [DecidableEq L] [DecidableEq J]

def shearMatrix (X : UpperShear K H L J) : Matrix (Sum H L × J) (Sum H L × J) K
  | (.inl a,j), (.inr b,s) => X (a,j) (b,s)
  | _, _ => 0

theorem shearMatrix_sq (X : UpperShear K H L J) : shearMatrix X * shearMatrix X = 0 := by
  classical
  ext ⟨a,j⟩ ⟨b,s⟩
  cases a <;> cases b <;> simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type, shearMatrix]

theorem shearMatrix_inverse (X : UpperShear K H L J) :
    (1 + shearMatrix X) * (1 - shearMatrix X) = 1 ∧
      (1 - shearMatrix X) * (1 + shearMatrix X) = 1 := by
  constructor <;>
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, shearMatrix_sq]

variable [DecidableEq I] [DecidableEq B]

def matrixPrimal (A : Matrix (Sum H L × J) (I × B) K) :
    (Sum H L × J) → Matrix I B K := fun p i b => A p (i,b)

def matrixDual (S : Matrix (Sum H L × J) (I × B) K) :
    (Sum H L × J) → Matrix B I K := fun p b i => S p (i,b)

theorem primalShear_matrixPrimal (A : Matrix (Sum H L × J) (I × B) K)
    (X : UpperShear K H L J) :
    matrixPrimal ((1 + shearMatrix X) * A) = primalShear (matrixPrimal A) X := by
  rw [Matrix.add_mul, Matrix.one_mul]
  funext p i b
  rcases p with ⟨a,j⟩
  cases a <;> simp [matrixPrimal, primalShear, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, shearMatrix]

theorem dualShear_matrixDual (S : Matrix (Sum H L × J) (I × B) K)
    (X : UpperShear K H L J) :
    matrixDual ((1 - shearMatrix X)ᵀ * S) = dualShear (matrixDual S) X := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul]
  funext p b i
  rcases p with ⟨a,j⟩
  cases a <;> simp [matrixDual, dualShear, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type, shearMatrix]

theorem crossed_matrix_shear (A S : Matrix (Sum H L × J) (I × B) K)
    (X : UpperShear K H L J) :
    crossed (matrixPrimal ((1 + shearMatrix X) * A))
      (matrixDual ((1 - shearMatrix X)ᵀ * S)) =
      crossed (matrixPrimal A) (matrixDual S) +
        deltaLinear (matrixPrimal A) (matrixDual S) X := by
  rw [primalShear_matrixPrimal, dualShear_matrixDual, crossed_shear]

theorem shear_dual_pair (A S : Matrix (Sum H L × J) (I × B) K)
    (X : UpperShear K H L J) (hAS : A * Sᵀ = 1) (hSA : Sᵀ * A = 1) :
    let A' := (1 + shearMatrix X) * A
    let S' := (1 - shearMatrix X)ᵀ * S
    A' * S'ᵀ = (1 : Matrix (Sum H L × J) (Sum H L × J) K) ∧
      S'ᵀ * A' = (1 : Matrix (I × B) (I × B) K) := by
  dsimp only
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  constructor
  · calc
      ((1 + shearMatrix X) * A) * (Sᵀ * (1 - shearMatrix X)) =
          (1 + shearMatrix X) * (A * Sᵀ) * (1 - shearMatrix X) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAS, Matrix.mul_one, (shearMatrix_inverse X).1]
  · calc
      (Sᵀ * (1 - shearMatrix X)) * ((1 + shearMatrix X) * A) =
          Sᵀ * ((1 - shearMatrix X) * (1 + shearMatrix X)) * A := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(shearMatrix_inverse X).2, Matrix.mul_one, hSA]

end Mathproof.EvenTI.Reciprocal

#print axioms Mathproof.EvenTI.Reciprocal.crossed_shear
#print axioms Mathproof.EvenTI.Reciprocal.shearMatrix_inverse
#print axioms Mathproof.EvenTI.Reciprocal.crossed_matrix_shear
#print axioms Mathproof.EvenTI.Reciprocal.shear_dual_pair
