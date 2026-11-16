/-
Adapted from OpenAI's formalization of Problem 336, Apache-2.0.
OAI/Probability/SpanningForest/CauchyBinet.lean, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Ring

namespace Mathproof.MinimumGeneration.RankMinors

noncomputable section

open Matrix Polynomial
open scoped BigOperators

variable {R m n : Type*} [CommRing R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem coeff_det_one_add_X_smul_card (M : Matrix n n R) :
    (Matrix.det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card n) = M.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hsets : (Finset.univ : Finset n).powersetCard (Fintype.card n) =
      {Finset.univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_singleton]
    exact Finset.card_eq_iff_eq_univ s
  rw [hsets, Finset.sum_singleton]
  let e : (Finset.univ : Finset n) ≃ n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Matrix.det_submatrix_equiv_self e M

theorem det_one_add_X_mul_comm (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (1 + (X : R[X]) • (A * B).map C) =
      Matrix.det (1 + (X : R[X]) • (B * A).map C) := by
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] using
    Matrix.det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C)

theorem det_mul_eq_sum_principal_minors (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (A * B) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        Matrix.det ((B * A).submatrix (Subtype.val : s → m) (Subtype.val : s → m)) := by
  rw [← coeff_det_one_add_X_smul_card (A * B), det_one_add_X_mul_comm A B,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]

theorem det_mul_transpose_eq_sum_principal_minors (A : Matrix n m R) :
    Matrix.det (A * A.transpose) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        Matrix.det ((A.transpose * A).submatrix
          (Subtype.val : s → m) (Subtype.val : s → m)) :=
  det_mul_eq_sum_principal_minors A A.transpose

abbrev ColumnSets (n m : Type*) [Fintype n] [Fintype m] :=
  ((Finset.univ : Finset m).powersetCard (Fintype.card n))

def columnIndexEquiv (s : ColumnSets n m) : (s.val : Finset m) ≃ n :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp s.property).2)

def columnMinor (A : Matrix n m R) (s : ColumnSets n m) :
    Matrix (s.val : Finset m) (s.val : Finset m) R :=
  A.submatrix (columnIndexEquiv s) Subtype.val

omit [DecidableEq m] [DecidableEq n] in
theorem columnMinor_map {S : Type*} [CommRing S]
    (A : Matrix n m R) (f : R →+* S) (s : ColumnSets n m) :
    columnMinor (A.map f) s = (columnMinor A s).map f := rfl

omit [DecidableEq n] in
theorem columnMinor_map_det {S : Type*} [CommRing S]
    (A : Matrix n m R) (f : R →+* S) (s : ColumnSets n m) :
    (columnMinor (A.map f) s).det = f (columnMinor A s).det := by
  rw [columnMinor_map]
  exact (RingHom.map_det f (columnMinor A s)).symm

theorem det_mul_eq_sum_minors (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (A * B) =
      ∑ s : ColumnSets n m,
        (columnMinor A s).det *
          (B.submatrix Subtype.val (columnIndexEquiv s)).det := by
  rw [det_mul_eq_sum_principal_minors, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Matrix.submatrix_mul_equiv B A Subtype.val (columnIndexEquiv s) Subtype.val,
    Matrix.det_mul]
  exact mul_comm _ _

theorem det_mul_transpose_eq_sum_sq_minors (A : Matrix n m R) :
    Matrix.det (A * A.transpose) =
      ∑ s : ColumnSets n m, (columnMinor A s).det ^ 2 := by
  rw [det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro s _
  have ht : A.transpose.submatrix Subtype.val (columnIndexEquiv s) =
      (columnMinor A s).transpose := rfl
  rw [ht, Matrix.det_transpose, pow_two]

omit [DecidableEq n] in
theorem columnMinor_mul_diagonal (A : Matrix n m R) (w : m → R)
    (s : ColumnSets n m) :
    columnMinor (A * Matrix.diagonal w) s =
      columnMinor A s * Matrix.diagonal (fun j : (s.val : Finset m) => w j.val) := by
  ext i j
  simp [columnMinor, Matrix.mul_diagonal]

theorem det_weighted_gram_eq_sum_sq_minors (A : Matrix n m R) (w : m → R) :
    Matrix.det (A * Matrix.diagonal w * A.transpose) =
      ∑ s : ColumnSets n m,
        (∏ j : (s.val : Finset m), w j.val) * (columnMinor A s).det ^ 2 := by
  rw [det_mul_eq_sum_minors]
  apply Finset.sum_congr rfl
  intro s _
  have ht : A.transpose.submatrix Subtype.val (columnIndexEquiv s) =
      (columnMinor A s).transpose := rfl
  rw [columnMinor_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal,
    ht, Matrix.det_transpose]
  ring


end

end Mathproof.MinimumGeneration.RankMinors
