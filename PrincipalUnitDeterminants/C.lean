import Mathlib

namespace TruncationProbe

open scoped BigOperators

/-- Translation on a finite basis of powers. This matrix needs no quotient relation. -/
def pascal {R : Type*} [CommRing R] (n : ℕ) (a : R) : Matrix (Fin n) (Fin n) R :=
  fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : R)

theorem det_pascal {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    (pascal n a).det = 1 := by
  have upper : (pascal n a).IsUpperTriangular := by
    intro i j h
    change a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : R) = 0
    rw [Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from h), Nat.cast_zero, mul_zero]
  rw [Matrix.det_of_isUpperTriangular upper]
  simp [pascal]

/-- Apply the same set of linear coordinate probes to each successive power. -/
def powerColumns {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (probe : Fin n → A →ₗ[R] R) (g : A) : Matrix (Fin n) (Fin n) R :=
  fun i j => probe i (g ^ (j : ℕ))

theorem powerColumns_translate {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (probe : Fin n → A →ₗ[R] R) (g : A) (a : R) :
    powerColumns probe (algebraMap R A a + g) = powerColumns probe g * pascal n a := by
  ext i j
  change probe i ((algebraMap R A a + g) ^ (j : ℕ)) =
    ∑ k : Fin n, probe i (g ^ (k : ℕ)) *
      (a ^ ((j : ℕ) - k) * ((j : ℕ).choose k : R))
  rw [add_comm (algebraMap R A a) g, add_pow, map_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    probe i (g ^ k) * (a ^ ((j : ℕ) - k) * ((j : ℕ).choose k : R)))]
  calc
    _ = ∑ k ∈ Finset.range ((j : ℕ) + 1),
          probe i (g ^ k) * (a ^ ((j : ℕ) - k) * ((j : ℕ).choose k : R)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc]
      have e : algebraMap R A (a ^ ((j : ℕ) - k) * ((j : ℕ).choose k : R)) =
          (algebraMap R A a) ^ ((j : ℕ) - k) * ((j : ℕ).choose k : A) := by simp
      rw [← e, mul_comm (g ^ k), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    _ = _ := by
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (Nat.succ_le_of_lt j.isLt))
      · intro k _ hk
        have lt : (j : ℕ) < k := by simp only [Finset.mem_range, not_lt] at hk; omega
        simp [Nat.choose_eq_zero_of_lt lt]

/-- A scalar translation never changes the determinant of a power-basis substitution. -/
theorem det_powerColumns_translate {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (probe : Fin n → A →ₗ[R] R) (g : A) (a : R) :
    (powerColumns probe (algebraMap R A a + g)).det = (powerColumns probe g).det := by
  rw [powerColumns_translate, Matrix.det_mul, det_pascal, mul_one]

end TruncationProbe
