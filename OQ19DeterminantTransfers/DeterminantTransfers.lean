import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OQ19DeterminantTransfers

/-- Every attainable character value is a translate of a stabilizer value. -/
theorem transporter_character_coset
    {G X A : Type*} [Group G] [Group A] [MulAction G X]
    (chi : G →* A) (source target : X) (base : G) (align : base • source = target) (d : A) :
    (∃ g : G, g • source = target ∧ chi g = d) ↔
      (∃ h : G, h • source = source ∧ chi base * chi h = d) := by
  constructor
  · rintro ⟨g, hg, hd⟩
    refine ⟨base⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, hg, ← align, inv_smul_smul]
    · rw [← map_mul]
      simpa using hd
  · rintro ⟨h, hh, hd⟩
    refine ⟨base * h, ?_, ?_⟩
    · rw [mul_smul, hh, align]
    · rwa [map_mul]

/-- Two elements with the same character differ by a correction in its kernel. -/
theorem equal_character_correction
    {G A : Type*} [Group G] [Group A] (chi : G →* A)
    (source target : G) (same : chi source = chi target) :
    ∃ correction : G, chi correction = 1 ∧ source * correction = target := by
  refine ⟨source⁻¹ * target, ?_, by simp⟩
  simp [same]

/-- A power that is a multiple of the character order contributes no sign. -/
theorem neutral_character_power
    {A : Type*} [Monoid A] (x : A) {m n : ℕ} (order : x ^ m = 1)
    (divides : m ∣ n) : x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := divides
  rw [pow_mul, order, one_pow]

/-- The parity factor of exchanging two equal blocks has exponent equal
to their common dimension modulo two. -/
theorem equal_block_exchange_sign {R : Type*} [Ring R] (n : ℕ) :
    (-1 : R) ^ (n * n) = (-1 : R) ^ n := by
  have h : (n * n) % 2 = n % 2 := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  calc
    (-1 : R) ^ (n * n) = (-1) ^ ((n * n) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ (n % 2) := by rw [h]
    _ = (-1) ^ n := (neg_one_pow_eq_pow_mod_two _).symm

/-- A freely chosen off-diagonal block does not affect a mode determinant. -/
theorem support_complement_determinant
    {R U W : Type*} [CommRing R] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (support : Matrix U U R) (cross : Matrix U W R) (complement : Matrix W W R) :
    (Matrix.fromBlocks support cross 0 complement).det = support.det * complement.det :=
  Matrix.det_fromBlocks_zero₂₁ support cross complement

end OQ19DeterminantTransfers
