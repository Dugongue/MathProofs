import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! An explicit power of a primary matrix generates a field with its original
irreducible minimal polynomial. The Frobenius exponent has polynomial bit size. -/
namespace Mathproof.Problem17ComparatorPrimaryPower
open Polynomial Algebra

variable {K : Type*} [Field K] [Fintype K]

private theorem aeval_frob_pow {R : Type*} [CommRing R] [Algebra K R]
    (t : R) (f : K[X]) (n : ℕ) :
    aeval (t ^ (Fintype.card K)^n) f = (aeval t f) ^ (Fintype.card K)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    let fr := FiniteField.frobeniusAlgHom K R
    rw [pow_succ, pow_mul, pow_mul]
    change aeval (fr (t ^ (Fintype.card K)^n)) f =
      fr ((aeval t f) ^ (Fintype.card K)^n)
    rw [aeval_algHom_apply, ih]

theorem minpoly_explicit_primary_power {R : Type*} [Ring R] [Nontrivial R] [Algebra K R]
    (T : R) {f : K[X]} {m n : ℕ} (hf : f.Monic) (hi : Irreducible f)
    (hm : minpoly K T ∣ f ^ m) (hn : m ≤ n) :
    T ^ (Fintype.card K)^n ∈ adjoin K ({T} : Set R) ∧
      minpoly K (T ^ (Fintype.card K)^n) = f := by
  let A := adjoin K ({T} : Set R)
  let t : A := ⟨T, self_mem_adjoin_singleton K T⟩
  let q := Fintype.card K
  have hpow : m ≤ q^n := hn.trans
    (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance) n))
  have hkill : (aeval T f)^m = 0 := by
    rw [← map_pow]
    exact minpoly.dvd_iff.mp hm
  have hmap : aeval (T ^ q^n) f = (aeval T f)^q^n := by
    simpa [t, q, coe_aeval_mk_apply] using congrArg Subtype.val (aeval_frob_pow t f n)
  have hroot : aeval (T ^ q^n) f = 0 := by
    rw [hmap, ← Nat.add_sub_of_le hpow, pow_add, hkill, zero_mul]
  refine ⟨?_, (minpoly.eq_of_irreducible_of_monic hi hroot hf).symm⟩
  exact (adjoin K ({T} : Set R)).pow_mem (self_mem_adjoin_singleton K T) _

theorem primary_exponent_bitSize (n : ℕ) :
    Nat.size ((Fintype.card K)^n) ≤ n*Nat.size (Fintype.card K)+1 := by
  have hc := Nat.lt_size_self (Fintype.card K)
  apply Nat.size_le.mpr
  calc
    (Fintype.card K)^n ≤ (2^Nat.size (Fintype.card K))^n := Nat.pow_le_pow_left hc.le n
    _ = 2^(n*Nat.size (Fintype.card K)) := by rw [← pow_mul, Nat.mul_comm (Nat.size (Fintype.card K)) n]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

end Mathproof.Problem17ComparatorPrimaryPower

#print axioms Mathproof.Problem17ComparatorPrimaryPower.minpoly_explicit_primary_power