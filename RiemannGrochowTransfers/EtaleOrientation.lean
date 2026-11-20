import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace EtaleOrientation

open Matrix
open scoped BigOperators

variable (F E : Type*) [Field F] [Fintype F] [Field E] [Algebra F E]

def mooreMatrix {n : ℕ} (b : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  of fun i j => b j ^ ((Fintype.card F) ^ i.val)

noncomputable def mooreVolume {n : ℕ} (b : Fin n → E) : E :=
  (mooreMatrix F E b).det

theorem mooreVolume_change {E' : Type*} [Field E'] [Algebra F E']
    {n : ℕ} (φ : E ≃ₐ[F] E') (b : Fin n → E) (c : Fin n → E')
    (P : Matrix (Fin n) (Fin n) F)
    (hP : ∀ j, φ (b j) = ∑ k, c k * algebraMap F E' (P k j)) :
    φ (mooreVolume F E b) = mooreVolume F E' c * algebraMap F E' P.det := by
  classical
  let σ := FiniteField.frobeniusAlgHom F E'
  have hσ (i : ℕ) (x : E') : (σ ^ i) x = x ^ (Fintype.card F ^ i) := by
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
  have hmatrix : (mooreMatrix F E b).map (φ : E → E') =
      mooreMatrix F E' c * P.map (algebraMap F E') := by
    ext i j
    simp only [Matrix.map_apply, mooreMatrix, Matrix.of_apply, Matrix.mul_apply, map_pow]
    rw [← hσ, hP, map_sum]
    simp only [map_mul, AlgHom.commutes]
    simp only [hσ]
  unfold mooreVolume
  calc
    _ = ((mooreMatrix F E b).map (φ : E → E')).det :=
      φ.map_det (mooreMatrix F E b)
    _ = _ := by
      rw [hmatrix, Matrix.det_mul]
      exact congrArg ((mooreMatrix F E' c).det * ·) ((algebraMap F E').map_det P).symm

theorem mooreVolume_fixed [Finite E] {n : ℕ} (hn : Odd (n + 1))
    (hdegree : Module.finrank F E = n + 1) (b : Fin (n + 1) → E) :
    FiniteField.frobeniusAlgHom F E (mooreVolume F E b) = mooreVolume F E b := by
  classical
  let σ := FiniteField.frobeniusAlgHom F E
  let : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card F ^ (n + 1) := by
    rw [Module.card_eq_pow_finrank (K := F), hdegree]
  have hmatrix : (mooreMatrix F E b).map σ =
      (mooreMatrix F E b).submatrix (finRotate (n + 1)) id := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, mooreMatrix, Matrix.of_apply,
      id_eq, coe_finRotate]
    change (b j ^ (Fintype.card F ^ i.val)) ^ Fintype.card F = _
    rw [← pow_mul, ← pow_succ]
    split_ifs with hi
    · have hlast : i.val = n := congrArg Fin.val hi
      rw [hlast, ← hcard, FiniteField.pow_card]
      simp
    · rfl
  have hsign : Equiv.Perm.sign (finRotate (n + 1)) = 1 := by
    rw [sign_finRotate, Nat.add_sub_cancel]
    have he : Even n := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, by omega⟩
    exact he.neg_one_pow
  change σ (mooreVolume F E b) = mooreVolume F E b
  unfold mooreVolume
  calc
    _ = ((mooreMatrix F E b).map σ).det := σ.map_det (mooreMatrix F E b)
    _ = _ := by rw [hmatrix, Matrix.det_permute, hsign]; simp

end EtaleOrientation
