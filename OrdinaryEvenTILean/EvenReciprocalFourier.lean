import EvenReciprocalShear
import FourierTransfer
import TraceCharacters

/-! Fourier variation of a squared linear shear. The target can be an affine
trace space, identified with its parallel linear subspace by translation. -/
namespace Mathproof.EvenTI.Reciprocal
open scoped BigOperators Matrix
open Mathproof.Problem18FourierCore20260930
open Mathproof.Problem17FourierTransfer Mathproof.Problem17TraceCharacters

section Square
variable {K V R G : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Ring R] [Algebra K R] [AddCommGroup G] [Module K G]

def squarePolar (D : V →ₗ[K] R) (l : R →ₗ[K] K) : V →ₗ[K] Module.Dual K V where
  toFun x :=
    { toFun := fun y => l (D x * D y + D y * D x)
      map_add' y z := by simp only [map_add, mul_add, add_mul]; abel
      map_smul' a y := by simp only [map_smul, smul_eq_mul, mul_smul_comm, smul_mul_assoc,
        ← smul_add, RingHom.id_apply] }
  map_add' x y := by
    ext z
    change l (D (x + y) * D z + D z * D (x + y)) =
      l (D x * D z + D z * D x) + l (D y * D z + D z * D y)
    simp only [map_add, mul_add, add_mul]
    abel
  map_smul' a x := by
    ext y
    change l (D (a • x) * D y + D y * D (a • x)) = a • l (D x * D y + D y * D x)
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add]

def centeredSquare (C : R) (D : V →ₗ[K] R) (l : R →ₗ[K] G) (x : V) : G :=
  l ((C + D x)^2 - C^2)

theorem centeredSquare_polar (C : R) (D : V →ₗ[K] R) (l : R →ₗ[K] K) (x y : V) :
    centeredSquare C D l (x + y) =
      centeredSquare C D l x + centeredSquare C D l y + squarePolar D l y x := by
  change l ((C + D (x + y))^2 - C^2) =
    l ((C + D x)^2 - C^2) + l ((C + D y)^2 - C^2) +
      l (D y * D x + D x * D y)
  simp only [map_add, map_sub, pow_two, add_mul, mul_add]
  abel

variable [Fintype K] [Fintype V] (S : Submodule K G) [Fintype S]

def centeredSquareIn (C : R) (D : V →ₗ[K] R) (l : R →ₗ[K] G)
    (hS : ∀ x, centeredSquare C D l x ∈ S) (x : V) : S :=
  ⟨centeredSquare C D l x, hS x⟩

theorem centeredSquare_variation_sq (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (r : ℕ)
    (C : R) (D : V →ₗ[K] R) (l : R →ₗ[K] G)
    (hS : ∀ x, centeredSquare C D l x ∈ S)
    (hr : ∀ c : Module.Dual K G, c.comp S.subtype ≠ 0 →
      r ≤ Module.finrank K (squarePolar D (c.comp l)).range) :
    ((∑ y, ‖uniformImageWeight (centeredSquareIn S C D l hS) y -
      (Fintype.card S : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card S : ℝ) * ((Fintype.card K : ℝ)^r)⁻¹ / 4 := by
  refine image_variation_of_polar_rank (centeredSquareIn S C D l hS) r ?_
  intro χ hχ
  obtain ⟨m, hm⟩ := every_character_is_linear ψ hψ χ
  obtain ⟨c, hc⟩ := LinearMap.exists_extend m
  have hc0 : c.comp S.subtype ≠ 0 := by
    rw [hc]
    intro hm0
    apply hχ
    ext y
    rw [hm, hm0]
    simp
  refine ⟨ψ, centeredSquare C D (c.comp l), squarePolar D (c.comp l), hψ, ?_,
    centeredSquare_polar C D (c.comp l), hr c hc0⟩
  intro x
  rw [hm, ← hc] <;> rfl

end Square
end Mathproof.EvenTI.Reciprocal

#print axioms Mathproof.EvenTI.Reciprocal.centeredSquare_polar
#print axioms Mathproof.EvenTI.Reciprocal.centeredSquare_variation_sq
