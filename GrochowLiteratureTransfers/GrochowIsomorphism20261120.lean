import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace GrochowIsomorphism20261120

/-- Fixing one ordinary transporter reduces a prescribed character to the stabilizer. -/
theorem character_transporter_iff {G D X : Type*} [Group G] [Group D] [MulAction G X]
    (χ : G →* D) (a b : X) (t : G) (ht : t • a = b) (d : D) :
    (∃ g : G, g • a = b ∧ χ g = d) ↔
      ∃ s : G, s • a = a ∧ χ s = (χ t)⁻¹ * d := by
  constructor
  · rintro ⟨g, hg, hc⟩
    refine ⟨t⁻¹ * g, ?_, by simp [hc]⟩
    rw [mul_smul, hg, ← ht, inv_smul_smul]
  · rintro ⟨s, hs, hc⟩
    refine ⟨t * s, by rw [mul_smul, hs, ht], ?_⟩
    rw [map_mul, hc, ← mul_assoc, mul_inv_cancel, one_mul]

/-- An adjoint identity converts the normalized anchor congruence into a norm equation. -/
theorem congruence_iff_adjoint_norm {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (D E U Uadj C : Matrix ι ι R) (hInv : E * D = 1)
    (hAdj : U.transpose * D = D * Uadj) :
    U.transpose * D * U = D * C ↔ Uadj * U = C := by
  rw [hAdj, mul_assoc]
  constructor
  · intro h
    simpa only [← mul_assoc, hInv, one_mul] using congrArg (fun T => E * T) h
  · intro h
    rw [h]

open scoped InnerProductSpace in
/-- Equality of Gram matrices preserves all linear relations in the two families. -/
theorem gram_preserves_linear_relations {K ι E F : Type*} [RCLike K] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F]
    (u : ι → E) (v : ι → F) (h : Matrix.gram K u = Matrix.gram K v)
    (a : ι → K) :
    (∑ i, a i • u i) = 0 ↔ (∑ i, a i • v i) = 0 := by
  have hi := congrArg (fun M : Matrix ι ι K => dotProduct (star a) (Matrix.mulVec M a)) h
  rw [Matrix.star_dotProduct_gram_mulVec, Matrix.star_dotProduct_gram_mulVec] at hi
  rw [← inner_self_eq_zero (𝕜 := K), hi, inner_self_eq_zero]

/-- For a perfect quotient, an abelian central cocycle has at most one correction. -/
theorem unique_cocycle_correction {Q A : Type*} [Group Q] [CommGroup A]
    (hQ : commutator Q = ⊤) (c : Q → Q → A) (f g : Q → A)
    (hf : ∀ x y, f (x * y) = f x * f y * c x y)
    (hg : ∀ x y, g (x * y) = g x * g y * c x y) : f = g := by
  let d : Q →* A :=
    { toFun := fun x => f x / g x
      map_one' := by
        have h : f 1 / g 1 = (f 1 / g 1) * (f 1 / g 1) := by
          calc
            f 1 / g 1 = f (1 * 1) / g (1 * 1) := by simp
            _ = _ := by rw [hf, hg, mul_div_mul_right_eq_div, mul_div_mul_comm]
        exact (mul_left_cancel (show (f 1 / g 1) * 1 =
          (f 1 / g 1) * (f 1 / g 1) by simpa only [mul_one] using h)).symm
      map_mul' := by
        intro x y
        rw [hf, hg, mul_div_mul_right_eq_div, mul_div_mul_comm] }
  have hker : commutator Q ≤ d.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    simp [MonoidHom.mem_ker, commutatorElement_def]
  rw [hQ] at hker
  funext x
  have hx : x ∈ d.ker := hker (Subgroup.mem_top x)
  exact div_eq_one.mp (MonoidHom.mem_ker.mp hx)

end GrochowIsomorphism20261120
