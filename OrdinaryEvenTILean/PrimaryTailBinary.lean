import PrimaryTailCount
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace Mathproof.Problem17PrimaryTail
open Module Matrix LinearMap Polynomial
noncomputable section

private theorem binary_matrix_sqzero_count :
    (Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) (ZMod 2) => A ^ 2 = 0)).card = 4 := by
  decide

theorem binary_sqzero_count {K : Type*} [Field K] [Fintype K] (hq : Nat.card K = 2) :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // A ^ 2 = 0} = 4 := by
  classical
  have hF : Fintype.card K = 2 := by simpa [Nat.card_eq_fintype_card] using hq
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
  let E := e.mapMatrix (m := Fin 2)
  let E' : {A : Matrix (Fin 2) (Fin 2) (ZMod 2) // A^2=0} ≃
      {A : Matrix (Fin 2) (Fin 2) K // A^2=0} :=
    E.toEquiv.subtypeEquiv fun A => by
      change A^2=0 ↔ (E A)^2=0
      rw [← map_pow, ← map_zero E]
      exact E.injective.eq_iff.symm
  rw [← Nat.card_congr E']
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using binary_matrix_sqzero_count

/-- For every binary scalar, size-two blocks with that double eigenvalue
have weight at most two thirds against the basis multiplicity. -/
theorem binary_double_block_weight {K : Type*} [Field K] [Fintype K]
    (hq : Nat.card K = 2) (lam : K) :
    3 * Nat.card (PolyEvent (· = (X - C lam)^2) (Coord K 2)) ≤
      2 * Nat.card (GL (Fin 2) K) := by
  classical
  let b := Pi.basisFun K (Fin 2)
  let e := LinearMap.toMatrix b b
  let φ : PolyEvent (· = (X - C lam)^2) (Coord K 2) →
      {A : Matrix (Fin 2) (Fin 2) K // A^2=0} := fun T =>
    ⟨e T.val - lam • 1, by
      have he : (e T.val).charpoly = (X - C lam)^2 :=
        (LinearMap.charpoly_toMatrix T.val b).trans T.property
      have hh := Matrix.aeval_self_charpoly (e T.val)
      rw [he, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hh
      simpa [Algebra.algebraMap_eq_smul_one] using hh⟩
  have hφ : Function.Injective φ := by
    intro T U h
    apply Subtype.ext
    apply e.injective
    have hh := congrArg (fun z : {A : Matrix (Fin 2) (Fin 2) K // A^2=0} => z.val) h
    change e T.val - lam • 1 = e U.val - lam • 1 at hh
    exact sub_left_injective hh
  have h := Nat.card_le_card_of_injective φ hφ
  rw [binary_sqzero_count hq] at h
  have hG : Nat.card (GL (Fin 2) K) = 6 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two]
    have hF : Fintype.card K = 2 := by simpa [Nat.card_eq_fintype_card] using hq
    rw [hF]
    decide
  omega

end
end Mathproof.Problem17PrimaryTail

#print axioms Mathproof.Problem17PrimaryTail.binary_double_block_weight
