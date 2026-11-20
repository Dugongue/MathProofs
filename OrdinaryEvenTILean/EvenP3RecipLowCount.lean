import EvenP3RecipLowQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open Matrix Module LinearMap

variable {K V : Type*} [Field K] [Fintype K]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

set_option backward.isDefEq.respectTransparency false in
private theorem factor_lowRank (f : Module.End K V) (t : ℕ)
    (hf : finrank K f.range ≤ t) :
    ∃ (x : V →ₗ[K] (Fin t → K)) (y : (Fin t → K) →ₗ[K] V), y.comp x = f := by
  classical
  let b := Basis.ofVectorSpace K (↥f.range)
  let C := Basis.ofVectorSpaceIndex K (↥f.range)
  letI : Fintype C := inferInstanceAs (Fintype (Basis.ofVectorSpaceIndex K (↥f.range)))
  have hc : Fintype.card C ≤ t := by
    rwa [Module.finrank_eq_card_basis b] at hf
  let i : C ↪ Fin t := (Fintype.equivFin C).toEmbedding.trans (Fin.castLEEmb hc)
  let pr : (Fin t → K) →ₗ[K] (C → K) := LinearMap.funLeft K K i
  have hpr : Function.Surjective pr := by
    intro u
    exact ⟨Function.extend i u 0, funext (i.injective.extend_apply _ _)⟩
  let : Module.Free K (C → K) := Module.Free.of_divisionRing K (C → K)
  obtain ⟨s,hs⟩ := pr.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hpr)
  refine ⟨s.comp (b.equivFun.toLinearMap.comp f.rangeRestrict),
    f.range.subtype.comp (b.equivFun.symm.toLinearMap.comp pr), ?_⟩
  ext v
  change (b.equivFun.symm (pr (s (b.equivFun (f.rangeRestrict v))))).val = f v
  have hps : pr (s (b.equivFun (f.rangeRestrict v))) = b.equivFun (f.rangeRestrict v) :=
    LinearMap.congr_fun hs _
  rw [hps, b.equivFun.symm_apply_apply] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Rank factorization bounds the cumulative number of labels lying within
rank t of a scalar by q^(2 dim(V) t + 1). -/
theorem card_near_scalar_le [Finite V] (t : ℕ) :
    Nat.card {f : Module.End K V // ∃ a : K, finrank K (f - a • LinearMap.id).range ≤ t} ≤
      Nat.card K ^ (2 * finrank K V * t + 1) := by
  classical
  let A := V →ₗ[K] (Fin t → K)
  let B := (Fin t → K) →ₗ[K] V
  let : Finite A := Finite.of_injective (fun f : A => (f : V → (Fin t → K))) DFunLike.coe_injective
  let : Finite B := Finite.of_injective (fun f : B => (f : (Fin t → K) → V)) DFunLike.coe_injective
  let Code := K × A × B
  let f : Code → Module.End K V := fun p => p.1 • LinearMap.id + p.2.2.comp p.2.1
  let S := {g : Module.End K V // ∃ a : K, finrank K (g - a • LinearMap.id).range ≤ t}
  have hS (x : S) : ∃ p : Code, f p = x.val := by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨X,Y,hXY⟩ := factor_lowRank _ t ha
    refine ⟨⟨a,X,Y⟩, ?_⟩
    change a • LinearMap.id + Y.comp X = x.val
    rw [hXY]
    abel
  let enc : S → Code := fun x => (hS x).choose
  have hi : Function.Injective enc := by
    intro x y hxy
    apply Subtype.ext
    exact ((hS x).choose_spec).symm.trans ((congrArg f hxy).trans (hS y).choose_spec)
  apply (Nat.card_le_card_of_injective enc hi).trans_eq
  change Nat.card (K × A × B) = _
  rw [Nat.card_prod, Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := K) (V := A),
    Module.natCard_eq_pow_finrank (K := K) (V := B)]
  have hA : finrank K A = finrank K V * t := by
    change finrank K (V →ₗ[K] (Fin t → K)) = _
    rw [Module.finrank_linearMap, Module.finrank_pi, Fintype.card_fin]
  have hB : finrank K B = t * finrank K V := by
    change finrank K ((Fin t → K) →ₗ[K] V) = _
    rw [Module.finrank_linearMap, Module.finrank_pi, Fintype.card_fin]
  rw [hA, hB, ← pow_add, ← pow_succ']
  congr 1
  ring

#print axioms card_near_scalar_le

end Mathproof.EvenTI.Reciprocal.SquareLow
